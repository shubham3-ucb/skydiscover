"""Evaluator for Coq co-synthesis: implementation + proof together.

Generic for any .v file. Not problem-specific.

Scoring (always in [0, 1]):
  - Compiles, done (no Admitted, no todo, no axioms, qed > 0) → 1.0
  - Compiles, work remaining → qed / (qed + admitted + todo + axioms), always < 1
  - Doesn't compile, has real Qed work → 0.5 * qed / (qed + admitted + todo + axioms)
  - Doesn't compile, no Qed → 0.0

The 0.5 penalty ensures compiling programs always outscore non-compiling ones
with the same obligation ratio, while still giving partial credit so the search
retains near-compiling programs instead of discarding them.

Open obligations = Admitted proofs + todo expressions + non-todo Axiom declarations.
"""

import re
import subprocess
import os
import tempfile

from skydiscover.evaluation.evaluation_result import EvaluationResult

_COQ_COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
_AXIOM_TODO_LINE = re.compile(r"^\s*Axiom\s+todo\b.*$", re.MULTILINE)


def _strip_comments(text):
    return _COQ_COMMENT.sub("", text)


def _count_proof_terms(content):
    """Count Qed./Defined. and Admitted. outside comments."""
    stripped = _strip_comments(content)
    qed = len(re.findall(r"\bQed\s*\.", stripped))
    admitted = len(re.findall(r"\bAdmitted\s*\.", stripped))
    defined = len(re.findall(r"\bDefined\s*\.", stripped))
    return qed + defined, admitted


def _count_todos(content):
    """Count `todo` usage outside comments, excluding the Axiom declaration."""
    stripped = _strip_comments(content)
    without_axiom = _AXIOM_TODO_LINE.sub("", stripped)
    return len(re.findall(r"\btodo\b", without_axiom))


def _count_axiom_obligations(content):
    """Count Axiom declarations that are real obligations (not `Axiom todo`)."""
    stripped = _strip_comments(content)
    all_axioms = re.findall(r"^\s*Axiom\b", stripped, re.MULTILINE)
    todo_axioms = re.findall(r"^\s*Axiom\s+todo\b", stripped, re.MULTILINE)
    return len(all_axioms) - len(todo_axioms)


def _strip_markdown_fences(content):
    """Strip markdown code fences if the LLM wrapped the file in them."""
    lines = content.strip().splitlines()
    if not lines:
        return content
    # If first line is a fence opener (```coq, ```Coq, ```v, ```, etc.)
    if re.match(r'^```\s*[a-zA-Z]*\s*$', lines[0]):
        lines = lines[1:]
    # If last line is a fence closer
    if lines and re.match(r'^```\s*$', lines[-1]):
        lines = lines[:-1]
    # If first line is just a bare language tag left by bad fence stripping (e.g. "Coq", "coq")
    if lines and re.match(r'^[Cc]oq\s*$', lines[0]):
        lines = lines[1:]
    return '\n'.join(lines)


_TIMEOUT_GUIDANCE = (
    "Timeout: coqc exceeded the time limit. "
    "The proof likely contains tactics that diverge (cause infinite "
    "unification or rewriting loops). Common causes in Coq:\n"
    "  - `repeat rewrite ...` or `repeat (simpl; ...)` — unbounded rewriting\n"
    "  - `eauto` / `auto` in large contexts — exponential search\n"
    "  - `repeat split` with existential variables — unbounded goal generation\n"
    "  - `do N eexists` with large N — creates many unification variables\n"
    "  - `omega` / `lia` on goals with many hypotheses — expensive decision procedures\n"
    "Rewrite the proof using explicit, targeted tactics instead of open-ended automation."
)

def _postprocess_error(stderr):
    """Trim verbose coqc proof-context dumps to surface the actual error.

    coqc errors for proof failures include an "In environment" block listing
    every hypothesis in scope — often 15-30 lines. This overwhelms the LLM
    and buries the actual error message. We strip the environment block and
    keep only: (1) the File/line locator, (2) the core error message.
    """
    if not stderr:
        return stderr

    lines = stderr.strip().splitlines()

    # Find the first "Error:" line
    error_idx = None
    for i, line in enumerate(lines):
        if "Error:" in line or "Error :" in line:
            error_idx = i
            break

    if error_idx is None:
        return "\n".join(lines[-12:]).strip()[-2000:]

    # Find the "File ..." locator line before "Error:".  The environment
    # block can be arbitrarily long between the locator and the Error line,
    # so we scan backward, skipping environment content, to find the locator.
    header = []
    for i in range(error_idx - 1, max(-1, error_idx - 50), -1):
        stripped = lines[i].strip()
        if stripped.startswith("File "):
            header = [lines[i]]
            break

    # From "Error:" onward, skip "In environment" blocks entirely.
    # Environment lines are hypothesis bindings (name : type) or
    # continuation lines indented further. We detect the end of the
    # environment block by looking for a line that is NOT a binding
    # (i.e. doesn't match "identifier : ..." or isn't a continuation).
    _ENV_BINDING = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*\s*[:,]")
    body = []
    in_env = False
    for line in lines[error_idx:]:
        stripped = line.strip()
        if stripped == "In environment":
            in_env = True
            continue
        if in_env:
            if not stripped:
                in_env = False
                continue
            # Continuation lines of a multi-line type are indented
            if line.startswith("  ") and not _ENV_BINDING.match(stripped):
                continue
            if _ENV_BINDING.match(stripped):
                continue
            # Not a binding or continuation — we've exited the env block
            in_env = False
            body.append(line)
            continue
        body.append(line)
        if len(body) >= 10:
            break

    return "\n".join(header + body).strip()[-2000:]


def _run_coqc(filepath):
    filepath = os.path.abspath(filepath)
    try:
        r = subprocess.run(
            ["coqc", os.path.basename(filepath)],
            capture_output=True, text=True, timeout=300,
            cwd=os.path.dirname(filepath),
        )
        return r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired:
        return 1, "", _TIMEOUT_GUIDANCE


_ADMITTED_PAT = re.compile(r"Admitted\s*\.")
_THEOREM_HEADING = re.compile(
    r"^\s*(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark)\s+(\w+)",
    re.MULTILINE,
)


def _find_admitted_outside_comments(content):
    """Return match positions of Admitted. that are NOT inside Coq comments."""
    # Build a set of character positions that are inside comments
    comment_chars = set()
    for m in _COQ_COMMENT.finditer(content):
        comment_chars.update(range(m.start(), m.end()))
    results = []
    for m in _ADMITTED_PAT.finditer(content):
        if m.start() not in comment_chars:
            results.append(m)
    return results


def _extract_goal_states(filepath, content):
    """Run a second coqc pass with Show. before each Admitted. to capture goals.

    Returns a list of (theorem_name, goal_text) pairs.  Completely general —
    works for any .v file.  Only called when the file already compiles
    (so the Show. pass is guaranteed to succeed).
    """
    admitted_matches = _find_admitted_outside_comments(content)
    if not admitted_matches:
        return []

    # Inject "Show." before every real Admitted. (in reverse to preserve offsets)
    injected = content
    for m in reversed(admitted_matches):
        injected = injected[:m.start()] + "Show. " + injected[m.start():]

    d = os.path.dirname(os.path.abspath(filepath))
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".v", dir=d, delete=False
    ) as tmp:
        tmp.write(injected)
        tmp_path = tmp.name

    try:
        r = subprocess.run(
            ["coqc", os.path.basename(tmp_path)],
            capture_output=True, text=True, timeout=300,
            cwd=d,
        )
        stdout = r.stdout or ""
    except (subprocess.TimeoutExpired, OSError):
        stdout = ""
    finally:
        _cleanup_coq_artifacts(tmp_path)
        try:
            os.remove(tmp_path)
        except OSError:
            pass

    if not stdout.strip():
        return []

    # Find theorem names (order matches admitted_matches order)
    headings = list(_THEOREM_HEADING.finditer(content))
    theorem_names = []
    for m in admitted_matches:
        name = "?"
        for h in reversed(headings):
            if h.start() < m.start():
                name = h.group(1)
                break
        theorem_names.append(name)

    # Parse goal blocks from stdout — each Show. produces "N goal(s)\n..."
    # "No more goals." lines are from already-solved-but-Admitted proofs; skip.
    # Split on goal headers; everything before the first is non-goal output.
    raw_blocks = re.split(r"(?=^\d+ goals?\s*$)", stdout.strip(),
                          flags=re.MULTILINE)
    goal_blocks = [b.strip() for b in raw_blocks
                   if re.match(r"^\d+ goals?", b.strip())]

    # Map goal blocks back to theorem names.  If a proof was already complete
    # (Show. prints "No more goals."), it produces no goal block, so we
    # skip those names.  Count "No more goals." occurrences before each block
    # to align correctly.
    no_more = stdout.count("No more goals.")
    # Simple path: if no "No more goals." lines, 1:1 mapping
    if no_more == 0:
        name_iter = iter(theorem_names)
    else:
        # Rebuild alignment: walk stdout lines and pair with theorem names
        name_iter = iter(theorem_names)
        aligned_names = []
        for line in stdout.strip().splitlines():
            if "No more goals" in line:
                try:
                    next(name_iter)  # skip this theorem
                except StopIteration:
                    break
            elif re.match(r"^\d+ goals?\s*$", line.strip()):
                try:
                    aligned_names.append(next(name_iter))
                except StopIteration:
                    aligned_names.append("?")
        name_iter = iter(aligned_names)

    results = []
    for i, block in enumerate(goal_blocks):
        name = next(name_iter, "?")
        # Trim: stop at Check output or other non-goal lines after the separator
        lines = block.splitlines()
        trimmed = []
        past_separator = False
        for line in lines:
            if "======" in line:
                past_separator = True
                trimmed.append(line)
                continue
            if past_separator and line and not line[0].isspace() and ":" in line:
                break
            trimmed.append(line)
        results.append((name, "\n".join(trimmed[:15]).strip()))

    return results


def _cleanup_coq_artifacts(filepath):
    base = filepath.rsplit(".v", 1)[0]
    for ext in [".vo", ".vos", ".vok", ".glob", ".aux"]:
        try:
            os.remove(base + ext)
        except FileNotFoundError:
            pass
    d, f = os.path.split(filepath)
    aux = os.path.join(d, "." + f.rsplit(".v", 1)[0] + ".aux")
    try:
        os.remove(aux)
    except FileNotFoundError:
        pass


_FEEDBACK_BUDGET = 1850  # must fit within format_artifacts 2000-char cap (with margin)


def _build_feedback(compiles, done, qed, admitted, todo, axioms=0,
                    goal_states=None):
    """Build natural-language feedback for the LLM."""
    if done:
        return "All obligations discharged. The file is complete."
    parts = []
    if not compiles:
        parts.append("File does NOT compile (see error above). Fix the error first.")
    remaining = admitted + todo + axioms
    detail = []
    if admitted > 0:
        detail.append(f"{admitted} Admitted proof(s)")
    if todo > 0:
        detail.append(f"{todo} todo expression(s)")
    if axioms > 0:
        detail.append(f"{axioms} Axiom placeholder(s) to define")
    parts.append(f"{remaining} obligation(s) remain: {', '.join(detail)}.")
    if axioms > 0:
        parts.append("Replace one Axiom placeholder with a proper definition.")
    elif todo > 0:
        parts.append("Pick one todo expression and replace it with a concrete Coq term.")
    elif admitted > 0:
        parts.append("Prove one Admitted lemma with Qed.")

    if goal_states:
        header_text = " ".join(parts)
        goal_parts = [header_text, "\nRemaining proof goals:"]
        used = len(header_text) + 1 + len("\nRemaining proof goals:")  # +1 for join \n
        added = 0
        for name, goals in goal_states:
            entry = f"\n[{name}]\n{goals}"
            if used + 1 + len(entry) > _FEEDBACK_BUDGET:
                omitted = len(goal_states) - added
                goal_parts.append(f"\n(... {omitted} more goal(s) omitted)")
                break
            goal_parts.append(entry)
            used += 1 + len(entry)
            added += 1
        return "\n".join(goal_parts)

    return " ".join(parts)


def evaluate(program_path):
    content = open(program_path).read()
    cleaned = _strip_markdown_fences(content)
    if cleaned != content:
        with open(program_path, 'w') as f:
            f.write(cleaned)
        content = cleaned

    qed_count, admitted_count = _count_proof_terms(content)
    todo_count = _count_todos(content)
    axiom_count = _count_axiom_obligations(content)
    code_length = len(content.splitlines())

    rc, stdout, stderr = _run_coqc(program_path)
    _cleanup_coq_artifacts(program_path)

    compiles = rc == 0
    open_obligations = admitted_count + todo_count + axiom_count
    done = compiles and open_obligations == 0 and qed_count > 0

    total = qed_count + open_obligations
    if done:
        score = 1.0
    elif total > 0:
        ratio = qed_count / total
        score = ratio if compiles else 0.5 * ratio
    else:
        score = 0.0

    # Extract goal states for Admitted proofs (only when file compiles)
    goal_states = []
    if compiles and admitted_count > 0:
        goal_states = _extract_goal_states(program_path, content)

    metrics = {
        "combined_score": score,
        "compiles": 1.0 if compiles else 0.0,
        "qed_count": float(qed_count),
        "admitted_count": float(admitted_count),
        "todo_count": float(todo_count),
        "axiom_count": float(axiom_count),
        "code_length": float(code_length),
        "done": 1.0 if done else 0.0,
    }

    if not compiles:
        processed = _postprocess_error(stderr) if stderr else ""
        metrics["error"] = processed or "Compilation failed (no details from coqc)."

    artifacts = {}
    feedback = _build_feedback(compiles, done, qed_count, admitted_count,
                               todo_count, axiom_count,
                               goal_states=goal_states)
    if feedback:
        artifacts["feedback"] = feedback

    return EvaluationResult(metrics=metrics, artifacts=artifacts)
