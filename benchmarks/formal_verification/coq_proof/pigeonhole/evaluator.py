"""Evaluator for Coq co-synthesis: implementation + proof together.

Generic for any .v file. Not problem-specific.

Scoring (always in [0, 1]):
  - Compiles, done (no Admitted, no todo, no axioms, qed > 0) → 1.0
  - Compiles, work remaining → qed / (qed + admitted_weight + todo + axioms), < 1
  - Doesn't compile, has real Qed work → 0.5 * above ratio
  - Doesn't compile, no Qed → 0.0

admitted_weight: each Admitted proof normally counts as 1.0 open obligation.
If the proof used admit. for sub-goals (Coq reports "No more goals, but there
are some goals you gave up"), it counts as 0.5 — rewarding incremental proof
progress within a single theorem.

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


_GAVE_UP_RE = re.compile(r"No more goals, but there are some goals you gave up")


def _extract_goal_states(filepath, content):
    """Run a second coqc pass with Show. before each Admitted. to capture goals.

    Returns a list of (theorem_name, goal_text, gave_up) triples.
    ``gave_up`` is True when Coq reports "No more goals, but there are some
    goals you gave up" — meaning the LLM used ``admit.`` to close sub-goals,
    making real progress inside this theorem even though it ends with Admitted.

    Completely general — works for any .v file.  Only called when the file
    already compiles (so the Show. pass is guaranteed to succeed).
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

    # Split stdout into per-Show blocks.  Each Show. output is separated by
    # either a "N goal(s)" header or a "No more goals, but..." header.
    # We walk line-by-line to pair each block with its theorem name and detect
    # the "gave up" marker.
    stdout_lines = stdout.strip().splitlines()

    # Each Show. produces one of:
    #   A) "N goal(s)\n<goal content>"          — real unsolved goals
    #   B) "No more goals, but ...\nN goal(s)\n<gave-up content>\nYou need..."
    #      — all real goals solved, only admitted sub-goals remain
    #   C) "No more goals."                     — fully proved (shouldn't happen
    #      for Admitted. but possible with admit-all)

    blocks = []  # list of (goal_text_lines, gave_up_bool)
    current_lines = []
    current_gave_up = False
    in_block = False

    for line in stdout_lines:
        stripped = line.strip()
        # Detect "No more goals, but there are some goals you gave up"
        if _GAVE_UP_RE.search(stripped):
            # Start a new block marked as gave_up
            if in_block:
                blocks.append((list(current_lines), current_gave_up))
            current_lines = []
            current_gave_up = True
            in_block = True
            continue
        # Detect "N goal(s)" header
        if re.match(r"^\d+ goals?\s*$", stripped):
            if in_block and not current_gave_up:
                # Previous block was a normal goals block; save it
                blocks.append((list(current_lines), current_gave_up))
                current_lines = []
                current_gave_up = False
            elif not in_block:
                current_lines = []
                current_gave_up = False
            in_block = True
            current_lines.append(line)
            continue
        # Detect bare "No more goals." (fully proved — skip this theorem)
        if stripped == "No more goals.":
            if in_block:
                blocks.append((list(current_lines), current_gave_up))
                current_lines = []
                current_gave_up = False
                in_block = False
            # This represents a fully-proved Admitted; add empty block
            blocks.append(([], False))
            continue
        # "You need to go back and solve them." — end of a gave_up block
        if "You need to go back" in stripped:
            if in_block:
                blocks.append((list(current_lines), current_gave_up))
                current_lines = []
                current_gave_up = False
                in_block = False
            continue
        if in_block:
            current_lines.append(line)

    if in_block and current_lines:
        blocks.append((list(current_lines), current_gave_up))

    # Pair blocks with theorem names (1:1 order)
    results = []
    for i, (block_lines, gave_up) in enumerate(blocks):
        name = theorem_names[i] if i < len(theorem_names) else "?"
        # Trim: stop at Check output or other non-goal lines after separator
        trimmed = []
        past_separator = False
        for line in block_lines:
            if "======" in line:
                past_separator = True
                trimmed.append(line)
                continue
            if past_separator and line and not line[0].isspace() and ":" in line:
                break
            trimmed.append(line)
        goal_text = "\n".join(trimmed[:15]).strip()
        results.append((name, goal_text, gave_up))

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


def _recently_proved_bodies(content):
    """Extract proof bodies for theorems that were Admitted in initial_program.v
    but are now Qed in the current program.  Returns [(name, body_snippet)].

    This lets the LLM see its own successful proof patterns and reuse them
    for structurally similar theorems.  No leakage — bodies come from the
    LLM's own output, not from any solution.
    """
    ev_dir = os.path.dirname(os.path.abspath(__file__))
    init_path = os.path.join(ev_dir, "initial_program.v")
    try:
        init_content = open(init_path).read()
    except OSError:
        return []

    # Find which theorems are Admitted in initial
    init_admitted = set()
    current_name = None
    for line in _strip_comments(init_content).splitlines():
        m = re.match(r"\s*(?:Theorem|Lemma|Corollary|Proposition|Fact)\s+(\w+)", line)
        if m:
            current_name = m.group(1)
        if "Admitted." in line and current_name:
            init_admitted.add(current_name)
            current_name = None

    if not init_admitted:
        return []

    # Find which of those are now Qed in current, and extract proof body.
    # Walk the file line-by-line to correctly pair theorem names with their
    # proof bodies, avoiding cross-boundary regex matches.
    stripped = _strip_comments(content)
    results = []
    current_name = None
    in_proof = False
    proof_lines = []

    for line in stripped.splitlines():
        heading = re.match(
            r"\s*(?:Theorem|Lemma|Corollary|Proposition|Fact)\s+(\w+)", line
        )
        if heading:
            current_name = heading.group(1)
            in_proof = False
            proof_lines = []
        if re.match(r"\s*Proof\b", line):
            in_proof = True
            proof_lines = []
            continue
        if in_proof and re.search(r"\b(?:Qed|Defined)\s*\.", line):
            if current_name and current_name in init_admitted and proof_lines:
                snippet = "\n".join(proof_lines[:10])
                if len(proof_lines) > 10:
                    snippet += "\n  ..."
                results.append((current_name, snippet))
            in_proof = False
            current_name = None
            continue
        if in_proof and re.search(r"\bAdmitted\s*\.", line):
            in_proof = False
            current_name = None
            continue
        if in_proof:
            proof_lines.append(line.strip())

    return results


def _build_feedback(compiles, done, qed, admitted, todo, axioms=0,
                    goal_states=None, proof_patterns=None):
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

    header_text = " ".join(parts)
    sections = [header_text]
    used = len(header_text)

    # Proof patterns (recently proved bodies the LLM can reuse)
    if proof_patterns:
        pp_header = "\nRecently proved (patterns to reuse):"
        sections.append(pp_header)
        used += len(pp_header)
        for name, body in proof_patterns[-3:]:
            entry = f"\n[{name}] Proof.\n  {body}\n  Qed."
            if used + len(entry) > _FEEDBACK_BUDGET:
                break
            sections.append(entry)
            used += len(entry)

    # Goal states for remaining Admitted proofs
    if goal_states:
        gs_header = "\nRemaining proof goals:"
        sections.append(gs_header)
        used += len(gs_header)
        added = 0
        for item in goal_states:
            name, goals = item[0], item[1]
            gave_up = item[2] if len(item) > 2 else False
            marker = " (has sub-goal progress via admit.)" if gave_up else ""
            entry = f"\n[{name}]{marker}\n{goals}"
            if used + len(entry) > _FEEDBACK_BUDGET:
                omitted = len(goal_states) - added
                sections.append(f"\n(... {omitted} more goal(s) omitted)")
                break
            sections.append(entry)
            used += len(entry)
            added += 1

    return "\n".join(sections)


def _initial_proof_obligation_count():
    """Count proof obligations (Qed + Admitted) in initial_program.v.

    Used as a floor in two places:
    1. Score denominator: prevents gaming by dropping most of the spec.
    2. Done guard: the program must have at least this many Qed+Admitted
       to be considered complete (prevents trivial spec replacement).

    Only counts Qed + Admitted (proof terms), NOT todo or Axiom.  Todos
    consolidate when implemented (e.g. 2 todos in a function body become
    0 when the function is filled in), so counting them would make the
    floor too high for solved programs.
    """
    ev_dir = os.path.dirname(os.path.abspath(__file__))
    init_path = os.path.join(ev_dir, "initial_program.v")
    try:
        content = open(init_path).read()
    except OSError:
        return 0
    q, a = _count_proof_terms(content)
    return q + a


_INITIAL_PROOF_OBLS = _initial_proof_obligation_count()


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

    # Extract goal states for Admitted proofs (only when file compiles)
    goal_states = []
    if compiles and admitted_count > 0:
        goal_states = _extract_goal_states(program_path, content)

    # Compute admitted weight: proofs where the LLM used admit. for sub-goals
    # count as 0.5 instead of 1.0, rewarding incremental proof progress.
    gave_up_count = sum(1 for gs in goal_states if gs[2])
    normal_admitted = admitted_count - gave_up_count
    admitted_weight = normal_admitted + 0.5 * gave_up_count

    open_obligations = admitted_weight + todo_count + axiom_count
    total = qed_count + open_obligations

    # 'done' requires: compiles, no open obligations, at least one Qed, and
    # at least as many proof terms (Qed) as the initial program had proof
    # obligations (Qed+Admitted).  This prevents trivial spec replacement
    # while allowing todo consolidation (todos merge when implemented).
    done = (compiles and admitted_count == 0 and todo_count == 0
            and axiom_count == 0 and qed_count > 0
            and qed_count >= _INITIAL_PROOF_OBLS)

    if done:
        score = 1.0
    elif total > 0:
        effective_total = max(total, _INITIAL_PROOF_OBLS) if _INITIAL_PROOF_OBLS > 0 else total
        ratio = qed_count / effective_total
        score = ratio if compiles else 0.5 * ratio
    else:
        score = 0.0

    # Extract recently proved proof patterns for feedback
    proof_patterns = _recently_proved_bodies(content) if compiles else []

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
                               goal_states=goal_states,
                               proof_patterns=proof_patterns)
    if feedback:
        artifacts["feedback"] = feedback

    return EvaluationResult(metrics=metrics, artifacts=artifacts)
