"""Evaluator for Coq co-synthesis: implementation + proof together.

Generic for any .v file. Not problem-specific.

Scoring (always in [0, 1]):
  - Doesn't compile → 0.0, with coqc stderr as error (triggers retry)
  - Compiles, work remaining → qed / (qed + admitted + todo + axioms), always < 1
  - Compiles, done (no Admitted, no todo, no axioms, qed > 0) → 1.0

Open obligations = Admitted proofs + todo expressions + non-todo Axiom declarations.
The ratio qed/(qed+obligations) honestly reflects how close to completion the
program is.  Population-based search (adaevolve) handles temporary score dips fine.
"""

import re
import subprocess
import os

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

    # Keep up to 3 lines before "Error:" as locator (File/line/chars),
    # but stop if we hit "In environment" — that's context noise.
    header_start = max(0, error_idx - 3)
    header = []
    for line in lines[header_start:error_idx]:
        if line.strip().startswith("In environment"):
            break
        header.append(line)

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
        return r.returncode, r.stderr
    except subprocess.TimeoutExpired:
        return 1, _TIMEOUT_GUIDANCE


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


def _build_feedback(compiles, done, qed, admitted, todo, axioms=0):
    """Build natural-language feedback for the LLM."""
    if not compiles:
        return None  # coqc stderr is already sent via error key
    if done:
        return "All obligations discharged. The file is complete."
    parts = []
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

    rc, stderr = _run_coqc(program_path)
    _cleanup_coq_artifacts(program_path)

    compiles = rc == 0
    open_obligations = admitted_count + todo_count + axiom_count
    done = compiles and open_obligations == 0 and qed_count > 0

    total = qed_count + open_obligations
    if not compiles:
        score = 0.0
    elif done:
        score = 1.0
    elif total > 0:
        score = qed_count / total
    else:
        score = 0.0

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
    feedback = _build_feedback(compiles, done, qed_count, admitted_count, todo_count, axiom_count)
    if feedback:
        artifacts["feedback"] = feedback

    return EvaluationResult(metrics=metrics, artifacts=artifacts)
