"""Evaluator for Coq co-synthesis: implementation + proof together.

Generic for any .v file. Not problem-specific.

Scoring (always in [0, 1]):
  - Doesn't compile → 0.0, with coqc stderr as error (triggers retry)
  - Compiles, not done → 1 - 1/(qed + 1)  (monotonic in qed, always < 1)
  - Compiles, done (no Admitted, no todo) → 1.0
"""

import re
import subprocess
import os

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


def _run_coqc(filepath):
    filepath = os.path.abspath(filepath)
    try:
        r = subprocess.run(
            ["coqc", os.path.basename(filepath)],
            capture_output=True, text=True, timeout=120,
            cwd=os.path.dirname(filepath),
        )
        return r.returncode, r.stderr
    except subprocess.TimeoutExpired:
        return 1, "Timeout: coqc exceeded 120s"


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


def evaluate(program_path):
    content = open(program_path).read()

    qed_count, admitted_count = _count_proof_terms(content)
    todo_count = _count_todos(content)

    rc, stderr = _run_coqc(program_path)
    _cleanup_coq_artifacts(program_path)

    compiles = rc == 0
    done = compiles and admitted_count == 0 and todo_count == 0

    if not compiles:
        score = 0.0
    elif done:
        score = 1.0
    else:
        score = 1.0 - 1.0 / (qed_count + 1)

    result = {
        "combined_score": score,
        "compiles": 1.0 if compiles else 0.0,
        "qed_count": qed_count,
        "admitted_count": admitted_count,
        "todo_count": todo_count,
        "done": 1.0 if done else 0.0,
    }

    if not compiles and stderr:
        result["error"] = stderr[-2000:]

    return result
