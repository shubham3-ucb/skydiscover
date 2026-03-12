"""Evaluator for Coq co-synthesis: implementation + proof together.

Generic for any .v file. Not problem-specific.

Scoring (always in [0, 1]):
  - Doesn't compile → 0.0, with coqc stderr as error (triggers retry)
  - Compiles, work remaining → qed / (qed + admitted + todo), always < 1
  - Compiles, done (no Admitted, no todo) → 1.0

The ratio qed/(qed+admitted+todo) honestly reflects how close to
completion the program is.  It can temporarily dip when the LLM adds
new sub-lemmas (Admitted) or branches (todo), but that is the correct
signal — population-based search (adaevolve) handles this fine.
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
    "Timeout: coqc exceeded 300s. "
    "Your proof is likely structurally correct but uses tactics that cause "
    "infinite unification loops. Common culprits:\n"
    "  - `do N eexists` — use explicit `exists a, b, c` instead\n"
    "  - `repeat rewrite app_assoc` — use a single targeted `rewrite` or "
    "`replace ... with ... by (rewrite !app_assoc; reflexivity)`\n"
    "  - `repeat split` with existential variables — use individual `split` "
    "followed by the immediate proof of each conjunct\n"
    "  - `auto` or `eauto` in large contexts — use explicit tactics\n"
    "Rewrite the proof using explicit witnesses and targeted rewrites."
)


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


def _build_feedback(compiles, done, qed, admitted, todo):
    """Build natural-language feedback for the LLM."""
    if not compiles:
        return None  # coqc stderr is already sent via error key
    if done:
        return "All obligations discharged. The file is complete."
    parts = []
    remaining = admitted + todo
    parts.append(f"{remaining} obligation(s) remain: {admitted} Admitted proof(s), {todo} todo expression(s).")
    if todo > 0:
        parts.append("Pick one todo expression and replace it with a concrete Coq term.")
    elif admitted > 0:
        parts.append("All expressions are filled. Prove one Admitted lemma with Qed.")
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
    code_length = len(content.splitlines())

    rc, stderr = _run_coqc(program_path)
    _cleanup_coq_artifacts(program_path)

    compiles = rc == 0
    done = compiles and admitted_count == 0 and todo_count == 0

    total = qed_count + admitted_count + todo_count
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
        "code_length": float(code_length),
        "done": 1.0 if done else 0.0,
    }

    if not compiles and stderr:
        metrics["error"] = stderr[-2000:]

    artifacts = {}
    feedback = _build_feedback(compiles, done, qed_count, admitted_count, todo_count)
    if feedback:
        artifacts["feedback"] = feedback

    return EvaluationResult(metrics=metrics, artifacts=artifacts)
