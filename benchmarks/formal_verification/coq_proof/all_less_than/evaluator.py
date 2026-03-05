"""Evaluator for Coq proof evolution.

Generic for any .v file using Lemma/Theorem/Proposition/Corollary/Fact.

Checks how many proof obligations the LLM successfully proved by:
1. Trying to compile the full file with coqc.
2. If that fails, testing each proof independently
   (other proofs replaced with Admitted).
"""

import re
import subprocess
import tempfile
import os

# Matches proof obligations: (Lemma|Theorem|...) name ... Proof. body (Qed.|Admitted.|Defined.)
# Step 1: strip Coq comments before matching to avoid false hits on Qed./Admitted. in comments.
_COQ_COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
_PROOF_KW = r"(?:Lemma|Theorem|Proposition|Corollary|Fact|Remark)"
_TERM_KW = r"(?:Qed|Admitted|Defined)\."
_PROOF_PATTERN = re.compile(
    rf"({_PROOF_KW}\s+(\w+)\s*.*?)(Proof\.)(.*?)({_TERM_KW})",
    re.DOTALL,
)


def _strip_comments(text):
    """Replace Coq comments (* ... *) with whitespace of equal length to preserve positions."""
    def _replace(m):
        return " " * (m.end() - m.start())
    return _COQ_COMMENT.sub(_replace, text)


def _find_proofs(content):
    """Find proof obligations, matching against comment-stripped text but returning original positions."""
    stripped = _strip_comments(content)
    return list(_PROOF_PATTERN.finditer(stripped))


def _run_coqc(filepath):
    """Run coqc, return (returncode, stderr)."""
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
    """Remove coqc build artifacts for a given .v file."""
    base = filepath.rsplit(".v", 1)[0]
    for ext in [".vo", ".vos", ".vok", ".glob", ".aux"]:
        try:
            os.remove(base + ext)
        except FileNotFoundError:
            pass
    # Also .aux with dot prefix
    d, f = os.path.split(filepath)
    aux = os.path.join(d, "." + f.rsplit(".v", 1)[0] + ".aux")
    try:
        os.remove(aux)
    except FileNotFoundError:
        pass


def _admit_all_except(content, matches, keep_idx):
    """Replace all proof bodies with Admitted except the one at keep_idx."""
    result = content
    for i in reversed(range(len(matches))):
        if i == keep_idx:
            continue
        m = matches[i]
        result = result[:m.start(3)] + "Proof. Admitted." + result[m.end(5):]
    return result


def evaluate(program_path):
    content = open(program_path).read()
    matches = _find_proofs(content)
    total = len(matches)
    if total == 0:
        return {
            "combined_score": 0.0,
            "artifacts": {"error": "No proof obligations found (expected Lemma/Theorem/... Proof. ... Qed.)"},
        }

    # Count how many use Qed/Defined vs Admitted
    proved_count = sum(1 for m in matches if m.group(5).strip() != "Admitted.")

    # Try full compile
    rc, stderr = _run_coqc(program_path)
    _cleanup_coq_artifacts(program_path)

    if rc == 0:
        return {
            "combined_score": proved_count / total,
            "compiles": 1.0,
            "proved": proved_count,
            "total": total,
        }

    # Full compile failed — test each proof independently
    proved = 0
    proof_results = {}
    proof_errors = {}

    for i, m in enumerate(matches):
        name = m.group(2)
        if m.group(5).strip() == "Admitted.":
            proof_results[name] = "skipped"
            continue

        test_content = _admit_all_except(content, matches, keep_idx=i)
        with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False) as f:
            f.write(test_content)
            tmp = f.name
        try:
            rc_i, stderr_i = _run_coqc(tmp)
            if rc_i == 0:
                proved += 1
                proof_results[name] = "proved"
            else:
                proof_results[name] = "failed"
                proof_errors[name] = stderr_i[-500:]
        finally:
            _cleanup_coq_artifacts(tmp)
            try:
                os.remove(tmp)
            except FileNotFoundError:
                pass

    return {
        "combined_score": proved / total,
        "compiles": 0.0,
        "proved": proved,
        "total": total,
        "proof_results": proof_results,
        "artifacts": {
            "full_error": stderr[-1000:],
            "proof_errors": proof_errors,
        },
    }
