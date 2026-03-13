#!/usr/bin/env python3
"""Multi-turn iterative baseline for Coq co-synthesis.

Naive single-thread conversation loop — no search, no population:
    (current program + feedback) → LLM → new program → evaluate → repeat

Context is compacted when it grows too large: the system message and first
user turn (original spec) are always kept; only middle turns are dropped.

Usage:
    python run_iterative_baseline.py [problem ...] [--iters 100] [--out SUBDIR]

Examples:
    python run_iterative_baseline.py                         # all problems
    python run_iterative_baseline.py redblack_tree           # one problem
    python run_iterative_baseline.py binomial_queue --iters 50
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time

import openai

# ── Configuration ─────────────────────────────────────────────────────────────

PROBLEMS_DIR      = os.path.dirname(os.path.abspath(__file__))
MODEL             = "gemini-3-pro-preview"
API_BASE          = "https://generativelanguage.googleapis.com/v1beta/openai/"
API_KEY           = os.environ.get("GEMINI_API_KEY", "")
TEMPERATURE       = 0.8
MAX_TOKENS        = 16_000
LLM_TIMEOUT       = 600        # seconds per LLM call
COQC_TIMEOUT      = 120        # seconds per coqc call
MAX_CONTEXT_CHARS = 80_000     # compact when total message text exceeds this

SYSTEM_PROMPT = """\
You are an expert Coq proof engineer performing correct-by-construction synthesis.

The .v file contains holes:
  - `Axiom todo : forall {A : Type}, A.`  typed hole for unfinished expressions
  - `Admitted.`  placeholder for unfinished proofs
  - `Axiom` declarations that should become `Inductive` or `Definition`

Your goal: fill every hole until the file compiles with no Admitted and no todo.

Each call: make ONE step of progress.
  - For easy theorems: prove it fully with Qed., or fill one todo/Axiom.
  - For hard theorems (many sub-goals or complex case analysis): set up the
    proof structure and use `admit.` on branches you cannot solve yet. On the
    next call, replace one `admit.` with real tactics.
Working within a theorem over multiple calls via `admit.` is the preferred
approach for hard proofs. Work bottom-up: prove prerequisites first.
The file MUST compile with coqc after your edit.

Output the COMPLETE updated .v file inside a single ```coq ... ``` block.
No explanations. No text outside the code block.

Proof patterns:
  - Conjunctive theorems (forall x, P x /\\ Q x): prove directly by
    `induction x` then `split; intros`. Both halves appear in the IH.
    Do NOT split into separate lemmas — you lose inductive strength.
  - Generalize before induction: `revert` variables that depend on the
    induction variable so the IH quantifies over them.
  - Complex function in goal: when the goal has `f (g x)` and `f` matches
    on its argument, `destruct (g x)` to expose which arm applies.
    Handle one arm per call with `admit.` on the rest.

Rules:
  - Do NOT remove or rename existing lemmas/theorems or change their statements.
  - Do NOT close a proof with `exact todo.` — use real tactics.
  - Use `From Stdlib Require Import` (Coq 9.x), NOT `From Coq Require Import`.
  - Avoid `repeat rewrite` — it can diverge. Use targeted single rewrites.
  - Never write `do N eexists` — provide explicit witnesses.

Scoring: score = Qed / (Qed + Admitted + todo + axioms).
  1.0 when fully done, 0.0 if the file does not compile.
"""

# ── Evaluation (self-contained, no skydiscover dependency) ───────────────────

_COQ_COMMENT    = re.compile(r"\(\*.*?\*\)", re.DOTALL)
_AXIOM_TODO_PAT = re.compile(r"^\s*Axiom\s+todo\b.*$", re.MULTILINE)
_FENCE_RE       = re.compile(r"```[a-zA-Z]*\n(.*?)```", re.DOTALL)
_ENV_BINDING    = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*\s*[:,]")

_TIMEOUT_MSG = (
    "Timeout: coqc exceeded the time limit. Likely a diverging tactic "
    "(repeat rewrite, eauto in large context, do N eexists). "
    "Rewrite the proof with explicit, targeted tactics."
)


def _strip_fences(text: str) -> str:
    """Extract Coq source from markdown fences, or return text as-is."""
    matches = _FENCE_RE.findall(text)
    if matches:
        return max(matches, key=len).strip()
    lines = text.strip().splitlines()
    if lines and re.match(r"^```", lines[0]):
        lines = lines[1:]
    if lines and re.match(r"^```\s*$", lines[-1]):
        lines = lines[:-1]
    if lines and re.match(r"^[Cc]oq\s*$", lines[0]):
        lines = lines[1:]
    return "\n".join(lines)


def _strip_comments(text: str) -> str:
    return _COQ_COMMENT.sub("", text)


def _count_metrics(content: str):
    s = _strip_comments(content)
    qed      = len(re.findall(r"\bQed\s*\.",      s))
    defined  = len(re.findall(r"\bDefined\s*\.",  s))
    admitted = len(re.findall(r"\bAdmitted\s*\.", s))
    no_axiom = _AXIOM_TODO_PAT.sub("", s)
    todo     = len(re.findall(r"\btodo\b",         no_axiom))
    all_ax   = len(re.findall(r"^\s*Axiom\b",      s, re.MULTILINE))
    todo_ax  = len(re.findall(r"^\s*Axiom\s+todo\b", s, re.MULTILINE))
    axioms   = all_ax - todo_ax
    return qed + defined, admitted, todo, axioms


def _initial_proof_obligations(problem_dir: str) -> int:
    """Floor for score denominator — prevents trivial spec replacement."""
    path = os.path.join(problem_dir, "initial_program.v")
    try:
        content = open(path).read()
    except OSError:
        return 0
    q, a, _, _ = _count_metrics(content)
    return q + a


def _postprocess_error(stderr: str) -> str:
    """Strip verbose 'In environment' blocks from coqc errors."""
    if not stderr:
        return ""
    lines = stderr.strip().splitlines()
    error_idx = next((i for i, l in enumerate(lines) if "Error:" in l), None)
    if error_idx is None:
        return "\n".join(lines[-12:])[-2000:]
    header = []
    for i in range(error_idx - 1, max(-1, error_idx - 50), -1):
        if lines[i].strip().startswith("File "):
            header = [lines[i]]
            break
    body, in_env = [], False
    for line in lines[error_idx:]:
        s = line.strip()
        if s == "In environment":
            in_env = True; continue
        if in_env:
            if not s:
                in_env = False; continue
            if _ENV_BINDING.match(s) or (line.startswith("  ") and not _ENV_BINDING.match(s)):
                continue
            in_env = False
        body.append(line)
        if len(body) >= 10:
            break
    return "\n".join(header + body).strip()[-2000:]


def _cleanup(path: str):
    base = path.rsplit(".v", 1)[0]
    for ext in [".vo", ".vos", ".vok", ".glob", ".aux"]:
        try: os.remove(base + ext)
        except FileNotFoundError: pass
    d, f = os.path.split(path)
    try: os.remove(os.path.join(d, "." + os.path.splitext(f)[0] + ".aux"))
    except FileNotFoundError: pass


def _run_coqc(filepath: str):
    filepath = os.path.abspath(filepath)
    try:
        r = subprocess.run(
            ["coqc", os.path.basename(filepath)],
            capture_output=True, text=True, timeout=COQC_TIMEOUT,
            cwd=os.path.dirname(filepath),
        )
        return r.returncode == 0, r.stderr
    except subprocess.TimeoutExpired:
        return False, _TIMEOUT_MSG


def evaluate(program_text: str, problem_dir: str, floor: int):
    """Evaluate a program string. Returns (metrics_dict, cleaned_text)."""
    cleaned = _strip_fences(program_text)
    qed, admitted, todo, axioms = _count_metrics(cleaned)

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".v", dir=problem_dir, delete=False
    ) as f:
        f.write(cleaned)
        tmp = f.name

    try:
        compiles, stderr = _run_coqc(tmp)
    finally:
        try: os.remove(tmp)
        except FileNotFoundError: pass
        _cleanup(tmp)

    open_weight = admitted + todo + axioms
    total       = qed + open_weight
    eff_total   = max(total, floor) if floor > 0 else total

    done  = compiles and admitted == 0 and todo == 0 and axioms == 0 and qed >= floor
    if done:
        score = 1.0
    elif eff_total > 0:
        ratio = qed / eff_total
        score = ratio if compiles else 0.5 * ratio
    else:
        score = 0.0

    return {
        "score":    score,
        "compiles": compiles,
        "qed":      qed,
        "admitted": admitted,
        "todo":     todo,
        "axioms":   axioms,
        "done":     done,
        "error":    _postprocess_error(stderr) if not compiles else "",
    }, cleaned


# ── Context compaction ────────────────────────────────────────────────────────

def compact_messages(messages: list) -> list:
    """Drop middle turns when context is too large.

    Always keeps:
      messages[0]  — system prompt
      messages[1]  — first user turn (contains original spec)
      messages[2]  — first assistant turn (LLM's first attempt, if present)
    Drops turns in the middle, keeps the last 4 messages (2 most recent turns).
    Inserts a brief summary note where the dropped turns were.
    """
    total = sum(len(m["content"]) for m in messages)
    if total <= MAX_CONTEXT_CHARS or len(messages) <= 7:
        return messages

    head = messages[:3]   # system + first user + first assistant
    tail = messages[-4:]  # last 2 full turns
    n_dropped = len(messages) - len(head) - len(tail)

    note = {
        "role": "user",
        "content": (
            f"[{n_dropped} earlier turn(s) omitted to stay within context limits. "
            "The original spec is in the first message above. "
            "Continue from the latest program shown below.]"
        ),
    }
    return head + [note] + tail


# ── Main loop ─────────────────────────────────────────────────────────────────

def run_iterative(problem_name: str, max_iters: int, out_subdir: str):
    problem_dir = os.path.join(PROBLEMS_DIR, problem_name)
    init_path   = os.path.join(problem_dir, "initial_program.v")
    if not os.path.exists(init_path):
        print(f"[{problem_name}] SKIP — no initial_program.v")
        return None

    spec  = open(init_path).read()
    floor = _initial_proof_obligations(problem_dir)

    client  = openai.OpenAI(base_url=API_BASE, api_key=API_KEY)
    out_dir = os.path.join(problem_dir, out_subdir)
    os.makedirs(out_dir, exist_ok=True)
    log_path = os.path.join(out_dir, "iteration_log.jsonl")

    # Clear old log
    open(log_path, "w").close()

    done = False
    i    = 0  # guards total_iters if max_iters == 0

    # Compute real initial score (initial file already has given Qed proofs)
    init_q, init_a, init_t, init_x = _count_metrics(spec)
    init_open      = init_a + init_t + init_x
    init_total     = init_q + init_open
    init_eff_total = max(init_total, floor) if floor > 0 else init_total
    init_score     = (init_q / init_eff_total) if init_eff_total > 0 else 0.0

    best_score, best_program, best_iter = init_score, spec, 0

    print(f"\n[{problem_name}] iterative baseline | {max_iters} iters | {MODEL}")
    print(f"[{problem_name}] initial: score={init_score:.4f}  {init_q} Qed  "
          f"{init_a} Admitted  {init_t} todo  {init_x} axioms  floor={floor}")

    # Build initial conversation
    messages = [{"role": "system", "content": SYSTEM_PROMPT}]
    messages.append({
        "role": "user",
        "content": (
            f"Here is the Coq file to complete:\n\n```coq\n{spec}\n```\n\n"
            f"Score: {init_score:.4f} | {init_q} Qed | {init_a} Admitted "
            f"| {init_t} todo | {init_x} axioms.\n"
            f"Prove ONE Admitted lemma with Qed. (or fill one todo/Axiom if any). "
            f"Output the COMPLETE updated file."
        ),
    })

    for i in range(1, max_iters + 1):
        t0 = time.time()

        # Compact before calling LLM
        messages = compact_messages(messages)

        # LLM call
        try:
            resp = client.chat.completions.create(
                model=MODEL,
                messages=messages,
                temperature=TEMPERATURE,
                max_tokens=MAX_TOKENS,
                timeout=LLM_TIMEOUT,
            )
            llm_out = resp.choices[0].message.content
            if llm_out is None:
                raise ValueError("LLM returned None content")
        except Exception as e:
            print(f"[{problem_name}] iter {i:3d} LLM error: {e}")
            # Re-prompt without adding a broken turn
            continue

        elapsed = time.time() - t0

        # Evaluate
        m, cleaned = evaluate(llm_out, problem_dir, floor)

        if m["score"] > best_score:
            best_score, best_program, best_iter = m["score"], cleaned, i

        done = m["done"]

        status = "DONE" if done else ("OK  " if m["compiles"] else "FAIL")
        print(
            f"[{problem_name}] iter {i:3d} {status}  "
            f"score={m['score']:.4f}  qed={m['qed']}  adm={m['admitted']}  "
            f"best={best_score:.4f}  ({elapsed:.1f}s)"
        )

        # Log
        entry = {
            "iter": i, "score": m["score"], "qed": m["qed"],
            "admitted": m["admitted"], "todo": m["todo"], "axioms": m["axioms"],
            "compiles": m["compiles"], "done": done,
            "best_score": best_score, "elapsed_s": round(elapsed, 1),
        }
        with open(log_path, "a") as f:
            f.write(json.dumps(entry) + "\n")

        if done:
            print(f"[{problem_name}] SOLVED at iter {i}!")
            break

        # Build next user message.
        # If the attempt compiled: add it to history and continue from it.
        # If it failed: revert to best working program and include the error.
        messages.append({"role": "assistant", "content": llm_out})

        if m["compiles"]:
            next_msg = (
                f"Score={m['score']:.4f} | {m['qed']} Qed | {m['admitted']} Admitted "
                f"| {m['todo']} todo | {m['axioms']} axioms.\n\n"
                f"Current program:\n\n```coq\n{cleaned}\n```\n\n"
                f"Next: prove ONE more Admitted lemma with Qed. "
                f"Output the COMPLETE updated file."
            )
        else:
            best_label = "initial spec" if best_iter == 0 else f"iter {best_iter}"
            next_msg = (
                f"That attempt did NOT compile.\n\nError:\n{m['error']}\n\n"
                f"Reverting to best working program "
                f"(score={best_score:.4f} | {best_label}):\n\n"
                f"```coq\n{best_program}\n```\n\n"
                f"Fix the compile error and prove ONE Admitted lemma. "
                f"Output the COMPLETE updated file."
            )

        messages.append({"role": "user", "content": next_msg})

    # Save results
    best_path = os.path.join(out_dir, "best_program.v")
    with open(best_path, "w") as f:
        f.write(best_program)

    result = {
        "problem":    problem_name,
        "model":      MODEL,
        "max_iters":  max_iters,
        "total_iters": i,
        "best_score": best_score,
        "best_iter":  best_iter,
        "solved":     done,
        "temperature": TEMPERATURE,
    }
    with open(os.path.join(out_dir, "result.json"), "w") as f:
        json.dump(result, f, indent=2)

    status = "SOLVED" if done else f"score={best_score:.4f}"
    print(f"[{problem_name}] Final: {status}  best_iter={best_iter}/{i}  → {out_dir}")
    return result


# ── CLI ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("problems", nargs="*", help="Problem name(s). Default: all.")
    parser.add_argument("--iters", type=int, default=100, help="Max iterations (default 100).")
    parser.add_argument("--out",   default="baseline_iterative", help="Output subdirectory name.")
    args = parser.parse_args()

    if not API_KEY:
        print("ERROR: set GEMINI_API_KEY environment variable first.")
        sys.exit(1)

    all_problems = sorted(
        d for d in os.listdir(PROBLEMS_DIR)
        if os.path.isdir(os.path.join(PROBLEMS_DIR, d))
        and os.path.exists(os.path.join(PROBLEMS_DIR, d, "initial_program.v"))
    )
    problems = [p for p in all_problems if p in args.problems] if args.problems else all_problems

    if not problems:
        print(f"No matching problems. Available: {all_problems}")
        sys.exit(1)

    print(f"Running iterative baseline: {len(problems)} problem(s), {args.iters} iters each.")
    print(f"Problems: {problems}\n")

    results = {}
    for p in problems:
        r = run_iterative(p, args.iters, args.out)
        if r:
            results[p] = r
        print()

    # Summary table
    print("\n" + "=" * 70)
    print("ITERATIVE BASELINE RESULTS")
    print("=" * 70)
    print(f"{'Problem':<22} {'Score':>6} {'Solved':>7} {'BestIter':>9} {'TotalIter':>10}")
    print("-" * 70)
    for name in sorted(results):
        r = results[name]
        print(
            f"{name:<22} {r['best_score']:>6.4f} {str(r['solved']):>7} "
            f"{r['best_iter']:>9} {r['total_iters']:>10}"
        )


if __name__ == "__main__":
    main()
