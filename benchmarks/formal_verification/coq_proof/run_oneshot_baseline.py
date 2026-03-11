#!/usr/bin/env python3
"""One-shot baseline: send each problem to Gemini, ask it to solve in one go, evaluate."""

import os
import sys
import json
import subprocess
import tempfile
import re
import time

import openai

PROBLEMS_DIR = os.path.dirname(os.path.abspath(__file__))
MODEL = "gemini-3-pro-preview"
API_BASE = "https://generativelanguage.googleapis.com/v1beta/openai/"
API_KEY = os.environ.get("GEMINI_API_KEY", "")

ONESHOT_PROMPT = """You are an expert Coq proof engineer. You will receive a Coq file with:
- `Axiom todo : forall {A : Type}, A.` — typed holes for unfinished expressions
- Functions with `todo` as the body
- Theorems/lemmas marked `Admitted.` — unfinished proofs

Your task: produce the COMPLETE, FINAL version of this file where:
1. Every `todo` expression is replaced with a concrete implementation
2. Every `Admitted.` proof is completed with `Qed.`
3. The file compiles with `coqc`

Output ONLY the complete Coq file. No explanations, no markdown fences.

Important Coq tips:
- Use `From Stdlib` not `From Coq` (Coq 9.x).
- Use `length_app` not `app_length`.
- Never use `do N eexists` — use explicit `exists a, b, c.`
- Never use `repeat rewrite` — use targeted single rewrites.
- When `lia` fails on `length`, try `simpl in *` first.
"""

COQ_COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
AXIOM_TODO_LINE = re.compile(r"^\s*Axiom\s+todo\b.*$", re.MULTILINE)


def strip_fences(content):
    lines = content.strip().splitlines()
    if not lines:
        return content
    if re.match(r'^```\s*[a-zA-Z]*\s*$', lines[0]):
        lines = lines[1:]
    if lines and re.match(r'^```\s*$', lines[-1]):
        lines = lines[:-1]
    if lines and re.match(r'^[Cc]oq\s*$', lines[0]):
        lines = lines[1:]
    return '\n'.join(lines)


def count_metrics(content):
    stripped = COQ_COMMENT.sub("", content)
    qed = len(re.findall(r"\bQed\s*\.", stripped))
    admitted = len(re.findall(r"\bAdmitted\s*\.", stripped))
    defined = len(re.findall(r"\bDefined\s*\.", stripped))
    without_axiom = AXIOM_TODO_LINE.sub("", stripped)
    todo = len(re.findall(r"\btodo\b", without_axiom))
    return qed + defined, admitted, todo


def run_coqc(filepath, timeout=300):
    filepath = os.path.abspath(filepath)
    try:
        r = subprocess.run(
            ["coqc", os.path.basename(filepath)],
            capture_output=True, text=True, timeout=timeout,
            cwd=os.path.dirname(filepath),
        )
        return r.returncode == 0, r.stderr
    except subprocess.TimeoutExpired:
        return False, "Timeout (300s)"


def evaluate_solution(content):
    content = strip_fences(content)
    qed, admitted, todo = count_metrics(content)
    total = qed + admitted + todo

    with tempfile.NamedTemporaryFile(suffix=".v", delete=False, mode='w') as f:
        f.write(content)
        tmp = f.name

    try:
        compiles, stderr = run_coqc(tmp)
    finally:
        for ext in [".v", ".vo", ".vos", ".vok", ".glob"]:
            try:
                os.remove(tmp.replace(".v", ext))
            except FileNotFoundError:
                pass
        base = os.path.splitext(tmp)[0]
        d, fn = os.path.split(tmp)
        for aux in [base + ".aux", os.path.join(d, "." + os.path.splitext(fn)[0] + ".aux")]:
            try:
                os.remove(aux)
            except FileNotFoundError:
                pass

    done = compiles and admitted == 0 and todo == 0
    if not compiles:
        score = 0.0
    elif done:
        score = 1.0
    elif total > 0:
        score = qed / total
    else:
        score = 0.0

    return {
        "score": score,
        "compiles": compiles,
        "qed": qed,
        "admitted": admitted,
        "todo": todo,
        "done": done,
        "lines": len(content.splitlines()),
        "error": stderr[:500] if not compiles else "",
    }, content


def run_oneshot(problem_name):
    problem_dir = os.path.join(PROBLEMS_DIR, problem_name)
    initial = os.path.join(problem_dir, "initial_program.v")

    if not os.path.exists(initial):
        return problem_name, {"error": "no initial_program.v"}

    spec = open(initial).read()

    client = openai.OpenAI(base_url=API_BASE, api_key=API_KEY)

    print(f"[{problem_name}] Sending to {MODEL}...")
    t0 = time.time()

    try:
        response = client.chat.completions.create(
            model=MODEL,
            messages=[
                {"role": "system", "content": ONESHOT_PROMPT},
                {"role": "user", "content": f"Here is the Coq file to complete:\n\n{spec}"},
            ],
            temperature=0.3,
            max_tokens=16000,
        )
        llm_output = response.choices[0].message.content
    except Exception as e:
        return problem_name, {"error": str(e)}

    elapsed = time.time() - t0
    print(f"[{problem_name}] Got response in {elapsed:.1f}s, evaluating...")

    metrics, cleaned = evaluate_solution(llm_output)
    metrics["llm_time_s"] = round(elapsed, 1)

    baseline_dir = os.path.join(problem_dir, "baseline_oneshot")
    os.makedirs(baseline_dir, exist_ok=True)

    with open(os.path.join(baseline_dir, "solution.v"), "w") as f:
        f.write(cleaned)
    with open(os.path.join(baseline_dir, "result.json"), "w") as f:
        json.dump(metrics, f, indent=2)

    status = "SOLVED" if metrics["done"] else f"score={metrics['score']:.2f}"
    print(f"[{problem_name}] {status} (qed={metrics['qed']} admitted={metrics['admitted']} todo={metrics['todo']} compiles={metrics['compiles']} time={elapsed:.1f}s)")

    return problem_name, metrics


def main():
    if not API_KEY:
        print("Set GEMINI_API_KEY env var first")
        sys.exit(1)

    problems = sorted([
        d for d in os.listdir(PROBLEMS_DIR)
        if os.path.isdir(os.path.join(PROBLEMS_DIR, d))
        and os.path.exists(os.path.join(PROBLEMS_DIR, d, "initial_program.v"))
    ])

    if len(sys.argv) > 1:
        problems = [p for p in problems if p in sys.argv[1:]]

    print(f"Running one-shot baseline for {len(problems)} problems: {problems}\n")

    results = {}
    for p in problems:
        name, metrics = run_oneshot(p)
        results[name] = metrics
        print()

    print("\n" + "=" * 60)
    print("ONE-SHOT BASELINE RESULTS")
    print("=" * 60)
    print(f"{'Problem':<20} {'Score':>6} {'Compiles':>8} {'Qed':>4} {'Adm':>4} {'Todo':>4} {'Done':>5} {'Time':>6}")
    print("-" * 60)
    for name in sorted(results):
        m = results[name]
        if "error" in m and "score" not in m:
            print(f"{name:<20} ERROR: {m['error'][:40]}")
            continue
        print(f"{name:<20} {m['score']:>6.2f} {str(m['compiles']):>8} {m['qed']:>4} {m['admitted']:>4} {m['todo']:>4} {str(m['done']):>5} {m.get('llm_time_s','?'):>5}s")


if __name__ == "__main__":
    main()
