# Coq Evaluator — Exact Logic

Generic evaluator (`evaluator.py`) for Coq co-synthesis. Not problem-specific — works for any `.v` file.

---

## Entry Point

```python
evaluate(program_path: str) -> EvaluationResult
```

Called by AdaEvolve once per program candidate. Returns `metrics` dict + `artifacts` dict.

---

## Step 1 — Strip Markdown Fences

`_strip_markdown_fences(content)` — LLMs sometimes wrap the `.v` file in a code block. Strips:
- Opening fence: `` ```coq ``, `` ```v ``, ` ``` ` etc.
- Closing ` ``` `
- Bare language tag on first line (`coq`, `Coq`)

Writes cleaned content back to disk before compiling.

---

## Step 2 — Count Obligations (static, before coqc)

All counts are performed on **comment-stripped** source (`(* ... *)` removed, including nested/multiline).

| Counter | Regex | What it finds |
|---------|-------|---------------|
| `qed_count` | `\bQed\s*\.` + `\bDefined\s*\.` | Completed proof terms |
| `admitted_count` | `\bAdmitted\s*\.` | Open proof stubs |
| `todo_count` | `\btodo\b` (excluding the `Axiom todo` declaration line) | Open expression holes |
| `axiom_count` | `^\s*Axiom\b` minus `^\s*Axiom\s+todo\b` | Real Axiom placeholders (e.g. `Axiom` that should become `Inductive`) |

---

## Step 3 — Compile

```python
subprocess.run(["coqc", basename], cwd=dirname, timeout=300)
```

- `compiles = (returncode == 0)`
- On **TimeoutExpired**: `compiles = False`, error = verbose guidance about diverging tactics (`repeat rewrite`, `eauto`, `do N eexists`, etc.)
- On compile failure: error passed through `_postprocess_error()` (see below)

---

## Step 4 — Goal State Extraction (only if compiles and admitted_count > 0)

`_extract_goal_states(filepath, content)` runs a **second coqc pass** to capture proof state at each `Admitted.`:

1. Find all `Admitted.` occurrences **not** inside comments (character-level comment map)
2. Inject `Show. ` immediately before each `Admitted.` (in reverse order to preserve offsets)
3. Write to a temp file, run `coqc`, capture **stdout**
4. Parse stdout to extract per-theorem goal blocks

**Show. output types:**
- `"N goal(s)\n<goal text>"` — real unsolved goals remain
- `"No more goals, but there are some goals you gave up\n..."` — LLM used `admit.` for sub-goals; all top-level goals solved but sub-goals admitted → **`gave_up = True`**
- `"No more goals."` — fully proved (rare with `Admitted.`)

Returns `[(theorem_name, goal_text, gave_up), ...]` — one entry per `Admitted.` in document order.

---

## Step 5 — Admitted Weight (partial credit for admit.)

```python
gave_up_count  = sum(1 for gs in goal_states if gs[2])
normal_admitted = admitted_count - gave_up_count
admitted_weight = normal_admitted + 0.5 * gave_up_count
```

When the LLM writes `admit.` (lowercase) for hard sub-goals and ends with `Admitted.`:
- Coq accepts the file (compiles = True)
- The "gave up" marker appears in `Show.` output
- That theorem counts as **0.5** open obligation instead of **1.0**

This rewards incremental proof progress within a single hard theorem.

---

## Step 6 — Score

```python
open_obligations = admitted_weight + todo_count + axiom_count
total            = qed_count + open_obligations
effective_total  = max(total, _INITIAL_PROOF_OBLS)   # denominator floor
```

| Condition | Score |
|-----------|-------|
| `done == True` | `1.0` |
| `compiles`, `total > 0` | `qed_count / effective_total` |
| `not compiles`, `total > 0` | `0.5 * (qed_count / effective_total)` |
| `total == 0` | `0.0` |

**`_INITIAL_PROOF_OBLS`** — computed once at module load time from `initial_program.v` (Qed + Admitted count). Used as the denominator floor to prevent score gaming: if an LLM drops half the spec and proves the remainder, the denominator stays at the original obligation count.

---

## Step 7 — Done Guard

```python
done = (compiles
        and admitted_count == 0
        and todo_count == 0
        and axiom_count == 0
        and qed_count > 0
        and qed_count >= _INITIAL_PROOF_OBLS)
```

All five conditions must hold. The `qed_count >= _INITIAL_PROOF_OBLS` check blocks trivial spec replacement (e.g. replacing 28 theorems with one `Theorem dummy : True`).

---

## Step 8 — Error Postprocessing

`_postprocess_error(stderr)` strips `coqc`'s verbose "In environment" blocks:

```
File "foo.v", line 42, characters 5-10:
In environment
  n : nat
  l : list nat
  H : sorted l
  ...               ← 15-30 lines stripped
Error: The term "n" has type "nat" which should be coerced to ...
```

**After stripping:**
```
File "foo.v", line 42, characters 5-10:
Error: The term "n" has type "nat" which should be coerced to ...
```

Algorithm:
1. Find first line containing `"Error:"`
2. Scan backward (up to 50 lines) to find `"File ..."` locator
3. From `"Error:"` onward: skip lines matching `In environment` + subsequent hypothesis bindings (`name : type` or indented continuations)
4. Keep first 10 non-environment lines, truncate to 2000 chars

Reduces error message size by ~74%.

---

## Step 9 — Feedback Construction

`_build_feedback(...)` assembles the `artifacts["feedback"]` string (≤1850 chars):

1. **Header** — compile status + remaining obligation count + next action hint
2. **Proof patterns** (last 3 recently proved) — via `_recently_proved_bodies()`:
   - Finds theorems that were `Admitted` in `initial_program.v` but are now `Qed` in the current file
   - Extracts proof body (up to 10 lines) as a reusable tactic pattern
   - No leakage — these are the LLM's own proofs, not ground truth
3. **Goal states** — from `_extract_goal_states()` output, one block per `Admitted.` theorem
   - Marks `(has sub-goal progress via admit.)` for gave-up theorems

---

## Metrics Dict

```python
{
    "combined_score": float,   # primary score in [0, 1]
    "compiles":       float,   # 1.0 or 0.0
    "qed_count":      float,
    "admitted_count": float,
    "todo_count":     float,
    "axiom_count":    float,
    "code_length":    float,   # lines
    "done":           float,   # 1.0 or 0.0
    # only present when not compiles:
    "error":          str,
}
```

---

## _INITIAL_PROOF_OBLS Computation

```python
# Runs at module import time, once per evaluator.py load
_INITIAL_PROOF_OBLS = _initial_proof_obligation_count()
# = Qed + Admitted count in ./initial_program.v
```

Only counts `Qed`/`Admitted` — NOT `todo` or `Axiom`. This is because `todo` expressions consolidate (e.g. 3 `todo`s in a function body all disappear when the function is filled in with one expression), so counting them would set an unreachably high floor.

---

## coqc Invocation

```python
subprocess.run(
    ["coqc", os.path.basename(filepath)],
    cwd=os.path.dirname(filepath),
    timeout=300,
)
```

Run from the file's own directory so that relative `Require Import` paths resolve correctly. If a problem needs `-Q`/`-R` library flags, modify `_run_coqc()` in that problem's `evaluator.py`.
