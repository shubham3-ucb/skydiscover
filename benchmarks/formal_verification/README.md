# Formal Verification Benchmark

## What this is

This benchmark asks SkyDiscover to perform **co-synthesis**: given only a formal specification (Coq type signature + correctness theorem), build the implementation and its machine-checked proof together, step by step, until `coqc` accepts the entire file with no holes. Every intermediate state must type-check — there is no guess-and-check.

## Problems

| Problem | Difficulty | Description |
|---|---|---|
| `all_less_than` | Easy | Check all list elements are below a bound |
| `insertion_sort` | Medium | Implement and verify a sorting algorithm |
| `regex_matcher` | Hard | Verified regex matcher via Brzozowski derivatives |

## Setup

```bash
brew install coq   # Rocq/Coq 9.x
export OPENAI_API_KEY="..."
cd skydiscover/
source .venv/bin/activate
```

## Run

All three benchmarks in parallel:
```bash
bash benchmarks/formal_verification/coq_proof/run_all.sh
```

Single benchmark:
```bash
skydiscover-run \
  benchmarks/formal_verification/coq_proof/regex_matcher/initial_program.v \
  benchmarks/formal_verification/coq_proof/regex_matcher/evaluator.py \
  --config benchmarks/formal_verification/coq_proof/regex_matcher/config.yaml \
  -o benchmarks/formal_verification/coq_proof/regex_matcher/outputs
```

## How it works

```
initial_program.v                        evaluator.py
┌────────────────────────────┐          ┌────────────────────────────────┐
│ Axiom todo : ∀{A}, A.      │          │ 1. coqc compiles the file      │
│                            │          │ 2. Count Qed / Admitted / todo │
│ Definition f := todo.      │─────────>│ 3. score = Qed/(Qed+Adm+todo) │
│                            │          │    0 if fails, 1.0 if complete │
│ Theorem spec : ...         │          │ 4. Return NL feedback to LLM   │
│ Proof. Admitted.           │          └────────────────────────────────┘
└────────────────────────────┘                        │
                 ▲                                    │
                 │  AdaEvolve (multi-island search)   │
                 └────────────────────────────────────┘
```

Each iteration the LLM takes **one step**: fill one `todo`, add sub-lemmas as `Admitted.`, prove the parent lemma → `Qed.`

Score is always in [0, 1]: `0.0` if it doesn't compile, `Qed / (Qed + Admitted + todo)` otherwise, `1.0` when fully done.

## Adding a new problem

Only `initial_program.v` is problem-specific. Copy `evaluator.py` and `config.yaml` from any existing problem unchanged.

```coq
(* initial_program.v *)
Require Import ...
Axiom todo : forall {A : Type}, A.

Definition my_func : <type> := todo.

Theorem my_spec : forall ..., <correctness property>.
Proof. Admitted.
```

Then run with the same command pattern above substituting `<name>`.

> **Note:** If your problem needs external Coq libraries, modify `_run_coqc()` in `evaluator.py` to pass `-Q`/`-R` flags.
