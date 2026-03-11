# Formal Verification Benchmark

## What this is

This benchmark asks SkyDiscover to perform **co-synthesis**: given only a formal specification (Coq type signature + correctness theorem), build the implementation and its machine-checked proof together, step by step, until `coqc` accepts the entire file with no holes. Every intermediate state must type-check — there is no guess-and-check.

## Problems

| Problem | Difficulty | Description | Result |
|---|---|---|---|
| `all_less_than` | Easy | Check all list elements are below a bound | Score 1.0 at iteration 1 |
| `insertion_sort` | Medium | Implement and verify a sorting algorithm | Score 1.0 at iteration 14 |
| `regex_matcher` | Hard | Verified regex matcher via Brzozowski derivatives | Score 0.929 (13/14 proofs) at iteration 30 |
| `bst_verification` | Hard | Implement and verify a binary search tree | — |
| `pigeonhole` | Hard | Define `repeats` and prove the pigeonhole principle | — |

Best synthesized programs are in `<problem>/outputs/best/best_program.v`.

## Setup

```bash
brew install coq        # Rocq/Coq 9.x
export OPENAI_API_KEY="..."
cd skydiscover/
source .venv/bin/activate
```

## Run

All three in parallel:
```bash
bash benchmarks/formal_verification/coq_proof/run_all.sh
```

Single benchmark:
```bash
skydiscover-run \
  benchmarks/formal_verification/coq_proof/<name>/initial_program.v \
  benchmarks/formal_verification/coq_proof/<name>/evaluator.py \
  --config benchmarks/formal_verification/coq_proof/<name>/config.yaml \
  -o benchmarks/formal_verification/coq_proof/<name>/outputs
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

Each iteration the LLM takes **one step**: fill one `todo` with a concrete expression, add sub-lemmas as `Admitted.` for any new holes, then prove the parent lemma → `Qed.`

Score is always in [0, 1]: `0.0` if it doesn't compile, `Qed / (Qed + Admitted + todo)` otherwise, `1.0` when fully done.

## Adding a new problem

Only `initial_program.v` is problem-specific. Copy `evaluator.py` and `config.yaml` from any existing problem unchanged.

Write `initial_program.v` giving the spec with `todo`/`Admitted.` holes:

```coq
Require Import ...
Axiom todo : forall {A : Type}, A.

Definition my_func : <type> := todo.

Theorem my_spec : forall ..., <correctness property>.
Proof. Admitted.
```

Then run using the single-benchmark command above with your `<name>`.

> If your problem needs external Coq libraries, modify `_run_coqc()` in `evaluator.py` to pass `-Q`/`-R` flags.
