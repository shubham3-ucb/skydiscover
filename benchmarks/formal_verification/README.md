# Formal Verification Benchmark

## What this is

This benchmark asks SkyDiscover to perform **co-synthesis**: given only a formal specification (Coq type signature + correctness theorem), build the implementation and its machine-checked proof together, step by step, until `coqc` accepts the entire file with no holes. Every intermediate state must type-check — there is no guess-and-check.

## Problems

| Problem | Difficulty | Description | AdaEvolve | Iterative Baseline |
|---|---|---|---|---|
| `all_less_than` | Easy | Check all list elements are below a bound | ✅ iter 5 | ✅ iter 3 |
| `insertion_sort` | Medium | Implement and verify a sorting algorithm | ✅ iter 15 | ✅ iter 2 |
| `pigeonhole` | Hard (5★) | Define `repeats` and prove the pigeonhole principle | ✅ iter 5 | ✅ iter 3 |
| `regex_matcher` | Hard (2–4★) | Verified regex matcher via Brzozowski derivatives | ✅ iter 15 | ✅ iter 8 |
| `bst_verification` | Hard | Implement and verify a binary search tree | ✅ iter 25 | ✅ iter 9 |
| `trie_adt` | Very hard | Define `is_trie` invariant, prove 10 ADT theorems | ✅ iter 25 | ✅ iter 28 |
| `strong_pumping` | Very hard (5★) | Prove the strong pumping lemma | ✅ iter 10 | ❌ 0.80 |
| `type_safe_eval` | Medium | Verified type-safe expression evaluator (12 theorems) | 🔄 in progress | — |
| `binomial_queue` | Very hard (56★) | Invent `priqueue_elems`, prove 20 ADT theorems | ❌ 0.76 | ❌ 0.76 |
| `redblack_tree` | Very hard (32★) | Prove BST, lookup, and red-black invariants | ❌ 0.9655 | ❌ 0.9655 |

See [`coq_proof/PROBLEMS.md`](coq_proof/PROBLEMS.md) for detailed descriptions and SF source links.

## Setup

```bash
brew install coq        # Rocq/Coq 9.x
export GEMINI_API_KEY="..."   # or OPENAI_API_KEY for GPT models
cd skydiscover/
source .venv/bin/activate
```

## Run

All benchmarks in parallel:
```bash
bash benchmarks/formal_verification/coq_proof/run_all.sh
```

Single benchmark:
```bash
python -m skydiscover.cli \
  benchmarks/formal_verification/coq_proof/<name>/initial_program.v \
  benchmarks/formal_verification/coq_proof/<name>/evaluator.py \
  -c benchmarks/formal_verification/coq_proof/<name>/config.yaml \
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

Score is always in [0, 1]: `0.0` if it doesn't compile (0.5× partial credit if some Qed), `Qed / (Qed + admitted_weight + todo + axioms)` if it compiles, `1.0` when fully done. Admitted proofs where the LLM used `admit.` for sub-goals count as 0.5 instead of 1.0 in the denominator, rewarding incremental proof progress.

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
