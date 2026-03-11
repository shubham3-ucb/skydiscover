# Formal Verification Benchmark

## What this is

Writing software that is **provably correct** requires two things: an implementation, and a machine-checked proof that the implementation satisfies its specification. In Coq, this means writing both a function body and a theorem proof simultaneously — each constrains the other.

This benchmark asks SkyDiscover to perform **co-synthesis**: given only a formal specification (function type + correctness theorem), iteratively build the implementation and its proof together, step by step, until Coq's type checker accepts the entire file with no holes.

This is harder than ordinary code generation because the LLM cannot guess-and-check — every intermediate state must type-check, and the proof must be logically sound. It is a concrete instance of a general problem: building verified software from a spec.

## Benchmark problems

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
```

## Run all benchmarks

```bash
bash benchmarks/formal_verification/coq_proof/run_all.sh
```

Or a single benchmark:

```bash
source .venv/bin/activate
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
│ Theorem spec : ...         │          │ 4. Return score + NL feedback  │
│ Proof. Admitted.           │          └────────────────────────────────┘
└────────────────────────────┘                        │
                 ▲                                    │
                 │           AdaEvolve                │
                 │  (multi-island population search)  │
                 └────────────────────────────────────┘
                         LLM takes ONE step per iteration:
                         • Fill one todo with a concrete expression
                         • Add sub-lemmas as Admitted.
                         • Prove the parent lemma → Qed.
```

**Scoring** (always in [0, 1]):
- `0.0` — doesn't compile (coqc error returned to LLM for retry)
- `Qed / (Qed + Admitted + todo)` — compiles, work remaining
- `1.0` — fully done: no `Admitted.`, no `todo`

**Search**: AdaEvolve maintains a population of partial solutions across multiple islands. Temporary score dips (from adding new sub-lemmas) are handled by population diversity. Paradigm breakthrough fires when all islands stagnate.

## Adding a new problem

The evaluator and prompt are **fully generic** — no changes needed for new problems. Only `initial_program.v` is problem-specific.

1. Create `benchmarks/formal_verification/coq_proof/<name>/`

2. Write `initial_program.v` — give the spec, leave the implementation as `todo` and the proof as `Admitted.`:
   ```coq
   Require Import ...
   Axiom todo : forall {A : Type}, A.

   Definition my_func : <type> := todo.

   Theorem my_spec : forall ..., <correctness property>.
   Proof. Admitted.
   ```

3. Copy `evaluator.py` and `config.yaml` from any existing problem. Adjust `max_iterations` in the config if needed.

4. Run:
   ```bash
   skydiscover-run \
     benchmarks/formal_verification/coq_proof/<name>/initial_program.v \
     benchmarks/formal_verification/coq_proof/<name>/evaluator.py \
     --config benchmarks/formal_verification/coq_proof/<name>/config.yaml \
     -o benchmarks/formal_verification/coq_proof/<name>/outputs
   ```

**Note:** The evaluator runs plain `coqc`. If your problem needs external libraries (Iris, Verdi, etc.), modify `_run_coqc()` in `evaluator.py` to pass the required `-Q`/`-R` flags.
