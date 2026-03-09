# Formal Verification Benchmark

Co-synthesize Coq implementations and their machine-checked proofs from formal specifications using SkyDiscover.

## Setup

```bash
brew install coq   # needs Rocq/Coq 9.x
```

## Run

```bash
export OPENAI_API_KEY="..."

uv run skydiscover-run \
  benchmarks/formal_verification/coq_proof/all_less_than/initial_program.v \
  benchmarks/formal_verification/coq_proof/all_less_than/evaluator.py \
  -c benchmarks/formal_verification/coq_proof/all_less_than/config.yaml \
  -s best_of_n \
  -i 30
```

## How it works

```
initial_program.v          evaluator.py
┌──────────────────┐       ┌──────────────────────────┐
│ Axiom todo ...   │       │ 1. Run coqc              │
│ Parameter f ...  │       │ 2. Compiles → score =    │
│                  │       │    Qed count             │
│ Lemma spec: ...  │       │ 3. Fails → score = 0    │
│ Proof. Admitted. │──────>│ 4. Return Qed/Admitted/  │
│                  │       │    todo counts + errors  │
└──────────────────┘       └──────────────────────────┘
        │                            │
        │         SkyDiscover        │
        │   LLM fills one todo per   │
        │   step, adds sub-lemmas,   │
        │   proves parent lemma      │
        └────────────────────────────┘
```

**Scoring** (always [0, 1]): `0` if doesn't compile (with coqc error for retry), `1 - 1/(Qed+1)` if compiles with work remaining, `1.0` when no `Admitted.` and no `todo` remain.

**Feedback:** `coqc` errors returned to LLM as artifacts on compile failure.

## Adding a new problem

The evaluator is generic — works for any `.v` file.

1. Create `benchmarks/formal_verification/coq_proof/<name>/`

2. Write `initial_program.v` — one or more `Parameter`s and spec theorems:
   ```coq
   Axiom todo : forall {A : Type}, A.

   Parameter my_func : <type signature>.

   Theorem my_spec : forall ..., <property about my_func>.
   Proof. Admitted.
   ```
   You can have multiple `Parameter`s and multiple theorems. Add any
   `Require Import` statements the problem needs.

3. Copy `evaluator.py` from an existing problem — no changes needed.

4. Write `config.yaml` — copy from existing, adjust `max_iterations` if needed.
   The system prompt is generic and does not need per-problem changes.

**Limitation:** The evaluator runs plain `coqc` with no `-Q`/`-R` flags. If your
problem needs external libraries (Iris, Verdi, etc.), modify `_run_coqc()` in the
evaluator to pass the required flags.

5. Run:
   ```bash
   uv run skydiscover-run \
     benchmarks/formal_verification/coq_proof/<name>/initial_program.v \
     benchmarks/formal_verification/coq_proof/<name>/evaluator.py \
     -c benchmarks/formal_verification/coq_proof/<name>/config.yaml \
     -s best_of_n -i 30
   ```
