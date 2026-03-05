# Formal Verification Benchmarks

Use SkyDiscover to evolve Coq proofs. Given proof obligations with `Admitted.` placeholders, the LLM writes proof tactics until `coqc` accepts them.

## Setup

```bash
brew install coq   # needs Rocq/Coq 9.x
```

## Run the example

```bash
export OPENAI_API_KEY="..."

uv run skydiscover-run \
  benchmarks/formal_verification/coq_proof/all_less_than/initial_program.v \
  benchmarks/formal_verification/coq_proof/all_less_than/evaluator.py \
  -c benchmarks/formal_verification/coq_proof/all_less_than/config.yaml \
  -s best_of_n \
  -i 10
```

## How it works

```
initial_program.v          evaluator.py
┌──────────────────┐       ┌──────────────────────────┐
│ Implementation   │       │ 1. Run coqc on file       │
│ (fixed)          │       │ 2. If compiles:           │
│                  │       │    score = Qed / total    │
│ Lemma foo: ...   │       │ 3. If fails:              │
│ Proof. Admitted. │──────>│    test each proof alone  │
│                  │       │    (others = Admitted)    │
│ Lemma bar: ...   │       │ 4. Return partial score   │
│ Proof. Admitted. │       │    + coqc error feedback  │
└──────────────────┘       └──────────────────────────┘
        │                            │
        │         SkyDiscover        │
        │   LLM replaces Admitted.   │
        │   with real proof tactics  │
        │   ending in Qed.           │
        └────────────────────────────┘
```

**Scoring**: `proved_count / total` (0.0 to 1.0). Each proof tested independently so partial progress gets partial credit.

**Feedback**: `coqc` error messages are passed back to the LLM as artifacts, so it knows exactly which tactic failed and why.

## Adding a new problem

The evaluator is generic — it works for any `.v` file. It handles:
- `Lemma`, `Theorem`, `Proposition`, `Corollary`, `Fact`, `Remark`
- `Qed.`, `Admitted.`, `Defined.` terminators
- Comments containing `Qed.`/`Admitted.` (correctly ignored)

### Steps

1. Create `benchmarks/formal_verification/coq_proof/<name>/`

2. Write `initial_program.v` — fixed code + proof obligations with `Admitted.`:
   ```coq
   (* your fixed definitions *)
   Definition my_func ... := ...

   (* EVOLVE-BLOCK-START *)
   Theorem my_theorem: forall ..., ...
   Proof. Admitted.

   Lemma helper: forall ..., ...
   Proof. Admitted.
   (* EVOLVE-BLOCK-END *)
   ```

   Keep definitions **outside** the EVOLVE-BLOCK (they shouldn't change).
   Put proof obligations **inside** the EVOLVE-BLOCK.

3. Copy `evaluator.py` from the existing example — no changes needed.

4. Write `config.yaml`:
   ```yaml
   language: coq
   file_suffix: ".v"
   diff_based_generation: true
   max_iterations: 20

   llm:
     models:
       - name: "gpt-5"
         weight: 1.0
     timeout: 600
     retries: 2

   evaluator:
     timeout: 120
     cascade_evaluation: false

   prompt:
     system_message: |
       You are an expert Coq proof engineer.
       <describe the problem, key tactics, relevant library lemmas>
   ```

   The only thing that changes per-problem is the `system_message`.

5. Run:
   ```bash
   uv run skydiscover-run \
     benchmarks/formal_verification/coq_proof/<name>/initial_program.v \
     benchmarks/formal_verification/coq_proof/<name>/evaluator.py \
     -c benchmarks/formal_verification/coq_proof/<name>/config.yaml \
     -s best_of_n -i 20
   ```

### Limitations

- **Stdlib imports only**: The evaluator runs `coqc` from the file's directory. If your problem needs custom libraries, you'll need to modify `_run_coqc()` to pass `-Q`/`-R` flags.
- **Statement integrity**: The evaluator does not verify that the LLM preserved lemma statements unchanged. The system prompt instructs it not to, and the fixed implementation outside the EVOLVE-BLOCK constrains the types. For stronger guarantees, add statement checks to the evaluator.
