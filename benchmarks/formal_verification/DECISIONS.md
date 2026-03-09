# Formal Verification Benchmark — Design Decisions

## Task

Co-synthesize a Coq **implementation** and its **machine-checked proof** from a formal specification, step by step.

Applies to any domain with formal specs: protocols, crypto, compilers, data structures.

## Decisions

### 1. One action per iteration
Instruct via prompt, not enforced mechanically. If LLM takes a bigger leap and it compiles — fine. If it breaks — score = 0, retry mechanism kicks in, and if still broken the sampler picks an earlier state.

### 2. Backtracking = population search
No explicit tree. SkyDiscover's database keeps all states with scores. Broken state (score 0) → sampler picks highest-scoring prior state. Implicit backtracking.

### 3. Scoring (always [0, 1])
- **Doesn't compile:** `0.0` with `error = <coqc stderr>` (triggers SkyDiscover's retry mechanism)
- **Compiles, not done:** `1 - 1/(qed + 1)` — monotonically increasing with each proved lemma, always < 1.0
- **Done** (`Admitted == 0 AND todo == 0 AND compiles`): `1.0`

Why `1 - 1/(qed+1)` instead of `qed/(qed+admitted+todo)`: the ratio is non-monotonic — correct decomposition adds new `Admitted` sub-lemmas, temporarily lowering the ratio. With best_of_n (which always picks the highest-scoring parent), a dip means the search gets stuck at the pre-decomposition state and can never advance. `1 - 1/(qed+1)` depends only on qed count, which only increases, so the score is monotonic and the search always moves forward. No hardcoded constants — works for any problem size.

### 4. Initial program shape
Not prescribed. Evaluator and prompt work on any `.v` file. The `all_less_than` example starts from `Parameter` + one spec theorem, but partial implementations also work.

### 5. Typed holes
`Axiom todo : forall {A : Type}, A.` — standard Coq typed hole. Works for any type.

### 6. LLM generates everything
Full `.v` file (or diff) each iteration: implementation actions, sub-lemma statements, proofs. No auto-generation by the system.

### 7. No EVOLVE-BLOCK
Entire `.v` file is the evolving artifact. Implementation and proofs change together — no fixed/unfixed regions.

## Components

| File | Role | Problem-specific? |
|------|------|-------------------|
| `initial_program.v` | Starting state | Yes (one per problem) |
| `evaluator.py` | Compile + count Qed/Admitted/todo | No (generic) |
| `config.yaml` | Search params + system prompt | Prompt is generic; model/iteration params may vary |

## Open Questions
- Best search strategy? Starting with `best_of_n`.
- Iteration count for non-toy problems?
