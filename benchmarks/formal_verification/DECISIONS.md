# Formal Verification Benchmark — Design Decisions

## Setting and Goal

**Problem:** Given a formal specification (Coq type signature + correctness theorem), automatically synthesize both the implementation and a machine-checked proof of correctness.

**Why it's hard:** Implementation and proof are mutually dependent — the proof structure dictates how the function must be written, and vice versa. Every intermediate state must type-check; the search space is enormous; feedback is sparse (compile or not, proved or not).

**Approach:** SkyDiscover evolves a Coq `.v` file iteratively. Each iteration, the LLM takes one deductive step — fill one `todo`, prove its lemma — until the file is complete.

---

## Design Decisions

### 1. One step per iteration
One action per LLM call: replace one `todo` with a concrete expression, prove its parent lemma to `Qed.`, add sub-lemmas as `Admitted.` for any new `todo`s introduced. Enforced via prompt. If the LLM takes a bigger leap and it compiles — fine. If it breaks — score = 0, retry fires.

### 2. Backtracking via population search
No explicit proof tree. AdaEvolve maintains a population of partial solutions across multiple islands. A broken state (score = 0) causes the sampler to pick a different parent. Paradigm breakthrough fires when all islands stagnate, generating qualitatively new proof strategies.

### 3. Scoring
| State | Score |
|---|---|
| Doesn't compile | `0.0` + coqc stderr returned as `error` (triggers retry) |
| Compiles, work remaining | `Qed / (Qed + Admitted + todo)` |
| Fully done | `1.0` |

Score honestly reflects proximity to completion. Temporary dips when the LLM decomposes a `todo` into sub-expressions are handled naturally by AdaEvolve's population diversity.

**Known limitation:** No partial credit for a partially-written proof that fails to compile. Causes flat plateaus when stuck on one hard lemma.

### 4. Feedback to LLM
- `metrics["error"]` — coqc stderr on compile failure, shown on retry
- `artifacts["feedback"]` — natural language count of remaining `Admitted`/`todo` and what to do next; injected into AdaEvolve prompt automatically

### 5. Search: AdaEvolve
Chosen over `best_of_n` for population diversity, tolerance of non-monotonic scores, paradigm breakthrough, and cross-island migration. All critical for a task where individual steps can temporarily lower the score.

### 6. Prompt
Generic for any Coq co-synthesis problem: step definition, prerequisite ordering (prove independent lemmas first), standard Coq tactic hints (`remember`, `generalize dependent`, induction on evidence). No problem-specific content.

### 7. Initial program shape
`Definition f := todo.` + `Theorem spec ... Proof. Admitted.` Pre-proved helper lemmas are fine — they raise the starting score, but `1.0` is only reached when all `Admitted.` and `todo` are eliminated.

### 8. Typed holes
`Axiom todo : forall {A : Type}, A.` — a Coq idiom for a typed hole at any type. The evaluator excludes this declaration itself from the `todo` count.

### 9. LLM generates everything
Implementation choices, sub-lemma statements, proof tactics — all by the LLM. The system provides no hints about proof structure or algorithm.

---

## Components

| File | Role | Problem-specific? |
|---|---|---|
| `initial_program.v` | Formal spec + holes | **Yes** — one per problem |
| `evaluator.py` | Compile, score, NL feedback | **No** |
| `config.yaml` | Search params + system prompt | **No** — only `max_iterations` may vary |

---

## Open Questions

- **Plateau**: stuck on one hard proof → score flat for many iterations, no gradient. Directions: coqc goal-state feedback, partial proof credit, structured stagnation recovery.
- **Dependency inference**: LLM must read code to know which `Admitted.` lemmas block others. Explicit dependency info in feedback could help.
- **Budget**: harder problems (`regex_matcher`) saturate near 0.85–0.93 in 50 iterations — more iterations of the same strategy may not help; a qualitatively different decomposition is needed.
