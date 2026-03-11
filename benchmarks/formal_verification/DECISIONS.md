# Formal Verification Benchmark — Design Decisions

## Setting and Goal

**Problem:** Given a formal specification (Coq type signature + correctness theorem), automatically synthesize both the implementation and a machine-checked proof of correctness.

**Why it's hard:** Implementation and proof are mutually dependent — the proof structure dictates how the function must be written, and vice versa. Every intermediate state must type-check; the search space is enormous; the feedback signal is sparse (compile or not, proved or not).

**Approach:** SkyDiscover evolves a Coq `.v` file iteratively. Each iteration the LLM takes one deductive step — fill one `todo`, prove its lemma — until the file compiles fully with no holes.

**Results so far:**
- `all_less_than` (easy): solved at iteration 1, score 1.0
- `insertion_sort` (medium): solved at iteration 14, score 1.0
- `regex_matcher` (hard): 13/14 proofs in 30 iterations, score 0.929

---

## Components

| File | Role | Problem-specific? |
|---|---|---|
| `initial_program.v` | Formal spec with `todo`/`Admitted.` holes for the LLM to fill | **Yes** — one per problem |
| `evaluator.py` | Runs `coqc`, counts Qed/Admitted/todo, scores, returns NL feedback | **No** — generic for any `.v` file |
| `config.yaml` | Search config + system prompt | **No** — only `max_iterations` may vary |

---

## Design Decisions

### 1. One step per iteration
One action per LLM call: replace one `todo` with a concrete expression, prove its parent lemma to `Qed.`, add sub-lemmas as `Admitted.` for any new `todo`s introduced. Enforced via prompt only — not mechanically. If the LLM takes a bigger leap and it compiles, fine. If it breaks, score = 0 and retry fires.

### 2. Backtracking
No explicit proof tree. The search maintains a population of partial solutions at different progress levels. A broken state (score = 0) causes the sampler to pick a different parent. When all islands stagnate, paradigm breakthrough generates a qualitatively new high-level strategy.

### 3. Scoring
| State | Score |
|---|---|
| Doesn't compile | `0.0` + coqc stderr returned as `error` (triggers retry) |
| Compiles, work remaining | `Qed / (Qed + Admitted + todo)` |
| Fully done | `1.0` |

`Qed / (Qed + Admitted + todo)` honestly reflects proximity to completion. It can temporarily dip when the LLM decomposes a `todo` into sub-expressions (adding new `Admitted`/`todo`) — this is the correct signal.

**Known limitation:** No partial credit for a proof attempt that fails to compile. Causes flat score plateaus when the LLM is stuck on one hard lemma — observed in `regex_matcher` on `star_ne` and `derive_corr`.

### 4. Feedback to LLM
- `metrics["error"]` — coqc stderr on compile failure, shown on retry
- `artifacts["feedback"]` — natural language count of remaining `Admitted`/`todo` and what to do next; injected into the prompt automatically

### 5. Search
AdaEvolve (multi-island population search). Key reason: individual steps can temporarily lower the score when the LLM adds new sub-lemmas — a monotonic search like `best_of_n` would reject these valid progress states.

### 6. Prompt
Fully generic — no problem-specific content. Covers: the one-step action definition, prerequisite ordering (prove independent `Admitted.` lemmas before dependent ones), standard Coq tactic hints (`remember`, `generalize dependent`, induction on evidence). Anti-gaming rules prevent closing proofs with `exact todo` or trivial axiom applications.

### 7. Initial program shape
`Definition f := todo.` + `Theorem spec ... Proof. Admitted.` Pre-proved helper lemmas in the initial file are fine — they raise the starting score, but `1.0` is only reached when all `Admitted.` and `todo` are gone.

### 8. Typed holes
`Axiom todo : forall {A : Type}, A.` — a Coq idiom for a typed hole at any type. The evaluator excludes this declaration itself from the `todo` count.

### 9. LLM owns all synthesis decisions
Implementation algorithm, sub-lemma statements, proof tactics — all by the LLM. The system provides no hints about proof structure or algorithm. This is the point: can LLMs discover correct decompositions on their own?

---

## Open Questions

- **Plateau**: stuck on one hard lemma → score flat, no gradient. Directions: expose coqc goal state as feedback, add partial proof credit, structured stagnation recovery.
- **Dependency inference**: LLM must read code to know which `Admitted.` lemmas block others. Explicit dependency graph in feedback could help prioritize.
- **Iteration budget**: `regex_matcher` saturates near 0.93 in 50 iterations. The missing proof (`star_ne`) requires a non-obvious induction strategy — more iterations of the same approach won't help; a different decomposition is needed.
- **Scoring granularity**: score is binary per obligation (proved or not). A finer signal — e.g. how many subgoals remain in an open proof — could help escape plateaus without full credit.
