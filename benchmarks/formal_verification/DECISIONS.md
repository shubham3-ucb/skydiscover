# Formal Verification Benchmark — Design Decisions

## Setting and Goal

**Problem:** Given a formal specification (Coq type signature + correctness theorem), automatically synthesize both the implementation and a machine-checked proof of correctness.

**Why it's hard:** Implementation and proof are mutually dependent — the proof structure dictates how the function must be written, and vice versa. Every intermediate state must type-check; the search space is enormous; the feedback signal is sparse (compile or not, proved or not).

**Approach:** SkyDiscover evolves a Coq `.v` file iteratively. Each iteration the LLM takes one deductive step — fill one `todo`, prove its lemma — until the file compiles fully with no holes.

**Results:**

| Problem | Difficulty | Solved | Iter | Score |
|---|---|---|---|---|
| all_less_than | Easy | Yes | 1 | 1.0 |
| insertion_sort | Medium | Yes | 14 | 1.0 |
| regex_matcher | Hard | Yes | 12 | 1.0 |
| pigeonhole | Hard | Yes | 5 | 1.0 |
| bst_verification | Hard | Yes | 23 | 1.0 |
| strong_pumping | 5-star | Running | — | 0.83 best prev |
| trie_adt | Hard (ADT) | Yes | 24 | 1.0 |
| binomial_queue | Very hard (ADT) | Running | — | — |

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
No explicit proof tree. AdaEvolve maintains a population of partial solutions at different progress levels. A broken state (score = 0) causes the sampler to pick a different parent. When all islands stagnate, paradigm breakthrough generates a qualitatively new high-level strategy.

### 3. Scoring
| State | Score |
|---|---|
| Doesn't compile | `0.0` + coqc stderr returned as `error` (triggers retry) |
| Compiles, work remaining | `Qed / (Qed + Admitted + todo)` |
| Fully done | `1.0` |

Score can temporarily dip when the LLM decomposes a `todo` into sub-expressions (adding new `Admitted`/`todo`). AdaEvolve handles this — a monotonic search like `best_of_n` would reject valid progress.

**Known limitation:** No partial credit for a proof attempt that fails to compile. Causes flat score plateaus when the LLM is stuck on one hard lemma.

### 4. Feedback to LLM
- `metrics["error"]` — coqc stderr on compile failure, shown on retry
- `artifacts["feedback"]` — natural language count of remaining `Admitted`/`todo` and what to do next

### 5. Search
AdaEvolve (multi-island population search). Non-monotonic scoring requires population diversity — single-path search rejects valid decomposition steps.

### 6. Prompt
Fully generic — no problem-specific content. Covers: the one-step action definition, prerequisite ordering, standard Coq tactic hints (`remember`, `generalize dependent`, induction on evidence). Anti-gaming rules prevent closing proofs with `exact todo`.

### 7. Initial program shape
`Definition f := todo.` + `Theorem spec ... Proof. Admitted.` Pre-proved helper lemmas are fine — they raise the starting score, but `1.0` requires all `Admitted.` and `todo` gone.

### 8. Typed holes
`Axiom todo : forall {A : Type}, A.` — a Coq idiom for a typed hole at any type. The evaluator excludes this declaration from the `todo` count.

### 9. LLM owns all synthesis decisions
Implementation algorithm, sub-lemma statements, proof tactics — all by the LLM. The system provides no hints about proof structure or algorithm.

---

## Key Findings

### Tactic timeout trap (strong_pumping)
The LLM generated a **mathematically correct** full proof of the 5-star Strong Pumping Lemma (218 lines, 0 Admitted). But it scored 0.0 because `coqc` timed out — tactics like `do 3 eexists` and `repeat rewrite app_assoc` cause infinite Coq unification loops. Manual fix: replace with explicit witnesses and targeted single rewrites. The proof then compiles in <1s.

**Root cause:** The evaluator's 120s timeout killed correct proofs silently. The LLM received no guidance about *why* it failed, so it couldn't self-correct.

**Fix applied (general):** (1) Evaluator timeout raised to 300s. (2) On timeout, evaluator returns actionable guidance about slow tactics. (3) Prompt includes general Coq tactic performance rules (no `eexists`, no `repeat rewrite`). All changes are domain-general — not problem-specific.

---

## Open Questions

- **Plateau problem:** Stuck on one hard lemma → score flat, no gradient. Directions: expose Coq goal state as feedback, partial credit for proof subgoals.
- **Dependency inference:** LLM must read code to know which `Admitted.` lemmas block others. Explicit dependency graph in feedback could help.
- **Scoring granularity:** Score is binary per obligation (proved or not). Finer signal (e.g. remaining subgoals) could help escape plateaus.
