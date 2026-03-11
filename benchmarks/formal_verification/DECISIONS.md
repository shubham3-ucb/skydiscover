# Formal Verification Benchmark — Design Decisions

## Setting and Goal

**The problem:** Given a formal specification (a Coq type signature + correctness theorem), automatically synthesize both the implementation and a machine-checked proof of correctness.

**Why it's hard:** The implementation and proof are mutually dependent — the proof structure dictates how the function must be written, and vice versa. A guess-and-check approach doesn't work because partial programs must type-check at every step. The search space is enormous and the feedback signal (does it compile + are proofs complete?) is sparse.

**Our approach:** Treat this as a program synthesis task over Coq `.v` files. SkyDiscover iteratively evolves the file using an LLM, guided by a structured evaluator. Each iteration, the LLM takes one deductive step: fill one `todo` expression and prove its corresponding lemma. The process continues until the file is fully proved.

---

## Design Decisions

### 1. One step per iteration
Each LLM call should take exactly one action: replace one `todo` with a concrete expression and prove its parent lemma, adding sub-lemmas as `Admitted.` for new `todo`s. Enforced via prompt (not mechanically). If the LLM takes a bigger leap and it compiles — fine. If it breaks — score = 0, retry fires.

### 2. Backtracking via population search
No explicit proof tree. AdaEvolve maintains a population of partial solutions at different progress levels across multiple islands. A broken state (score = 0) causes the sampler to pick a different parent from the population. Paradigm breakthrough fires when all islands stagnate, generating fresh high-level strategies.

### 3. Scoring (always [0, 1])
| State | Score |
|---|---|
| Doesn't compile | `0.0` + coqc stderr returned as `error` (triggers retry) |
| Compiles, work remaining | `Qed / (Qed + Admitted + todo)` |
| Fully done | `1.0` |

The ratio `Qed / (Qed + Admitted + todo)` honestly reflects proximity to completion. It can temporarily dip when the LLM decomposes a `todo` into sub-expressions (adding new Admitted/todo) — this is the correct signal. AdaEvolve's population handles dips naturally.

Previous formula `1 - 1/(Qed+1)` was monotonic but blind to remaining work, causing search to stall with no gradient.

**Known limitation:** Score is binary per obligation — proved or not. No partial credit for a proof attempt that gets partway before failing. This causes flat score plateaus when the LLM is stuck on one hard lemma.

### 4. Feedback to LLM
Two channels:
- `metrics["error"]` — coqc stderr on compile failure, shown to LLM on retry
- `artifacts["feedback"]` — natural language: how many Admitted/todo remain, what to do next; injected into AdaEvolve prompt automatically

### 5. Search algorithm: AdaEvolve
Chosen over `best_of_n` because:
- **Population diversity** — multiple partial solutions at different progress levels; no single-path bottleneck
- **Non-monotonic scoring** — islands can independently explore decompositions that temporarily lower the score
- **Paradigm breakthrough** — when stagnating, generates qualitatively new proof strategies
- **Migration** — cross-pollinates good ideas between islands

### 6. Prompt design
Generic for any Coq co-synthesis problem. Key sections:
- Step definition: fill one `todo`, prove its lemma, add sub-lemmas
- Prerequisite ordering: prove lemmas that don't depend on other `Admitted.` ones first
- Proof strategy hints: `remember`, `generalize dependent`, induction on evidence, helper lemmas — standard Coq advice, no problem-specific content

### 7. Initial program shape
`Definition f := todo.` + `Theorem spec ... Proof. Admitted.` Any number of functions and theorems. Pre-proved helper lemmas in the initial file are fine — they raise the starting score but 1.0 is only reached when all `Admitted.` and `todo` are gone.

### 8. Typed holes
`Axiom todo : forall {A : Type}, A.` — a Coq idiom for a typed hole usable at any type. The evaluator excludes this declaration itself from the `todo` count.

### 9. LLM generates everything
Implementation choices, sub-lemma statements, proof tactics — all by the LLM. The system provides no hints about proof structure or algorithm choice.

---

## Components

| File | Role | Problem-specific? |
|---|---|---|
| `initial_program.v` | Formal spec + holes for the LLM to fill | **Yes** — one per problem |
| `evaluator.py` | Compile, score, return NL feedback | **No** — generic for any `.v` file |
| `config.yaml` | Search params + system prompt | **No** — prompt is generic; only `max_iterations` may vary |

---

## Open Questions

- **Plateau problem**: when the LLM is stuck on one hard proof, score is flat for many iterations and search has no gradient signal. Directions: coqc goal-state feedback, partial proof credit, or structured stagnation recovery.
- **Proof dependency**: the LLM must infer which `Admitted.` lemmas depend on others from reading the code. Explicit dependency information in feedback could help prioritize.
- **Iteration budget**: harder problems (e.g. `regex_matcher`) saturate near 0.85–0.93 in 50 iterations. The LLM may need a qualitatively different strategy (different tactic, different decomposition) rather than more of the same.
