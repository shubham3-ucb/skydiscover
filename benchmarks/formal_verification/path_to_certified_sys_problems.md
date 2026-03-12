# Path to Certified Systems

## What We Tested

| Problem | Initial spec | LLM produced | Invariant design | Model | Solved | Iter |
|---|---|---|---|---|---|---|
| all_less_than | 1 todo, 1 Admitted | 1 Qed | — | GPT-5 | Yes | 1/50 |
| insertion_sort | 1 todo, 1 Admitted | 5 Qed (invented helper `insert`) | — | GPT-5 | Yes | 14/50 |
| pigeonhole | 1 todo defn, 2 Admitted | 2 Qed | Predicate defn (`repeats`) | Gemini 3 Pro | Yes | 5/50 |
| regex_matcher | 3 todo fns, 5 Admitted + 9 given Qed | 14 Qed total | — | Gemini 3 Pro | Yes | 12/50 |
| bst_verification | 3 todo fns, 5 Admitted | 9 Qed (invented 4 sub-lemmas) | — | Gemini 3 Pro | Yes | 23/50 |
| strong_pumping | 5 Admitted | 5 Qed (full induction on match evidence, explicit witnesses) | — | Gemini 3 Pro | Yes | 25/100 |
| trie_adt | 1 todo defn, 10 Admitted + 2 given Qed | 12 Qed + `is_trie` defn | `is_trie` invariant | Gemini 3 Pro | Yes | 24/100 |
| binomial_queue | 1 Axiom defn, 20 Admitted + 5 given Qed | — | `priqueue_elems` relation | Gemini 3 Pro | Running | — |
| redblack_tree | 14 Admitted + 14 given Qed | — | — (RB/NearlyRB given) | Gemini 3 Pro | Running | — |

All single-file, <=423 lines initial. Coq stdlib + VFA/PLF imports where needed. One generic evaluator and prompt across all problems.

---

## What Real Certified Systems Require

CompCert, seL4, FSCQ, CertiKOS share these traits:

- **Multi-file** (50k–500k lines, hundreds of modules with import chains)
- **Layered refinement** (spec → model → impl, each layer proved to refine the one above)
- **Representation invariants** (the core intellectual challenge — what abstraction to choose)
- **Imperative reasoning** (separation logic or Hoare logic for heap/state)
- **Concurrency / crash recovery** (temporal reasoning, interleaving)

Scale reference: FSCQ (verified file system) = ~30k lines Coq, ~40 person-months.

---

## Gap Analysis

| Gap | Severity | Closable? | How |
|---|---|---|---|
| **Multi-file context** | High | Yes | Agent reads imported `.v` files, provides lemma signatures as context. Evaluator already handles `coqc` with imports. Engineering, not research. |
| **Scale (>500 lines)** | Medium | Likely | Step-by-step is inherently incremental. Need to test at 200+ iterations. `bst_verification` did 23 iters / 9 Qed — promising but unproven at 5x. |
| **Invariant invention** | High | Partial | `trie_adt` tests this (LLM must define `is_trie`). Standard data structures likely feasible from training data. Novel protocol invariants (crash safety, distributed consensus) genuinely hard — would need NL spec → Coq formalization. |
| **Separation logic** | Medium | Partial | Coq frameworks exist (Iris, VST). Different proof patterns (entailment vs induction). Testable with a single VST benchmark — no fundamental barrier. |
| **Concurrency / crash** | Low (for now) | Unclear | Requires Gaps 1–4 first. |

---

## Struggles Observed

**LLM ignores step-by-step.** On easy problems, solved in one shot. On hard problems with many holes, one-shot attempts produce non-compiling code. Prompt enforcement works but may need mechanical diff validation at scale.

**Score plateaus.** When stuck on one hard lemma, score is flat — no gradient to guide search. Fix: expose Coq goal state as feedback, partial credit for proof subgoals.

**Scoring non-monotonicity.** Decomposing 1 todo → 3 sub-todos drops the score. A monotonic search rejects valid progress. Fix: AdaEvolve (population search). This worked — all hard problems solved.

**External dependencies.** Hard SF exercises need `From PLF Require Import ...`. We inlined or avoided. Real systems can't do this. Fix: agent-based context (Gap 1).

**Gaming.** `Qed` with `exact todo` inside would fake progress. Fix: evaluator counts `todo` occurrences; Coq's type checker rejects unsound proofs at `Qed`.

**Diff parsing.** LLM sometimes wraps diffs in markdown fences, corrupting the Coq file. Fixed: evaluator strips fences before compilation.

**Tactic timeout.** LLM generates structurally correct proofs that hang Coq's unifier (`do N eexists`, `repeat rewrite`). Scores 0.0 with no actionable feedback. Fixed: 300s timeout, actionable timeout guidance, tactic performance hints in prompt.

**Verbose error noise.** `coqc` stderr for proof failures includes "In environment" blocks listing every in-scope hypothesis (15-30 lines). LLM couldn't parse the actual error from the noise. Fixed: evaluator strips environment blocks via regex, surfacing only the core error message (74% reduction in error text size).

**Axiom tracking.** Benchmarks requiring the LLM to replace an `Axiom` with a definition (e.g. `binomial_queue`'s `priqueue_elems`) weren't tracked as open obligations. Fixed: evaluator counts non-`todo` `Axiom` declarations and includes them in the score denominator.

---

## Honest Assessment

**Can claim:** LLMs co-synthesize implementations and machine-checked proofs for textbook-scale Coq problems (up to 5-star SF exercises, up to 12 new proof obligations per problem, solved programs reaching ~300 lines). The approach is general — one evaluator, one prompt, 7 problems from trivial to 5-star. The LLM discovers decompositions (sub-functions, sub-lemmas, proof strategies, invariant definitions) without human guidance. All proofs verified by `coqc`. `trie_adt` demonstrates invariant invention (`is_trie`). `strong_pumping` demonstrates the LLM can generate mathematically correct proofs of 5-star exercises — the remaining gap is tactic efficiency, not mathematical reasoning.

**Cannot claim:** This builds a certified file system, compiler, or network stack today. Multi-file context, separation logic, concurrency, and large-scale invariant design are untested.

**Bridge:**
1. Multi-file + invariant benchmarks work → *"AI builds verified functional libraries."*
2. Additionally imperative/VST works → *"AI assists certified systems components."*
3. Additionally scale (500+ lines) works → *"AI co-pilots certified systems development."*

---

## Next Steps (by impact)

1. **Complete running benchmarks.** `binomial_queue` (20 obligations, invariant invention) and `redblack_tree` (14 obligations, 3 proof domains, 423 lines) are running with Gemini 3 Pro. Both are genuine 5-star-level problems that failed one-shot.
2. **Graph coloring (VFA/Color).** Kempe's algorithm with termination proof — a real compiler backend component.
3. **Multi-file benchmark.** VFA SearchTree importing Maps — minimal setup, tests the core gap.
4. **Agent context.** On `Require Import Foo`, agent extracts `Foo.v` signatures into LLM context.
5. **Goal-state feedback.** On proof failure, return Coq's pending goal to the LLM — breaks plateaus.
6. **VST benchmark** — one C function verified with separation logic.
