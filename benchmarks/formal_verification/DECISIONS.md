# Formal Verification Benchmark — Design Decisions

## Setting and Goal

**Problem:** Given a formal specification (Coq type signature + correctness theorem), automatically synthesize both the implementation and a machine-checked proof of correctness.

**Approach:** SkyDiscover evolves a Coq `.v` file iteratively. Each iteration the LLM takes one deductive step — fill one `todo`, prove one lemma — until the file compiles fully with no holes.

**Results (AdaEvolve · Gemini 3 Pro Preview):**

| Problem | Difficulty | Solved | Ada first solved | Iterative first solved | Best score |
|---|---|---|---|---|---|
| all_less_than | Easy | ✅ | iter 5 | iter 3 | 1.0 |
| insertion_sort | Medium | ✅ | iter 15 | iter 2 | 1.0 |
| pigeonhole | Hard | ✅ | iter 5 | iter 3 | 1.0 |
| regex_matcher | Hard | ✅ | iter 15 | iter 8 | 1.0 |
| bst_verification | Hard | ✅ | iter 25 | iter 9 | 1.0 |
| trie_adt | Very hard | ✅ | iter 25 | iter 28 | 1.0 |
| strong_pumping | 5★ | ✅ Ada only | iter 10 | ❌ 0.80 (100 iters) | 1.0 |
| type_safe_eval | Medium | 🔄 in progress | — | — | 0.786 (iter 40/50) |
| binomial_queue | Very hard | ❌ | ❌ 0.76 (200 iters) | ❌ 0.76 (200 iters) | 0.76 |
| redblack_tree | Very hard | ❌ | ❌ 0.9655 (200 iters) | ❌ 0.9655 (200 iters) | 0.9655 |

v5 reruns (anti-inflation guard + prompt fixes) in progress for binomial_queue and redblack_tree.

---

## Components

| File | Role | Problem-specific? |
|---|---|---|
| `initial_program.v` | Formal spec with `todo`/`Admitted.` holes | **Yes** — one per problem |
| `evaluator.py` | Runs `coqc`, counts Qed/Admitted/todo, scores, returns feedback | **No** — generic for any `.v` file |
| `config.yaml` | Search config + system prompt | **No** — only `max_iterations` may vary |

---

## Design Decisions

### 1. One step per iteration
One action per LLM call: replace one `todo`, prove one lemma, or define one `Axiom`. If the LLM takes a bigger leap and it compiles, fine. If it breaks, score drops and retry fires.

### 2. Backtracking
No explicit proof tree. AdaEvolve maintains a population of partial solutions. A broken state causes the sampler to pick a different parent. Paradigm breakthrough generates qualitatively new strategies when all islands stagnate.

### 3. Scoring
| State | Score |
|---|---|
| Compiles, done | `1.0` |
| Compiles, work remaining | `qed / (qed + admitted_weight + todo + axioms)` |
| Doesn't compile, has Qed work | `0.5 * above ratio` |
| Doesn't compile, no Qed | `0.0` |

`admitted_weight`: each `Admitted` proof counts as 1.0 open obligation, **except** when the LLM used `admit.` for sub-goals (Coq reports "No more goals, but gave up"), it counts as 0.5 — but only if the LLM has NOT inflated the total obligation count by adding new Admitted stubs. If `qed + admitted > _INITIAL_PROOF_OBLS`, all Admitted get full 1.0 weight (anti-inflation guard — see Key Findings).

The denominator is floored at `_INITIAL_PROOF_OBLS` (Qed + Admitted count in `initial_program.v`) to prevent trivial spec replacement.

### 4. Feedback to LLM
- `metrics["error"]` — coqc stderr on compile failure (environment blocks stripped)
- `artifacts["feedback"]` — remaining obligations count + Coq goal states for each `Admitted` proof (via `Show.` injection) + recently proved proof bodies (patterns to reuse)

### 5. Incremental proof via admit.
The prompt teaches the LLM to use `admit.` (lowercase) for hard sub-goals within a proof. This keeps the file compiling (Coq accepts `admit.` + `Admitted.`) and lets the search retain partial proof progress. The evaluator detects `admit.` usage via the "gave up" marker in Coq's `Show.` output and rewards it with reduced obligation weight (0.5 instead of 1.0).

### 6. Proof-pattern feedback
When a theorem transitions from `Admitted` to `Qed`, the evaluator includes its proof body (truncated to 10 lines) in feedback. This helps the LLM reuse successful tactics on structurally similar remaining proofs.

### 7. Search
AdaEvolve (multi-island population search). Non-monotonic scoring requires population diversity.

### 8. Prompt
Fully generic — no problem-specific content. Covers: one-step rule, prerequisite ordering, Coq tactic hints, `admit.` usage, anti-gaming rules, proof patterns (conjunctive induction, generalize before induction, function case analysis).

---

## Key Findings

### Code extraction truncation
LLM splits output across multiple fenced code blocks. `parse_full_rewrite` took only the first block. **Fix:** `max(matches, key=len)` — picks the longest block.

### Verbose error noise
`coqc` error messages include "In environment" blocks (15-30 lines of hypotheses). **Fix:** Evaluator strips environment blocks via regex, surfacing only file location + core error (74% size reduction).

### Axiom tracking
Benchmarks requiring `Axiom` → `Inductive` replacement weren't tracked. **Fix:** Count non-`todo` `Axiom` declarations as open obligations.

### Trivial spec replacement
LLM replaced entire spec with `Theorem dummy : True. Proof. exact I. Qed.` scoring 1.0. **Fix:** `done` requires `qed_count >= _INITIAL_PROOF_OBLS` (Qed+Admitted count in initial file). Score denominator floored at this value.

### Proof plateaus
When stuck on one hard lemma, score is flat. **Fix (v4):** `admit.` for sub-goals gives fractional credit + goal-state feedback shows remaining sub-goals + proved-pattern feedback enables tactic reuse.

### Dead-end decomposition trap (v5)
The LLM splits a conjunctive theorem (`P /\ Q`) into two separate helper lemmas, proves the parent by applying them (→ Qed!), but the helpers are individually unprovable because each loses half the induction hypothesis. The `admit.` discount made this score *higher* than the unsplit original, creating a trap state the search cannot escape.

**Root cause:** The 0.5 gave_up discount was only ever effective when `total > floor` — i.e., when the LLM had added new Admitted stubs. For original-spec Admitted proofs, the floor absorbed the discount and it had no effect. The incentive was exactly backwards.

**Fix (v5):** Anti-inflation guard — the gave_up discount only applies when `qed_count + admitted_count <= _INITIAL_PROOF_OBLS`. If the LLM inflated obligations, all Admitted get full 1.0 weight.

**Prompt fix (v5):** Reframed "prove ONE Admitted with Qed per call" → "make ONE step of progress" with admit.-based incremental work as the *preferred* approach for hard proofs. Added general proof patterns: conjunctive induction (don't split), generalize before induction, function case analysis via destruct.
