# Benchmark Problems

Each problem is a self-contained Coq file with function stubs (`todo`) and theorem stubs (`Admitted`).
The LLM co-synthesizes the implementation and its machine-checked proof step by step.
One generic evaluator and prompt across all problems.

---

## all_less_than

**What:** Check whether all elements of a `list nat` are less than a bound.
**Spec:** 1 `todo` function, 1 `Admitted` theorem.
**Difficulty:** Easy.
**Solved:** iter 1/50 · 1 Qed · GPT-5
**Source:** Custom toy example.

---

## insertion_sort

**What:** Implement sorting on `list nat`, prove it produces a sorted permutation.
**Spec:** 1 `todo` function, 1 `Admitted` theorem.
**Difficulty:** Medium (1–3★). LLM must discover helper `insert` and chain 4 sub-lemmas.
**Solved:** iter 14/50 · 5 Qed · GPT-5
**Source:** [VFA Sort](https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html)

---

## pigeonhole

**What:** Define `repeats` predicate, prove the pigeonhole principle.
**Spec:** 1 `todo` definition, 2 `Admitted` theorems.
**Difficulty:** Hard (5★ advanced optional).
**Solved:** iter 5/50 · 2 Qed · Gemini 3 Pro
**Source:** [LF IndProp](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab261)

---

## regex_matcher

**What:** Regex matcher via Brzozowski derivatives. Prove correctness against relational `exp_match`.
**Spec:** 3 `todo` functions, 5 `Admitted` theorems, 9 given `Qed`. 164 lines.
**Difficulty:** Hard (2–4★). `derive_corr` is 4★.
**Solved:** iter 12/50 · 14 Qed · Gemini 3 Pro
**Source:** [LF IndProp](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)

---

## bst_verification

**What:** Implement `bound`, `lookup`, `insert` on BST, prove invariant preservation.
**Spec:** 3 `todo` functions, 5 `Admitted` theorems.
**Difficulty:** Hard (1–3★).
**Solved:** iter 23/50 · 9 Qed · Gemini 3 Pro
**Source:** [VFA SearchTree](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)

---

## strong_pumping

**What:** Prove the strong pumping lemma for regular expressions.
**Spec:** 5 `Admitted` (pure proof, no implementation).
**Difficulty:** Very hard (5★ advanced optional).
**Solved:** iter 25/100 · 5 Qed · Gemini 3 Pro
**Source:** [LF IndProp](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)

---

## trie_adt

**What:** Define representation invariant `is_trie`, prove 10 abstraction theorems.
**Spec:** 1 `todo` definition, 10 `Admitted`, 2 given `Qed`. 131 lines.
**Difficulty:** Very hard (1–3★ individually, but must invent invariant).
**Solved:** iter 24/100 · 12 Qed · Gemini 3 Pro
**Source:** [VFA Trie](https://softwarefoundations.cis.upenn.edu/vfa-current/Trie.html)

---

## binomial_queue

**What:** Verified mergeable priority queue. Invent `priqueue_elems` relation, prove 20 theorems.
**Spec:** 1 `Axiom` → `Inductive`, 20 `Admitted`, 5 given `Qed`. 305 lines.
**Difficulty:** Very hard (56 total ★, three 5★ theorems).
**Best so far:** 19/25 Qed (0.76) — both AdaEvolve (200 iters) and iterative baseline (200 iters). Proved `carry_valid`, `smash_elems`, `insert_priq`. Stuck on `join_valid`/`*_elems`/`*_relate` cluster.
**Status:** Unsolved.
**One-shot baseline:** 0.00
**Source:** [VFA Binom](https://softwarefoundations.cis.upenn.edu/vfa-current/Binom.html)

---

## redblack_tree

**What:** Verified red-black tree. Prove BST + lookup + RB-balance properties.
**Spec:** 14 `Admitted`, 14 given `Qed`. All implementations given. 423 lines.
**Difficulty:** Very hard (~32★, includes 4★ `balance_lookup`, 4★ `ins_RB`).
**Best so far:** 28/29 Qed (0.9655) — both AdaEvolve (200 iters) and iterative baseline. Only `ins_RB` (4★) remains — needs `balance_NearlyRB` helper decomposition.
**Status:** Unsolved.
**One-shot baseline:** 0.00
**Source:** [VFA Redblack](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)

---

# One-Shot Baseline (Gemini 3 Pro Preview)

Single LLM call, no feedback, no retry.

| Problem | Score | Compiles | Verdict |
|---|---|---|---|
| `all_less_than` | 1.00 | Yes | Solved — trivial |
| `insertion_sort` | 1.00 | Yes | Solved |
| `pigeonhole` | 1.00 | Yes | Solved |
| `bst_verification` | 0.00 | No | Almost — one proof bullet error |
| `regex_matcher` | 0.00 | No | Failed — complex type-level reasoning |
| `trie_adt` | 0.00 | No | Failed |
| `strong_pumping` | 0.00 | No | Failed — 0 Qed |
| `binomial_queue` | 0.00 | No | Failed |
| `redblack_tree` | 0.00 | No | Failed — response truncated |

3 easy problems solvable one-shot. 6 hard ones need iterative co-synthesis.
