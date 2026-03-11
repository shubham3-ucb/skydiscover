# Benchmark Problems

Each problem is a self-contained Coq file with function stubs (`todo`) and theorem stubs (`Admitted`).
The LLM must co-synthesize the implementation and its machine-checked proof step by step.
One generic evaluator and prompt across all problems.

---

## all_less_than

**What:** Check whether all elements of a `list nat` are less than a bound `n`.
**Initial spec:** 1 `todo` function, 1 `Admitted` theorem.
**Difficulty:** Easy. Single recursive function, one inductive proof.
**Solved:** iter 1/50 · 1 Qed · GPT-5
**Source:** Custom toy example.

---

## insertion_sort

**What:** Implement a sorting function on `list nat` and prove it produces a sorted permutation of the input.
**Initial spec:** 1 `todo` function (`sort`), 1 `Admitted` theorem. `Inductive sorted` and `is_a_sorting_algorithm` given.
**Difficulty:** Medium. LLM must discover it needs a helper `insert` function and chain 4 sub-lemmas. SF exercises for this problem range 1–3 stars.
**Solved:** iter 14/50 · 5 Qed (4 invented sub-lemmas) · GPT-5
**Source:** SF Vol. 3 (VFA) — [Sort chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html)

---

## pigeonhole

**What:** Define a `repeats` predicate (list has a duplicate) and prove the pigeonhole principle.
**Initial spec:** 1 `todo` definition (`repeats`), 2 `Admitted` theorems (`in_split`, `pigeonhole_principle`).
**Difficulty:** Hard (5★ advanced optional in SF). LLM must *invent* the definition of `repeats`, then prove a theorem requiring `excluded_middle`, list surgery via `in_split`, and `lia` for length arithmetic.
**Solved:** iter 5/50 · 2 Qed · Gemini 3 Pro
**Source:** SF Vol. 1 — [IndProp, pigeonhole exercise](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab261)

---

## regex_matcher

**What:** Implement a regex matcher via Brzozowski derivatives (`match_eps`, `derive`, `regex_match`) and prove correctness against a relational `exp_match` spec.
**Initial spec:** 3 `todo` functions, 5 `Admitted` theorems, 9 given `Qed` helper lemmas. 164 lines.
**Difficulty:** Hard. Individual SF exercises range 2–4 stars (hardest: `derive_corr` at 4★). Requires knowing the derivative construction, careful case analysis, and `remember` / induction-on-evidence.
**Solved:** iter 12/50 · 14 Qed (5 new + 9 given) · Gemini 3 Pro
**Source:** SF Vol. 1 — [IndProp, regex exercises](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)

---

## bst_verification

**What:** Implement `bound`, `lookup`, `insert` on a BST and prove invariant preservation and lookup correctness.
**Initial spec:** 3 `todo` functions, 5 `Admitted` theorems. `ForallT`, `BST` inductive invariant given.
**Difficulty:** Hard. SF exercises: `empty_tree_BST` (1★), `insert_BST` (3★), lookup theorems (2★ each). Requires 3-way key comparison, non-trivial auxiliary lemma ordering, equational proofs about `lookup ∘ insert`.
**Solved:** iter 23/50 · 9 Qed (4 invented sub-lemmas) · Gemini 3 Pro
**Source:** SF Vol. 3 (VFA) — [SearchTree chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)

---

## strong_pumping

**What:** Prove the strong pumping lemma for regular expressions, including 4 helper lemmas and the main theorem.
**Initial spec:** 5 `Admitted` (no implementation, pure proof). `pumping_constant` and `napp` functions given.
**Difficulty:** Very hard (5★ advanced optional in SF). Deep nested induction on `exp_match` evidence with existential witnesses. No implementation — pure proof reasoning.
**Status:** Running (100 iters, Gemini 3 Pro)
**Source:** SF Vol. 1 — [IndProp, pumping exercise](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)

---

## trie_adt

**What:** Define the representation invariant `is_trie` for a binary trie, then prove 10 theorems relating trie operations to a `total_map` abstraction.
**Initial spec:** 1 `todo` definition (`is_trie`), 10 `Admitted` theorems, 2 given `Qed` lemmas. `total_map` inlined from VFA/Maps. Uses stdlib `positive` type.
**Difficulty:** Very hard. SF exercises range 1–3 stars individually, but the LLM must *invent* the representation invariant and prove abstraction theorems (`empty_relate`, `lookup_relate`, `insert_relate`) plus injectivity and structural lemmas.
**Status:** Running (100 iters, Gemini 3 Pro)
**Source:** SF Vol. 3 (VFA) — [Trie chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Trie.html)
