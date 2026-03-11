# Benchmark Problems

Each problem is a self-contained Coq file with function stubs (`todo`) and theorem stubs (`Admitted`).
The LLM must co-synthesize the implementation and its machine-checked proof step by step.
All solutions verified by `coqc` with score 1.0.

---

## all_less_than

**What:** Check whether all elements of a `list nat` are less than a bound `n`.  
**Why easy:** Single recursive function, one inductive proof by list cases. Trivial for a capable LLM.  
**Solved:** iter 30/30 · 1 Qed  
**Source:** Custom toy example used to prototype the benchmark setup.

---

## insertion_sort

**What:** Implement insertion sort on `list nat` and prove the result is sorted.  
**Why medium:** Requires a helper `insert` function, an `Inductive sorted` predicate, and a correctness proof that chains lemmas about `insert` preserving sortedness.  
**Solved:** iter 30/30 · 5 Qed  
**Source:** Inspired by SF Vol. 1 (Logical Foundations) — [Lists chapter](https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html)

---

## regex_matcher

**What:** Implement a regex matcher via Brzozowski derivatives (`match_eps`, `derive`, `regex_match`) and prove correctness (`derive_corr`, `regex_match_correct`) against a relational `exp_match` spec.  
**Why hard:** Requires knowing the derivative construction, careful 3-way case analysis in proofs, and use of `remember` / `induction on evidence` to avoid ill-typed induction. The `derive_corr` proof is a 50-line structural induction.  
**Solved:** iter 12/50 · 14 Qed  
**Source:** SF Vol. 1 — [IndProp chapter, regex exercises](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)

---

## pigeonhole

**What:** Define an `Inductive`-style `repeats` predicate (list has a duplicate) and prove the pigeonhole principle: if `|l1| > |l2|` and every element of `l1` is in `l2`, then `l1` has a repeat.  
**Why hard:** The LLM must *invent* the right definition of `repeats`, then prove a theorem that requires `excluded_middle`, careful list surgery via `in_split`, and `lia` for length arithmetic. A 4-star SF exercise.  
**Solved:** iter 5/50 · 2 Qed  
**Source:** SF Vol. 1 — [IndProp chapter, pigeonhole exercise](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab261)

---

## bst_verification

**What:** Implement `bound`, `lookup`, `insert` on a binary search tree (keyed by `nat`) and prove: `empty_tree_BST`, `ForallT_insert`, `insert_BST`, `lookup_insert_eq`, `lookup_insert_neq`.  
**Why hard:** Requires 3-way key comparison (`k <? k'`, `k' <? k`), a non-trivial auxiliary lemma (`ForallT_insert`) that must be proved *before* `insert_BST`, and two commutativity-style equational proofs about `lookup ∘ insert`. Needs `lia` for arithmetic reasoning on keys.  
**Solved:** iter 41/50 · 9 Qed  
**Source:** SF Vol. 3 (VFA) — [SearchTree chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)
