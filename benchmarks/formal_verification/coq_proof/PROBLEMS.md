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
**Solved:** iter 25/100 · 5 Qed · Gemini 3 Pro. Full induction on `exp_match` evidence with explicit witnesses across all 7 constructors. 200 lines.
**Source:** SF Vol. 1 — [IndProp, pumping exercise](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)

---

## trie_adt

**What:** Define the representation invariant `is_trie` for a binary trie, then prove 10 theorems relating trie operations to a `total_map` abstraction.
**Initial spec:** 1 `todo` definition (`is_trie`), 10 `Admitted` theorems, 2 given `Qed` lemmas. `total_map` inlined from VFA/Maps. Uses stdlib `positive` type.
**Difficulty:** Very hard. SF exercises range 1–3 stars individually, but the LLM must *invent* the representation invariant and prove abstraction theorems (`empty_relate`, `lookup_relate`, `insert_relate`) plus injectivity and structural lemmas.
**Solved:** iter 24/100 · 12 Qed + `is_trie` invented · Gemini 3 Pro
**Source:** SF Vol. 3 (VFA) — [Trie chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Trie.html)

---

## redblack_tree

**What:** Verified red-black tree: balanced BST with color invariants. Prove BST preservation through balance/insert, lookup correctness (equational spec), and the red-black height bound.
**Initial spec:** 14 `Admitted` theorems, 14 given `Qed`. All implementations given (`balance`, `ins`, `insert`, `lookup`). Inlined `int` type from VFA/Extract. 423 lines.
**Difficulty:** Very hard. 14 exercises totaling ~32 stars (includes 4★ `balance_lookup`, 4★ `ins_RB`, 4★ `redblack_balanced`). Automated case analysis over 58+ balance cases. Three proof domains: BST ordering, equational lookup, red-black color/height.
**Status:** Running (100 iters, Gemini 3 Pro).
**One-shot baseline:** 0.00 (response truncated to 36 lines, doesn't compile)
**Source:** SF Vol. 3 (VFA) — [Redblack chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)

---

## binomial_queue

**What:** Verified mergeable priority queue (binomial heap). Invent `priqueue_elems` abstraction relation, prove 20 theorems about invariant preservation and abstraction correctness — including three 5★ theorems about `delete_max`.
**Initial spec:** 1 `Axiom` to replace with `Inductive` (`priqueue_elems`), 20 `Admitted` theorems, 5 given `Qed`. All implementations given. 305 lines.
**Difficulty:** Very hard. 56 total stars across exercises. Three 5★ theorems (`delete_max_Some_priq`, `delete_max_None_relate`, `delete_max_Some_relate`). LLM must invent the `priqueue_elems` inductive relation and prove correctness of all ADT operations.
**Status:** Running (100 iters, Gemini 3 Pro).
**One-shot baseline:** 0.00 (syntax error at line 49, only 4 given Qed survived)
**Source:** SF Vol. 3 (VFA) — [Binom chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Binom.html)

---

# One-Shot Baseline (Gemini 3 Pro Preview)

Single LLM call, no feedback, no retry. Shows which problems actually need iterative co-synthesis.

| Problem | Score | Compiles | Verdict |
|---|---|---|---|
| `all_less_than` | 1.00 | Yes | **Solved** — trivial |
| `insertion_sort` | 1.00 | Yes | **Solved** — LLM knows this |
| `pigeonhole` | 1.00 | Yes | **Solved** — surprising, got `repeats` + proof first try |
| `bst_verification` | 0.00 | No | Almost — one proof bullet error |
| `regex_matcher` | 0.00 | No | Failed — complex type-level reasoning |
| `trie_adt` | 0.00 | No | Failed — `look_ins_other` proof incomplete |
| `strong_pumping` | 0.00 | No | Completely failed — 0 Qed, tactic syntax errors |
| `binomial_queue` | 0.00 | No | Completely failed — only 4 given Qed survived |
| `redblack_tree` | 0.00 | No | Completely failed — response truncated to 36 lines |

**Takeaway:** 3 easy problems are solvable in one shot. The 6 hard ones (`bst_verification`, `regex_matcher`, `trie_adt`, `strong_pumping`, `binomial_queue`, `redblack_tree`) fail without iterative co-synthesis.

Raw results in each problem's `baseline_oneshot/` folder.

---

# Potential Next Problems

Problems targeting the path from textbook proofs toward certified systems.

---

## Tier 1: VFA — Verified Data Structures (single file, Coq stdlib, ready now)

### Graph Coloring / Register Allocator (VFA/Color)
**What:** Kempe's graph coloring algorithm with termination proof. Uses `FMaps`/`FSets`.
**Key exercises:** `cardinal_map` (4★), `Sremove_cardinal_less` (4★), full coloring correctness.
**Why:** This IS a verified compiler backend component — CompCert uses the same algorithm.
**Source:** [VFA Color chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Color.html)

---

## Tier 2: SLF — Separation Logic (requires SLF library — the systems frontier)

### Stack ADT with Encapsulation (SLF/Repr)
**What:** Stack as (mutable list pointer + size counter). Define `Stack L s` representation predicate. Verify `push` (3★) and `pop` (4★).
**Why:** THE verified ADT pattern. Exactly how seL4, CertiKOS verify data structures. First separation logic benchmark.
**Source:** [SLF Repr chapter](https://softwarefoundations.cis.upenn.edu/slf-current/Repr.html)

### Mutable List Iterator (SLF/Repr)
**What:** Higher-order iterator over mutable linked list. Verify invariant preservation with frame reasoning.
**Key exercise:** `triple_miter` (5★).
**Why:** Verified `foreach` loop — bread and butter of verified OS container libraries.
**Source:** [SLF Repr chapter](https://softwarefoundations.cis.upenn.edu/slf-current/Repr.html)

---

## Tier 3: VC — Verifiable C (requires VST — the ultimate goal)

### Verified Hash Table (VC/Verif_hash)
**What:** Complete C hash table verified against a functional model using VST separation logic.
**Key exercises:** `body_hash` (3★), `body_get` (3★), `body_new_table` (2★) — ~20 stars total.
**Why:** Real C program verification. This is what verified systems work actually looks like.
**Source:** [VC Verif_hash chapter](https://softwarefoundations.cis.upenn.edu/vc-current/Verif_hash.html)

### Verified String Library (VC/Verif_strlib)
**What:** Verify C `strlen`, `strcpy`, `strcmp` with `cstring` representation predicates.
**Key exercise:** `body_strcmp` (4★) — hardest single exercise in VC volume.
**Why:** libc function verification. Buffer overflows in string functions are the most exploited vulnerability class.
**Source:** [VC Verif_strlib chapter](https://softwarefoundations.cis.upenn.edu/vc-current/Verif_strlib.html)

---

## Tier 4: PLF — Verified Language Implementation

### Extended STLC with Full Type Safety (PLF/MoreStlc)
**What:** Build a complete programming language: numbers, let, pairs, sums, lists, fix. Define `subst` (3★), `step` (3★), `has_type` (3★). Prove Progress + Preservation.
**Why:** This is building a verified interpreter/runtime. Same pattern as CompCert, CakeML.
**Source:** [PLF MoreStlc chapter](https://softwarefoundations.cis.upenn.edu/plf-current/MoreStlc.html)

---

## Escalation Path

```
Done (VFA)        →  BST, Trie
Running (VFA)     →  Binomial Queue, Red-Black Tree
Next (VFA)        →  Graph Coloring (compiler backend)
                                    ↓
Separation Logic  →  SLF Stack ADT  →  SLF Iterator
                                    ↓
C Verification    →  VC String Lib  →  VC Hash Table
```

Each step adds one new proof dimension. If SLF Stack ADT works, the claim becomes: *"AI co-synthesizes verified heap-manipulating ADTs with separation logic."*
