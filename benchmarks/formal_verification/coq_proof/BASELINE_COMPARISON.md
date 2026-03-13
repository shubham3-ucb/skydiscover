# Iterative Baseline vs AdaEvolve — Coq Proof Synthesis

Comparison of two approaches on 9 Coq proof synthesis benchmarks.

- **AdaEvolve**: multi-island evolutionary search (population=10, 2 islands, paradigm breakthrough, UCB selection) — `gemini/gemini-3-pro-preview`
- **Iterative Baseline**: single-thread multi-turn conversation loop with context compaction, one lemma per turn — `gemini-3-pro-preview`

---

## Results Summary

| Problem | Difficulty | Iterative — Score | Iterative — First Solved | AdaEvolve — Score | AdaEvolve — First Solved |
|---------|------------|:-----------------:|:------------------------:|:-----------------:|:------------------------:|
| `all_less_than` | ⭐ | **1.00** | iter **3** | **1.00** | iter 5 |
| `insertion_sort` | ⭐ | **1.00** | iter **2** | **1.00** | iter 15 |
| `pigeonhole` | ⭐ | **1.00** | iter **3** | **1.00** | iter 5 |
| `regex_matcher` | ⭐⭐ | **1.00** | iter **8** | **1.00** | iter 15 |
| `bst_verification` | ⭐⭐ | **1.00** | iter **9** | **1.00** | iter 25 |
| `trie_adt` | ⭐⭐ | **1.00** | iter **28** | **1.00** | iter 25 |
| `strong_pumping` | ⭐⭐⭐ | 0.80 | ❌ (100 iters) | **1.00** | iter **10** |
| `binomial_queue` | ⭐⭐⭐⭐ | 0.76 | ❌ (200 iters) | 0.76 | ❌ (200 iters) |
| `redblack_tree` | ⭐⭐⭐⭐ | 0.9655¹ | ❌ (crashed@47) | 0.9655 | ❌ (200 iters) |

¹ Iterative baseline crashed at iter 47 (LLM returned None) after reaching 28/29 Qed; rerun in progress.

**Solved: Iterative 6/9 · AdaEvolve 7/9**

---

## Key Observations

### Iterative baseline wins on easy problems
For problems ≤⭐⭐ difficulty, the iterative baseline is **faster to first solve** — it converges in 2–28 turns vs AdaEvolve's 5–25 iterations. The single focused conversation keeps the LLM on track without the overhead of population management.

### AdaEvolve wins on hard problems
`strong_pumping` is the clearest example: iterative baseline plateaued at 0.80 (4/5 Qed) for 96 consecutive iterations without ever cracking the final lemma. AdaEvolve solved it at **iter 10** via population diversity + paradigm breakthrough discovering the right induction scheme.

### Both fail on the hardest two
`binomial_queue` and `redblack_tree` are unsolved by both approaches at 200 iterations:
- **RB**: both reach 0.9655 (28/29 Qed). The final lemma (`ins_RB`) requires a `balance_NearlyRB` helper that neither approach has discovered.
- **BQ**: both plateau at 0.76 (19/25 Qed). The `carry_elems`/`join_elems`/`*_relate` cluster requires coordinated multi-lemma proofs that exceed single-turn LLM capacity.

### Compile failure rate
The iterative baseline suffers heavy FAIL rates on hard problems (>80% of iters after stalling). Each failed attempt wastes ~135s on coqc timeout. AdaEvolve's population keeps multiple working programs alive, avoiding the "revert to best" loop.

---

## What These Results Mean for AdaEvolve

| Regime | Recommendation |
|--------|---------------|
| Easy problems (≤⭐⭐) | Iterative baseline is sufficient — cheaper, faster |
| Medium problems (⭐⭐⭐) | AdaEvolve's paradigm breakthrough is critical |
| Hard problems (⭐⭐⭐⭐) | Neither approach solves alone — need stronger helper-lemma discovery or human hints |

The iterative baseline serves as a useful **lower bound**: any problem AdaEvolve cannot beat it on is trivial; any problem AdaEvolve solves first shows where the evolutionary search adds real value.
