# Plurality consensus: 3-majority with `k` colors

A Lean 4 + Mathlib formalization of

> L. Becchetti, A. Clementi, E. Natale, F. Pasquale, R. Silvestri, L. Trevisan,
> **Simple Dynamics for Plurality Consensus**, SPAA 2014,
> [doi:10.1145/2612669.2612677](https://doi.org/10.1145/2612669.2612677);
> journal version [arXiv:1310.2858](https://arxiv.org/abs/1310.2858).

`n` nodes each support one of `k` colors. Every round, each node samples three
nodes uniformly at random (with repetition, possibly itself) and adopts the
majority color among them, or the first one if all three differ.

> **Theorem 3.8.** Let `λ ≥ 3`. If `m` is the unique plurality color,
> `c_m ≥ n/λ` and the bias is at least `22 √(λ n log n)`, then all nodes
> support `m` after `O(λ log n)` rounds with high probability.

Formally (`Plurality.theorem_3_8` in [Plurality/Upper.lean](Plurality/Upper.lean)):
if `log n ≥ 40` and `k ≥ 2`, then after `10 T` rounds, where
`T = phases n λ ≤ 13 λ log n` (`Plurality.phases_le`), consensus on `m` holds
with probability at least `1 - 11 T / n`. `Plurality.theorem_3_8_bigO` states
this as `≤ 130 λ log n` rounds with probability `≥ 1 - 143 λ log n / n`.

**[Blueprint](https://formal-dynamics.github.io/leanamics/plurality/blueprint/)** ·
**[Blueprint as pdf](https://formal-dynamics.github.io/leanamics/plurality/blueprint.pdf)** ·
**[Dependency graph](https://formal-dynamics.github.io/leanamics/plurality/blueprint/dep_graph_document.html)** ·
**[API docs](https://formal-dynamics.github.io/leanamics/plurality/docs/)**

## Status

| Paper | Lean | Status |
| --- | --- | --- |
| Model, Lemma 2.1 | `Model.lean`, `expected_count` | done |
| Lemmas 3.1, 3.2 | `lemma_3_1_a/b/c`, `lemma_3_2_a/b/c` | done |
| Lemmas 3.3, 3.4, 3.5 | `lemma_3_3`, `lemma_3_4`, `lemma_3_5` | done |
| Lemmas 3.6, 3.7 | `lemma_3_6`, `lemma_3_7_i`, `lemma_3_7_ii` | done |
| Lemma A.4 | `Dynamics.Kernel.nested_phases` | done |
| Theorem 3.8 | `theorem_3_8`, `theorem_3_8_bigO` | done |
| `k = 2` | `binary_consensus_whp` (reuses `three_majority`) | done |
| `k = 2` from a vanishing bias (gap `22√(3 n log n)`, `≤ 390 log n` rounds) | `majority3_vanishing_bias` (Theorem 3.8 with `λ = 3`, stated for `ThreeMajority.run`) | done |
| Corollaries 3.10–3.12 | `corollary_3_10`, `corollary_3_11`, `corollary_3_12` | done |
| Observation 3.9 (adversary) | | open |
| Lemma 4.1, Theorem 4.2 (`Ω(k log n)`) | `lemma_4_1`, `theorem_4_2`, `theorem_4_2_log` | done, for `k ≤ n^{1/4-δ}` |
| Theorem 4.8 (a), Lemma 4.9 | `theorem_4_8_a`, `not_solver_of_drift` | done except rules with `Δ_r, Δ_b ≤ 1` |
| Theorem 4.8 (b), Lemma 4.10 | `theorem_4_8_b`, `not_solver_of_nonuniform` | done |
| Lemma 4.11, Theorem 4.12 (`h`-plurality) | `lemma_4_11`, `theorem_4_12`, `theorem_4_12_log` | done |

The proof of Theorem 3.8 departs from the paper in a few places, and some
proofs in both versions of the paper have gaps. Both are recorded in
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

## Layout

| Module | Content |
| --- | --- |
| `Model` | Colorings, 3-input rules, `maj3`, rounds, the Markov kernel |
| `Expectation` | Adoption probabilities and Lemma 2.1 |
| `Quantities` | `m(c)`, `M(c)`, `s(c)`, `α(c)`, `γ(c)`, `μ_j(c)`; Lemmas 3.1, 3.2 |
| `Tail` | Chernoff lower tail and Markov's inequality |
| `Numerics` | Explicit "sufficiently large `n`" bounds |
| `Growth` | Lemmas 3.3, 3.4, 3.5 |
| `Saturation` | Lemmas 3.6, 3.7 |
| `Upper` | The phases, one round of each phase, Theorem 3.8 |
| `Corollaries` | Corollaries 3.10, 3.11, 3.12 |
| `Binary` | The `k = 2` case via the `three_majority` package |
| `Lower` | Lemma 4.1 and Theorem 4.2 |
| `Rules` | 3-input rules, `Δ`, `δ`, solvers, consensus needs survival |
| `ClearMajority` | Theorem 4.8 (a) |
| `UniformRule` | Theorem 4.8 (b) |
| `HPlurality` | The `h`-plurality model, Lemma 4.11, Theorem 4.12 |

The package depends on `../dynamics` (finite distributions, kernels,
Bernstein and Hoeffding inequalities, the nested-phase lemma) and
`../3-majority` (its Chernoff bounds and the binary theorem). Like the rest of
the repository it uses no measure theory, `PMF`/`ENNReal` or martingales.

## Building

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py   # audits the theorems listed in Audit.lean
```
