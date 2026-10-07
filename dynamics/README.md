# Dynamics

Shared finite probability and stochastic dynamics for Leanamics. This package
uses Lean 4.32.0 and Mathlib revision
`2d8c533bd0a0515caa32f18c0ab4485bd6229378`, exactly matching 3-majority.

| Module | API |
| --- | --- |
| `Uniform` | Finite averages, recursive uniform trajectory expectations, independence, reindexing; extracted from 3-majority |
| `Equivalence` | `expList_eq_avg_ofFn`, adapted from rumor spreading without modifying that independently pinned package |
| `Distribution` | Normalized nonnegative real weights, expectations, event probabilities, uniform distributions, point masses, independent products, pushforward |
| `Kernel` | Finite stochastic kernels, finite-time expectations, events, stationarity, harmonic observables |
| `Trajectory` | Weighted history/endpoint expectations and agreement with kernel iteration |
| `Stationary` | Stationary-distribution existence by Cesàro averages and compactness of the finite simplex |
| `Absorption` | Uniform absorption blocks, geometric survival bounds, convergence to zero |
| `Rounds` | The kernel `ofStep` of a process driven by i.i.d. uniform rounds, its agreement with `expList`, and `expList_escape` (union bound over rounds for a moving target) |
| `Concentration` | Hoeffding's and Bernstein's inequalities for sums of independent coordinates |
| `Phases` | Progress through nested phases (`nested_phases`, Lemma A.4 of Becchetti et al., SPAA 2014) |
| `DriftSeq` | Time-dependent chains (`iterateSeq`: kernel `K t` for the step `t → t + 1`), linearity and monotonicity |
| `Drift` | Drift theorems of Berenbrink et al. (ICALP 2016): drift `c/Ψ` ⇒ absorbed with probability `≥ 1/2` once `∑ c_t ≥ 4Ψ₀²` (`drift_absorption`, Lemma 2.2); multiplicative drift ⇒ survival `≤ ∏(1 − δ_t) Ψ₀/Ψ_min` (`multiplicative_drift`, Lemma 2.4); `_seq` forms for time-dependent chains |
| `GraphRounds` | Graph-indexed round types: `NeighborRound G` (every vertex samples a neighbour; independence and marginals) and `EdgeRound G` (one uniform oriented edge; edge, orientation and degree-bias averages) |

`avg` remains zero on an empty sample type. Normalized distributions require
mass one and therefore cannot inhabit an empty sample space; `uniform` requires
`Nonempty`. Weighted and uniform expectations agree on nonempty types.

The absorption API uses a zero-one survival indicator `f`. Its hypothesis
`K.apply f ≤ f` expresses absorption of the target `f = 0`, and
`∀ a, ∃ n, K.iterate n f a < 1` expresses positive-probability access.
`exists_uniform_block` produces a positive block length and contraction factor
strictly below one; `geometric_blocks` and `finite_absorption` give the decay
bound and full-time limit. No measure-theoretic path space is used.

Build and audit from this directory:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

The [blueprint](blueprint/src/content.tex) documents the generic results and
generates their dependency graph. Pages CI builds its HTML/PDF and doc-gen4 API
documentation. The same workflow as the existing packages is used; doc-gen4 is
resolved separately to preserve the main project's dependency pins.

3-majority retains all original `ThreeMajority` probability declarations and
blueprint links through compatibility declarations. The mean-scaled Chernoff bounds remain in 3-majority; `Concentration` adds
the Hoeffding and Bernstein inequalities used by `plurality/`.
