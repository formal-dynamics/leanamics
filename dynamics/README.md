# Dynamics

Shared finite probability and stochastic dynamics for Leanamics. This package
uses Lean 4.32.0 and Mathlib revision
`2d8c533bd0a0515caa32f18c0ab4485bd6229378`, exactly matching 3-majority.

| Module | API |
| --- | --- |
| `Uniform` | Finite averages, recursive uniform trajectory expectations, independence, reindexing; extracted from 3-majority |
| `Equivalence` | `expList_eq_avg_ofFn`, the recursive `expList` is the uniform average over `Fin T → α` |
| `Distribution` | Normalized nonnegative real weights, expectations, event probabilities, uniform distributions, point masses, independent products, pushforward |
| `Bridge` | The three expectation APIs agree: `avg` is Mathlib's `𝔼 a, f a` (`avg_eq_expect`), the product of uniform laws is uniform (`Distribution.independent_uniform_expect`), and `expList` is the expectation over `T` i.i.d. draws in Mathlib's and in the distribution form (`expList_eq_expect`, `expList_eq_independent_expect`) |
| `Kernel` | Finite stochastic kernels, finite-time expectations, events, stationarity, harmonic observables |
| `Trajectory` | Weighted history/endpoint expectations and agreement with kernel iteration |
| `Stationary` | Stationary-distribution existence by Cesàro averages and compactness of the finite simplex |
| `Absorption` | Uniform absorption blocks, geometric survival bounds, convergence to zero |
| `Rounds` | The kernel `ofStep` of a process driven by i.i.d. uniform rounds, its agreement with `expList`, and `expList_escape` (union bound over rounds for a moving target) |
| `Concentration` | Hoeffding's (both tails) and Bernstein's inequalities and the multiplicative Chernoff bounds (MGF bound, parametric and closed-form tails, `P(X ≤ (1-δ)μ) ≤ exp(-δ²μ/2)`) for sums of independent coordinates |
| `Tail` | Monotonicity of probability, Markov's inequality, the one-round bound `1 - 𝔼[bad]` for `ofStep`, monotone occupation of absorbing events, strict bounds `𝔼f < 1`, the `log n` conversions |
| `Phases` | Progress through nested phases (`nested_phases`, Lemma A.4 of Becchetti et al., SPAA 2014) |

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

This is the only finite-probability layer of the repository: `rumor_spread/`,
`3-majority/` and `plurality/` use `avg` and `expList` from here (see
[EXPECTATION_AUDIT.md](EXPECTATION_AUDIT.md) for the audit that removed the copies).
3-majority retains its `ThreeMajority` probability names and blueprint links
through compatibility declarations: `ThreeMajority.avg` is a reducible alias of `avg`.
All concentration and tail bounds of `median/`, `plurality/` and `3-majority/` live in
`Concentration` and `Tail` (see [CONCENTRATION_AUDIT.md](CONCENTRATION_AUDIT.md) for the
audit that removed the copies).
