# Dynamics

Shared finite probability and stochastic dynamics for Leanamics. This package
uses Lean 4.32.0 and Mathlib revision
`2d8c533bd0a0515caa32f18c0ab4485bd6229378`, exactly matching 3-majority.

| Module | API |
| --- | --- |
| `Uniform` | Finite averages, recursive uniform trajectory expectations, independence, reindexing; extracted from 3-majority |
| `Equivalence` | `expList_eq_avg_ofFn`, the recursive `expList` is the uniform average over `Fin T → α` |
| `Distribution` | Normalized nonnegative real weights, expectations, event probabilities and their elementary bounds (monotonicity, complement, union bounds, inclusion–exclusion, Markov's inequality), uniform distributions, point masses, independent products, pushforward |
| `Bridge` | The three expectation APIs agree: `avg` is Mathlib's `𝔼 a, f a` (`avg_eq_expect`), the product of uniform laws is uniform (`Distribution.independent_uniform_expect`), and `expList` is the expectation over `T` i.i.d. draws in Mathlib's and in the distribution form (`expList_eq_expect`, `expList_eq_independent_expect`) |
| `Kernel` | Finite stochastic kernels, finite-time expectations, events, stationarity, harmonic observables |
| `Trajectory` | Weighted history/endpoint expectations and agreement with kernel iteration |
| `Stationary` | Stationary-distribution existence by Cesàro averages and compactness of the finite simplex |
| `Absorption` | Uniform absorption blocks, geometric survival bounds, convergence to zero |
| `OptionalStopping` | Finite-horizon optional stopping (roadmap FND-4): a conserved observable, constant on two target events, gives the finite-time error bound `event_error_of_invariant`, the limit `tendsto_event_of_invariant` and the absorption probability `iSup_event_of_invariant` = `(φ(x₀) − φB)/(φA − φB)` |
| `Rounds` | The kernel `ofStep` of a process driven by i.i.d. uniform rounds, its agreement with `expList`, and `expList_escape` (union bound over rounds for a moving target) |
| `Reverse` | Time reversal of i.i.d. rounds (roadmap FND-6): `expList_comp_reverse`, and `iterate_ofStep_foldr` (round-based kernels applied last round first) |
| `Concentration` | Hoeffding's (both tails) and Bernstein's inequalities for sums of independent coordinates, and the variance bound `p(1 - p) ≤ p` of a `{0,1}` coordinate |
| `Moments` | Moments of sums of independent coordinates: Cauchy-Schwarz for `avg` (Mathlib's `Finset.expect_mul_sq_le_sq_mul_sq`), second and fourth moments, two-sided Paley-Zygmund and the anti-concentration bound `P(σ² ≤ 4S²) ≥ 9/64` (`avg_pz_sum`, `avg_pz_zero_one`), the variance `p(1 - p)` of a `{0,1}` coordinate, Hoeffding's mgf bound `avg_exp_sum_le`, and `𝔼S² ≤ μ + μ²` for pairwise independent indicators (`avg_sq_sum_le_of_pairwise`) |
| `Chernoff` | Multiplicative Chernoff bounds (ratio and closed forms, mean replaced by any upper/lower bound) for independent, non-identical Bernoulli trials: on `independent` products, for biased coins `Distribution.bernoulli`, and for one uniform round (roadmap FND-3); for uniform rounds also the MGF bound, the tails for a free parameter `t` (`avg_chernoff_upper_of_mgf`, `avg_chernoff_lower_of_mgf`) and the forms `exp(k - μ - k log(k/μ))` |
| `Tail` | Markov's inequality, the one-round bound `1 - 𝔼[bad]` for `ofStep`, monotone occupation of absorbing events, strict bounds `𝔼f < 1`, the `log n` conversions |
| `Scalar` | Real and natural-number facts for round and phase counts: ceilings add up (`ceil_add_ceil_le`, `mul_ceil_le_ceil`, `nat_ceil_mul_le_of_le`), `n ≤ q ^ ⌈log n / log q⌉₊` (`le_pow_ceil`, `le_pow_ceil_real`), geometric and doubly exponential growth (`exists_lt_pow_mul`, `exists_le_two_pow_two_pow`), powers of `log` (`pow_three_le_of_log`, `log_cube_le`, `log_pow_four_div_le`, `half_le_log_one_add`), the failure budget `mul_one_div_sq_le` |
| `Phases` | Progress through nested phases (`nested_phases`, Lemma A.4 of Becchetti et al., SPAA 2014) |
| `DriftSeq` | Time-dependent chains (`iterateSeq`: kernel `K t` for the step `t → t + 1`), linearity and monotonicity |
| `Drift` | Drift theorems of Berenbrink et al. (ICALP 2016): drift `c/Ψ` ⇒ absorbed with probability `≥ 1/2` once `∑ c_t ≥ 4Ψ₀²` (`drift_absorption`, Lemma 2.2); multiplicative drift ⇒ survival `≤ ∏(1 − δ_t) Ψ₀/Ψ_min` (`multiplicative_drift`, Lemma 2.4); `_seq` forms for time-dependent chains |
| `GraphRounds` | Graph-indexed round types: `NeighborRound G` (every vertex samples a neighbour; independence and marginals) and `EdgeRound G` (one uniform oriented edge; edge, orientation and degree-bias averages) |
| `DriftHittingDefs` | Hitting probabilities `K.hitProb B n a = P_a(T_B ≤ n)` (visit `B` at one of the times `0, …, n`), through `trajectory` |
| `DriftHittingStop` | The stopped chain `K.stopped B`; `1 − hitProb` is its event `¬B`; geometric drift `K V ≤ ρ V` off `B` ⇒ `P(T_B > t) ≤ ρ^t V(a)/V_min` (`one_sub_hitProb_le_of_drift`, via `multiplicative_drift`) |
| `DriftHitting` | Hitting-time bound of Doerr et al. (SPAA 2011, Claim 2.9): growth by `c₁` except with probability `e^{−c₂X}` and escape from `0` with probability `c₃` ⇒ `X ≥ c₄ log q` within `c₅ log q + log_{c₁}(c₄ log q)` steps with probability `≥ 1 − q^{−c₆}` (`drift_hitting`; `O(log q)` form `drift_hitting_log`); `DriftHittingAux` holds the potential |
| `Spectral` | Mathlib's eigenbasis of a real symmetric matrix on plain vectors: orthonormality, expansion and Parseval (`dotProduct_eq_sum_eigenvectorBasis`), the coefficients of `Aᵗ z` (`eigenvectorBasis_dotProduct_pow_mulVec`), the spectral bound for powers (`pow_mulVec_dotProduct_self_le`); the random walk `transitionMatrix G d = A/d` of a `d`-regular graph, its sorted eigenvalues `walkEigenvalues` and `λ_G = max {λ₂, \|λₙ\|}` (`lambdaG`), the top eigenvector when `λ_G < 1` (`exists_top_eigenvectorBasis`), indicator vectors `indVec` |

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
`3-majority/` and `plurality/` use `avg` and `expList` from here, and `Bridge` connects them to
Mathlib's `Finset.expect`. Where the statements deviate from their sources, see
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).
3-majority retains its `ThreeMajority` probability names and blueprint links
through compatibility declarations: `ThreeMajority.avg` is a reducible alias of `avg`.
All concentration, tail and moment bounds of `median/`, `plurality/` and `3-majority/` live in
`Concentration`, `Chernoff`, `Tail` and `Moments`; the packages no longer keep local copies.
The scalar facts on ceilings, phase counts and logarithms that `median/`, `plurality/` and
`undecided/` proved locally live in `Scalar`.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
