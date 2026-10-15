# Dynamics

Shared finite probability and stochastic dynamics for Leanamics. This package
uses Lean 4.32.0 and Mathlib revision
`2d8c533bd0a0515caa32f18c0ab4485bd6229378`, exactly matching 3-majority.

| Module | API |
| --- | --- |
| `Equivalence` | `expList_eq_avg_ofFn`, the recursive `expList` is the uniform average over `Fin T → α` |
| `Distribution` | Normalized nonnegative real weights, expectations, event probabilities and their elementary bounds (monotonicity, complement, union bounds, inclusion–exclusion, Markov's inequality), uniform distributions, point masses, biased coins `bernoulli`, independent products, pushforward |
| `Uniform` | Finite averages, recursive uniform trajectory expectations, independence over finite dependent products (`avg_pi_prod`, `avg_pi_eval`) and of disjoint blocks of coordinates (`avg_pi_split`), reindexing; `expList` only sees lists of its length (`expList_le_of_length`, `expList_congr_length`) and splits into two phases (`expList_le_of_split`); extracted from 3-majority |
| `Independent` | Independent products `Distribution.independent`: resampling and conditioning on one coordinate (`independent_expect_update`, `independent_expect_eq_sum_update`, `independent_expect_fin_succ`), pairwise and block independence (`independent_expect_pair`, `expect_mul_of_dep`), second and third moments of centred sums, coordinatewise combination of independent families (`expect_expect_coord`) |
| `Adaptive` | Adaptive observation processes: histories `hist obs ω k` (the observation after the history `h` is `obs h ω`), `hist_eq_iff`; the product supermartingale lemma `Distribution.expect_prod_hist_le_one` (factors with conditional expectation at most `1` along the history have a product of expectation at most `1`) and its deferred-decisions form for fresh observations of an independent family, `Distribution.expect_prod_hist_le_one_of_fresh` |
| `Bridge` | The three expectation APIs agree: `avg` is Mathlib's `𝔼 a, f a` (`avg_eq_expect`), the product of uniform laws is uniform (`Distribution.independent_uniform_expect`), and `expList` is the expectation over `T` i.i.d. draws in Mathlib's and in the distribution form (`expList_eq_expect`, `expList_eq_independent_expect`) |
| `Kernel` | Finite stochastic kernels, finite-time expectations (linear, with complements `iterate_const_sub`), events, stationarity, harmonic observables and their affine images (`harmonic_affine`); the transition matrix `toMatrix` (row stochastic, `iterate n f = toMatrix ^ n *ᵥ f`) |
| `BridgePMF` | `Distribution` as Mathlib's `PMF` (`Distribution.toPMF`, compatible with `PMF.uniformOfFintype`, `PMF.pure`, `PMF.map`): `expect` is the integral and `prob` the measure under `toPMF.toMeasure` (`expect_eq_integral`, `prob_eq_toMeasure`), `independent` is `Measure.pi` (`toMeasure_independent`) with `iIndepFun` coordinates (`iIndepFun_independent`), and Hoeffding's inequality for bounded, non-identical independent coordinates derived from Mathlib's (`Distribution.hoeffding`) |
| `Trajectory` | Weighted history/endpoint expectations and agreement with kernel iteration |
| `Stationary` | Stationary-distribution existence by Cesàro averages and compactness of the finite simplex |
| `Absorption` | Uniform absorption blocks, geometric survival bounds, convergence to zero; access from reachability along transitions of positive probability (`exists_iterate_lt_one_of_reachable`) |
| `Consensus` | The non-consensus indicator `nonConsensus` on configurations `V → C` (the survival indicator of the voter, Moran and undecided-state packages), its one-step bound when consensus is absorbing (`Kernel.nonConsensus_step`), its event form for two colours, the gambler's ruin formula `(φ(s) − φ(all-false))/(φ(all-true) − φ(all-false))` for the fixation probability in all-`true` from a harmonic `φ` (`Kernel.iSup_consensus_of_harmonic`), and its normalized form `Kernel.iSup_consensus_of_invariant` |
| `OptionalStopping` | Finite-horizon optional stopping (roadmap FND-4): a conserved observable, constant on two target events, gives the finite-time error bound `event_error_of_invariant`, the limit `tendsto_event_of_invariant` and the absorption probability `iSup_event_of_invariant` = `(φ(x₀) − φB)/(φA − φB)` |
| `Rounds` | The kernel `ofStep` of a process driven by i.i.d. uniform rounds, its agreement with `expList`, `expList_escape` (union bound over rounds for a moving target), and the probability `missProb step B T s` of being outside `B` after `T` rounds (monotone in `B`, composition of stages `missProb_comp` by the Markov property, antitone in `T` for a closed target, amplification `p ↦ p^k` over `k` blocks for a closed target `missProb_amplify`) |
| `Reverse` | Time reversal of i.i.d. rounds (roadmap FND-6): `expList_comp_reverse`, and `iterate_ofStep_foldr` (round-based kernels applied last round first) |
| `Concentration` | Hoeffding's and Bernstein's inequalities (both tails) for sums of independent coordinates, for `{0,1}` coordinates each Bernstein tail beyond `√(3ℓ(μ + 2ℓ))` at most `e^{-ℓ}` (`avg_bernstein_of_zero_one`, `avg_bernstein_lower_of_zero_one`), and the bounds `0 ≤ p ≤ 1`, `p(1 - p) ≤ p` for a `{0,1}` coordinate |
| `Moments` | Moments of sums of independent coordinates: Cauchy-Schwarz for `avg` (Mathlib's `Finset.expect_mul_sq_le_sq_mul_sq`), second and fourth moments, one-sided Paley-Zygmund `P(X > θ𝔼X) ≥ (1 - θ)²(𝔼X)²/𝔼X²` (`avg_pz_one_sided`), two-sided Paley-Zygmund and the anti-concentration bound `P(σ² ≤ 4S²) ≥ 9/64` (`avg_pz_sum`, `avg_pz_zero_one`), the variance `p(1 - p)` of a `{0,1}` coordinate, Hoeffding's mgf bound `avg_exp_sum_le`, and `𝔼S² ≤ μ + μ²` for pairwise independent indicators (`avg_sq_sum_le_of_pairwise`) |
| `Chernoff` | Multiplicative Chernoff bounds (ratio and closed forms, mean replaced by any upper/lower bound) for independent, non-identical Bernoulli trials: on `independent` products, for biased coins `Distribution.bernoulli`, and for one uniform round (roadmap FND-3); for uniform rounds also the MGF bound, the tails for a free parameter `t` (`avg_chernoff_upper_of_mgf`, `avg_chernoff_lower_of_mgf`) and the forms `exp(k - μ - k log(k/μ))`; on `independent` products also the upper tail at a fixed tilt `ε` (`Distribution.prob_ge_le_exp_tilt`, in `ChernoffAux`); for biased coins also the MGF of a weighted count of heads (`independent_bernoulli_expect_exp_sum`); for identical coins the binomial tail `Distribution.binTail` with its one-step recursion and the conditioning on one coin (`independent_bernoulli_prob_split`) |
| `Azuma` | Martingales along i.i.d. uniform rounds: the partial sums `incrementSum` of state-dependent increments (linear and monotone in the increments), the exponential supermartingale bound `𝔼[exp(incrementSum) · F(state)] ≤ F(x)` (`expList_exp_incrementSum_le`), Hoeffding's lemma for a uniform draw (`avg_exp_mul_le`), Ville's maximal inequality (`expList_ville`) and the maximal Azuma–Hoeffding inequality `P(∃ k ≤ n, M_k ≥ λ) ≤ exp(-λ²/(2 n c²))` (`expList_azuma`) |
| `Tail` | Markov's inequality, the one-round bound `1 - 𝔼[bad]` for `ofStep`, monotone occupation of absorbing events, strict bounds `𝔼f < 1`, the `log n` conversions |
| `Scalar` | Real and natural-number facts for round and phase counts: ceilings add up (`ceil_add_ceil_le`, `mul_ceil_le_ceil`, `nat_ceil_mul_le_of_le`), `n ≤ q ^ ⌈log n / log q⌉₊` (`le_pow_ceil`, `le_pow_ceil_real`), geometric and doubly exponential growth (`exists_lt_pow_mul`, `exists_le_two_pow_two_pow`), powers of `log` (`pow_three_le_of_log`, `log_cube_le`, `log_pow_four_div_le`, `half_le_log_one_add`), the failure budget `mul_one_div_sq_le`, `∏(1 − δ_t) ≤ exp(−∑ δ_t)` (`prod_one_sub_le_exp_neg_sum`) |
| `Phases` | Progress through nested phases (`nested_phases`, Lemma A.4 of Becchetti et al., SPAA 2014); phase calculus with the potential `λ^{J - phase}`: closed phases entered with probability `≥ 1 - q` per step ⇒ outside `A J` after `t` steps with probability `≤ (q + 1/λ)^t λ^J` (`iterate_outside_le_of_phases`) |
| `DriftSeq` | Time-dependent chains (`iterateSeq`: kernel `K t` for the step `t → t + 1`), linearity (also over finite sums) and monotonicity |
| `Drift` | Drift theorems of Berenbrink et al. (ICALP 2016): drift `c/Ψ` ⇒ absorbed with probability `≥ 1/2` once `∑ c_t ≥ 4Ψ₀²` (`drift_absorption`, Lemma 2.2); multiplicative drift ⇒ survival `≤ ∏(1 − δ_t) Ψ₀/Ψ_min` (`multiplicative_drift`, Lemma 2.4); `_seq` forms for time-dependent chains; exponential form `≤ exp(−∑ δ_t) Ψ₀/Ψ_min` (`multiplicative_drift_seq_exp`); fixed-time drift with an additive error, `K φ ≤ ρ φ + ε` ⇒ `K^T φ ≤ ρ^T φ + T ε` (`iterate_le_of_drift`, `expList_le_of_drift`); comparison and contraction on a region closed under the chain (`iterate_le_of_closed`, `iterate_le_pow_of_closed`) |
| `GraphRounds` | Graph-indexed round types: `NeighborRound G` (every vertex samples a neighbour; independence and marginals) and `EdgeRound G` (one uniform oriented edge; edge, orientation and degree-bias averages; on the complete graph, a uniform ordered pair of distinct vertices; the one-way protocol step `oneWayStep`) |
| `Lazy` | The lazy kernel `Kernel.lazy K = (I + K)/2`: entries and expectations, self-loop weight `≥ 1/2` (`lazy_weight_self_ge_half`), same support and same stationary distributions as `K` (`lazy_stationary_iff`) |
| `RandomWalk` | Random walks on a graph without isolated vertices: `Kernel.uniformNeighbor G hd = D⁻¹A` (support, neighbour-average expectation, `uniformNeighbor_expect_eq_avg` in the `avg` form) and the lazy walk `Kernel.lazyNeighbor G hd = (I + D⁻¹A)/2` |
| `DriftHittingDefs` | Hitting probabilities `K.hitProb B n a = P_a(T_B ≤ n)` (visit `B` at one of the times `0, …, n`), through `trajectory` |
| `DriftHittingStop` | The stopped chain `K.stopped B`; `1 − hitProb` is its event `¬B`; geometric drift `K V ≤ ρ V` off `B` ⇒ `P(T_B > t) ≤ ρ^t V(a)/V_min` (`one_sub_hitProb_le_of_drift`, via `multiplicative_drift`) |
| `DriftHitting` | Hitting-time bound of Doerr et al. (SPAA 2011, Claim 2.9): growth by `c₁` except with probability `e^{−c₂X}` and escape from `0` with probability `c₃` ⇒ `X ≥ c₄ log q` within `c₅ log q + log_{c₁}(c₄ log q)` steps with probability `≥ 1 − q^{−c₆}` (`drift_hitting`; `O(log q)` form `drift_hitting_log`); `DriftHittingAux` holds the potential |
| `Spectral` | Mathlib's eigenbasis of a real symmetric matrix on plain vectors: orthonormality, expansion and Parseval (`dotProduct_eq_sum_eigenvectorBasis`), the coefficients of `Aᵗ z` (`eigenvectorBasis_dotProduct_pow_mulVec`), the spectral bound for powers (`pow_mulVec_dotProduct_self_le`); the random walk `transitionMatrix G d = A/d` of a `d`-regular graph, its sorted eigenvalues `walkEigenvalues` and `λ_G = max {λ₂, \|λₙ\|}` (`lambdaG`), the top eigenvector when `λ_G < 1` (`exists_top_eigenvectorBasis`), indicator vectors `indVec` |
| `Hitting` | Facts about `hitProb`: bounds `0 ≤ hitProb ≤ 1`, monotone in the target and the horizon; hit `B` then reach an absorbing event (`hitProb_sub_le_event`, the strong Markov property at the hitting time, by induction); amplification of an absorbing event over two blocks (`event_amplify`) |
| `Perturbed` | Round-based processes perturbed by an adaptive adversary (`Perturbed`: each round is related by `Adm` to the unperturbed `step`, the perturbation may depend on all past rounds): fixed-time drift `𝔼 φ ≤ ρ^T φ + T ε` (`expList_le_of_drift_perturbed`), chains of one-round moves along a path of targets (`expList_path_perturbed`), and the failure indicator `failInd` of a proposition; extracted from median |

`avg` remains zero on an empty sample type. Normalized distributions require
mass one and therefore cannot inhabit an empty sample space; `uniform` requires
`Nonempty`. Weighted and uniform expectations agree on nonempty types.

The absorption API uses a zero-one survival indicator `f`. Its hypothesis
`K.apply f ≤ f` expresses absorption of the target `f = 0`, and
`∀ a, ∃ n, K.iterate n f a < 1` expresses positive-probability access; it follows from
a chain of transitions of positive probability to a state where `f` vanishes
(`exists_iterate_lt_one_of_reachable`, one step at a time by `iterate_succ_lt_one`).
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
Mathlib's `Finset.expect`; `BridgePMF` connects `Distribution` to Mathlib's `PMF` and measures. Where the statements deviate from their sources, see
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).
3-majority retains its `ThreeMajority` probability names and blueprint links
through compatibility declarations: `ThreeMajority.avg` is a reducible alias of `avg`.
The scalar facts on ceilings, phase counts and logarithms that `median/`, `plurality/` and
`undecided/` proved locally live in `Scalar`.
All concentration, tail and moment bounds of `median/`, `plurality/` and `3-majority/` live in
`Concentration`, `Chernoff`, `Tail` and `Moments`; the packages no longer keep local copies.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
