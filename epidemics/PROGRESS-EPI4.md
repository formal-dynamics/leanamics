# EPI-4: COBRA cover time on expanders (progress)

Source: C. Cooper, T. Radzik, N. Rivera, *The coalescing-branching random walk on expanders and
the dual epidemic process*, PODC 2016, arXiv:1602.05768 (v2, 23 May 2016). The duality
(Theorem 4, equation (2)) is already formalized in `Cobra*.lean` (`cobra_bips_duality`,
`cobra_bips_duality_singleton`, `cobra_hit_iff_bips_reverse`). This file tracks the cover-time
part (Theorems 1 to 3) and its lemmas.

Status: **Lemmas 1 to 4 are proved** (`sum_sq_neighbor_le`, `bips_expected_growth`, `bips_mgf_le`,
`bips_chernoff_lower`, `bips_small_phase`, `bips_large_phase`, `bips_end_phase`), by a generic
round-driven engine (`round_small_phase`, `round_large_phase`, `round_end_phase`) with growth
constant `c = 1 - λ` (using `1 - λ ≤ 1 - λ²`). Theorems 1 to 3 are still `sorry`. The spectral
eigenbasis lemmas in `CobraCoverSpectral.lean` (`sum_eigvec_mul_eigvec`,
`dotProduct_eq_sum_eigvec`, `eigvec_dotProduct_mulVec`, `dotProduct_mulVec_eq_sum_eigvec`,
`indVec`, `indVec_dotProduct_self`, `one_dotProduct_indVec`, `transitionMatrix_mulVec_one`,
`abs_eigenvalues_le_lambdaG`) are copies of `Median.mixing_transition` and its helpers, for a
later move to `dynamics/`. `Choices` in `Cobra.lean` is an `abbrev` (it was a `def`).
The pinned statements were reviewed by a second agent (faithfulness to the paper, quantifier
order, casts, vacuity, small-`n` edge cases, numerical checks of Lemmas 1 to 4 and of the coin
model); no statement changes were needed.

## Pinned statements

Notation: `G` is `r`-regular with `r > 0`, `n = |V|`, `λ = lambdaG G r = max {λ₂, |λₙ|}` for the
eigenvalues of `P = A/r`, BIPS with source `v` runs along i.i.d. uniform rounds
(`Choices G k`: every vertex samples `k` neighbours with replacement), probabilities are
`Dynamics.expList` averages of indicators, `log` is the natural logarithm.

| Declaration | File | Paper | Statement |
| --- | --- | --- | --- |
| `transitionMatrix`, `walkEigenvalues`, `lambdaG` | `CobraCoverSpectral` | Section 1 | `P = A/r`, its sorted eigenvalues, `λ = max {λ₂, |λₙ|}` (copies of the `Median` definitions) |
| `sum_sq_neighbor_le` | `CobraCoverSpectral` | proof of Lemma 1, (6)–(7) | `∑ₓ (d_A(x)/r)² ≤ λ² |A| + (1 − λ²) |A|²/n` |
| `bips_expected_growth` | `CobraCoverGrowth` | Lemma 1 | `k ≥ 2`: `E|A'| ≥ |A| (1 + (1 − λ²)(1 − |A|/n))` for every set `A` |
| `bips_mgf_le` | `CobraCoverGrowth` | (12) in Lemma 2 | `E e^{−φ|A'|} ≤ exp(−(1 − e^{−φ}) E|A'|)` for every real `φ` |
| `bips_chernoff_lower` | `CobraCoverGrowth` | (18), Lemma 4 | `μ ≤ E|A'|`, `0 < δ < 1`: `P(|A'| ≤ (1 − δ)μ) ≤ exp(−δ²μ/2)` |
| `bips_small_phase` | `CobraCoverSmall` | Lemma 2 | `λ < 1`, `2m ≤ n`, `T ≥ 13m/(1−λ) + 24 C log n/(1−λ)²`: `P(|A_s| ≤ m ∀ s ≤ T ∣ A₀ = {v}) ≤ n^{−C}` |
| `bips_large_phase` | `CobraCoverLarge` | Lemma 3 | `|A₀| ≥ 4000 log n/(1−λ)²`, `T ≥ 24 log n/(1−λ)`: `P(10|A_s| < 9n ∀ s ≤ T) ≤ T/n⁵` |
| `bips_end_phase` | `CobraCoverLarge` | Lemma 4 | `4000 log n/(1−λ)² ≤ 9n/10`, `10|A₀| ≥ 9n`, `T ≥ 8 log n/(1−λ)`: `P(A_T ≠ V) ≤ n^{−5}` |
| `bips_infection_time` | `CobraCover` | Theorem 2 (w.h.p.) | `∃ C₀ C`: if `1 − λ ≥ C₀ √(log n/n)`, `k ≥ 2`, `T ≥ C log n/(1−λ)³`, then `P(A_T ≠ V ∣ A₀ = {v}) ≤ C/n³` |
| `bips_infection_time_expectation` | `CobraCover` | Theorem 2 (expectation) | same hypotheses: `∑_{s<H} P(A_s ≠ V) ≤ C log n/(1−λ)³` for every `H` |
| `cobra_cover_time` | `CobraCover` | Theorem 1 (w.h.p.) | same hypotheses: `P(⋃_{t=1}^T C_t ≠ V ∣ C₀ = {u}) ≤ C/n²` |
| `cobra_cover_time_expectation` | `CobraCover` | Theorem 1 (expectation), (1) | `∑_{s<H} P(⋃_{t=1}^s C_t ≠ V) ≤ C log n/(1−λ)³` for every `H` |
| `CoinChoices`, `coinTargets`, `cobraCoinStep`, `cobraCoinRun`, `bipsCoinStep`, `bipsCoinRun` | `CobraCoverBranching` | Theorem 3, Corollary 1 | COBRA and BIPS with branching factor `1 + p/q` (second sample used iff a uniform coin in `Fin q` is `< p`) |
| `cobraCoin_bips_duality` | `CobraCoverBranching` | Theorem 4 for `1 + ρ` | `P(Hit_C(v) > t) = P(C ∩ A_t = ∅ ∣ A₀ = {v})` for the coin processes |
| `bipsCoin_expected_growth` | `CobraCoverBranching` | Corollary 1 | `E|A'| ≥ |A| (1 + (p/q)(1 − λ²)(1 − |A|/n))` |
| `bipsCoin_infection_time` | `CobraCoverBranching` | Theorem 2 for `1 + ρ` | `λ ≤ λ₀ < 1`, `p/q ≥ ρ₀ > 0` constants: `∃ C N`, for `n ≥ N`, `T ≥ C log n`: `P(A_T ≠ V) ≤ C/n³` |
| `cobra_cover_time_branching` | `CobraCoverBranching` | Theorem 3 (w.h.p.) | same: `P(⋃_{t=1}^T C_t ≠ V) ≤ C/n²` |
| `cobra_cover_time_branching_expectation` | `CobraCoverBranching` | Theorem 3 (expectation) | same: `∑_{s<H} P(cover time > s) ≤ C log n` |

`transitionMatrix_isHermitian` is proved and pinned (`walkEigenvalues` is built from it). Proved
helper lemmas (not pinned): `lambdaG_nonneg`, `source_mem_bipsStep`, `bipsStep_mono`,
`bipsStep_univ`.

## Deviations from the source

1. **Hypotheses dropped.** The paper assumes `G` connected and, in Theorems 1 and 2 and Lemmas 1
   to 4, `k = 2`. All statements hold for every `k ≥ 2` (Lemma 1 only needs
   `1 − (1 − p)^k ≥ 1 − (1 − p)²`, and Lemmas 2 to 4 only use Lemma 1, independence across
   vertices and monotonicity). Connectivity is implied by `λ < 1` (resp. by
   `1 − λ ≥ C₀ √(log n/n) > 0`) and is not assumed. Lemma 1, its spectral core and the one-round
   bounds hold for every regular graph and every infected set (not only sets containing `v`).
2. **`λ`.** The paper's `λ = max_{i ≥ 2} |λᵢ|` is written `max {λ₂, |λₙ|}` (equal since
   `λₙ ≤ λ₂`), as in `Median.lambdaG`; on graphs with fewer than two vertices it is `0`.
3. **Asymptotic notation.** "`1 − λ ≫ √(log n/n)`" is the paper's footnote form
   `1 − λ ≥ C₀ √(log n/n)` with `∃ C₀`; "`O(T)` w.h.p." is `∃ C`, failure probability
   `≤ C n^{−3}` (Theorem 2) or `≤ C n^{−2}` (Theorem 1, as derived in the paper's proof) for every
   number of rounds `≥ C T`. For Theorem 3 (constant `λ`, `ρ`) the constants depend on the bounds
   `λ₀ < 1`, `ρ₀ > 0` and the statements hold for `n ≥ N` (`∃ N`).
4. **Expectations.** `COV(u) = E cov(u)` and `INF(v) = E infec(v)` are expectations of unbounded
   times, not available in the finite layer. They are written through the tail sums
   `E τ = ∑_{s ≥ 0} P(τ > s)`: every partial sum `∑_{s < H} P(τ > s) = E min(τ, H)` is bounded by
   `C T`, uniformly in `H`. For BIPS, `infec(v) > s` iff `A_s ≠ V` since `V` is absorbing
   (`bipsStep_univ`).
5. **Cover time.** `cov(u) = min {T : ⋃_{t=1}^T C_t = V}` uses the times `1, …, T` (as in the
   paper's definition, so the start vertex must be revisited); the paper's proof uses
   `cov(u) = max_v Hit_u(v)`, which counts time `0`. The pinned statements follow the definition
   (slightly stronger); the extra step for the start vertex is one application of the duality from
   the first round's image.
6. **Explicit constants in the lemmas.** Lemma 2 is pinned with the paper's explicit `T` and the
   exact bound `n^{−C}` (the proof gives it; the paper writes `1 − O(n^{−C})`). Lemma 3: the
   paper's `23 log n/(1 − λ)` rounds come from "the infection doubles every `23/(1 − λ)` rounds",
   which gives `log₂ n` doublings, not `ln n` (needs a minor correction); the pinned version uses
   `24 log n/(1 − λ)` rounds, enough since `(1 + (1 − λ)/23)^T ≥ e^{T(1 − λ)/24}`, and keeps the
   union bound `T n^{−5}` instead of `n^{−4}`. Lemma 4: the paper's display (24) drops a factor
   `B₀ ≤ n/10` (`E B_T ≤ θ^T + …` should be `θ^T n/10 + …`) and switches from
   `T = 5 log n/log(1/θ)` to `6 log n/log(1/θ)` (minor corrections); with `6` the proof gives
   `n^{−5} + O(T² n^{−7})`, and with `T ≤ n` this is at most `n^{−5}`, the paper's statement.
   The paper's "`1 − λ ≫ √(log n/n)`" in Lemma 4 is the explicit condition
   `4000 log n/(1 − λ)² ≤ 9n/10` used in its proof.
7. **Proof of Theorem 2.** The paper applies Lemma 2 with `m = 4000 log n/(1 − λ²)`; Lemma 3 needs
   `|A| ≥ 4000 log n/(1 − λ)²`, so `m` should be `4000 log n/(1 − λ)²` (minor correction; this
   gives the `(1 − λ)^{−3}` of the theorem).
8. **Branching factor `1 + ρ` (Theorem 3).** The paper's coin of bias `ρ` is a uniform coin in
   `Fin q` compared with `p`, so `ρ = p/q` is rational: the finite uniform-round layer has no
   biased coins with irrational bias. Theorem 3 is stated for all `ρ = p/q ∈ [ρ₀, 1]`, which
   covers every constant `ρ ∈ (0, 1]` from below by rationals. The duality for these processes
   (`cobraCoin_bips_duality`) and the BIPS infection time (`bipsCoin_infection_time`) are pinned
   as intermediate steps ("the proof of Theorem 3 follows from the proof of Theorem 1, by using
   Corollary 1").

## Duplication to move to `dynamics/` later

`transitionMatrix`, `transitionMatrix_isHermitian`, `walkEigenvalues`, `lambdaG`, `lambdaG_nonneg`
are copies of the `Median` declarations of the same names (median package,
`Median/ExpanderDefs.lean`, `Median/ExpanderMixing.lean`); the spectral part of
`sum_sq_neighbor_le` reuses the eigenbasis argument of `Median.mixing_transition` and of
`Averaging.mulVec_dotProduct_mulVec_le` (averaging package). The epidemics package depends only on
`dynamics`, so these are restated here; they should move to `dynamics/` and be shared.

## Remaining

All pinned theorems (proofs `sorry`).
