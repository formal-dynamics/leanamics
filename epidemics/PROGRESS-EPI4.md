# EPI-4: COBRA cover time on expanders (progress)

Source: C. Cooper, T. Radzik, N. Rivera, *The coalescing-branching random walk on expanders and
the dual epidemic process*, PODC 2016, arXiv:1602.05768 (v2, 23 May 2016). The duality
(Theorem 4, equation (2)) is already formalized in `Cobra*.lean` (`cobra_bips_duality`,
`cobra_bips_duality_singleton`, `cobra_hit_iff_bips_reverse`). This file tracks the cover-time
part (Theorems 1 to 3) and its lemmas.

Status: **all pinned statements are proved** (Lemmas 1 to 4, Theorems 1 to 3, Corollary 1 and
the duality for branching factor `1 + ρ`). `lake build Epidemics` succeeds without warnings and
`python3 ../scripts/check_axioms.py` reports only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) for the pinned theorems and the main new lemmas listed in
`Audit.lean`. Lemmas 1 to 4 and the generic phase engine were proved by a first agent (Grok, run
interrupted); a second agent (Claude) generalized its BIPS chain, proved Theorems 1 to 3 and
restored `Choices` in `Cobra.lean` to a `def` (the first agent had made it an `abbrev`; the file
is now identical to the pin commit).
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
9. **Restarting (equation (1)), proof route.** The paper restarts COBRA after `T` steps "with any
   of the existing particles". The formal proof restarts from the whole current set `C_s`: the
   cover bound `P(⋃_{t=1}^{T₀+1} C_t ≠ V) ≤ n ε` holds from every nonempty start set (only
   `C₁ ≠ ∅` is used), so `P(cov > s + T₀ + 1) ≤ n ε P(cov > s)` and, with `n ε ≤ 1/2`, every tail
   sum is at most `2 (T₀ + 1)`. For BIPS, the process from a state `A ∋ v` dominates the one from
   `{v}` (monotonicity, persistent source), so `P(A_{s+T₀} ≠ V) ≤ P(A_s ≠ V)/2`.
10. **Theorem 3, proof route.** "The proof of Theorem 3 follows from the proof of Theorem 1, by
   using Corollary 1" is made precise by proving Lemmas 2 to 4, their chaining and the COBRA
   union bound for an abstract growth rate `c` (`GrowthProcess`), then using
   `c = min 1 (ρ₀ (1 - max λ₀ 0)) ≤ (p/q)(1 - λ²)` for the coin processes. The MGF bound (12)
   for the coin processes uses the same independence across vertices, after regrouping a round
   by vertex.

## Duplication to move to `dynamics/` later

`transitionMatrix`, `transitionMatrix_isHermitian`, `walkEigenvalues`, `lambdaG`, `lambdaG_nonneg`
are copies of the `Median` declarations of the same names (median package,
`Median/ExpanderDefs.lean`, `Median/ExpanderMixing.lean`); the spectral part of
`sum_sq_neighbor_le` reuses the eigenbasis argument of `Median.mixing_transition` and of
`Averaging.mulVec_dotProduct_mulVec_le` (averaging package). The epidemics package depends only on
`dynamics`, so these are restated here; they should move to `dynamics/` and be shared. The
eigenbasis lemmas in `CobraCoverSpectral.lean` (`sum_eigvec_mul_eigvec`,
`dotProduct_eq_sum_eigvec`, `eigvec_dotProduct_mulVec`, `dotProduct_mulVec_eq_sum_eigvec`,
`indVec`, `indVec_dotProduct_self`, `one_dotProduct_indVec`, `transitionMatrix_mulVec_one`,
`abs_eigenvalues_le_lambdaG`) are copies of `Median.mixing_transition` and its helpers
(`Median/ExpanderMixing.lean`), renamed into the `Epidemics` namespace.

Inside the package, `avg_pi_prod`/`avg_pi_eval`/`pi_count_mgf_le` (any dependent product) and
`avg_lower_tail_of_mgf` (any observable) generalize `avg_choices_prod`/`avg_choices_depends`/
`bips_mgf_le` and `bips_chernoff_lower`; the generic round lemmas (`roundRun`, `round_first_hit`,
`sum_range_shift_le`, `GrowthProcess`) are candidates for `dynamics/` as well.

## Proof architecture (files, line counts, main lemmas)

| File | Lines | Content |
| --- | --- | --- |
| `CobraCoverSpectral.lean` | 400 | pinned definitions, copies of the `Median` eigenbasis lemmas, `sum_sq_neighbor_le` (Lemma 1, (6)–(7)) |
| `CobraCoverRound.lean` | 202 | one BIPS round: independence over `Choices G k` (`avg_choices_prod`, `avg_choices_depends`), infection probability `1 - (1 - P_u)^k` (`bips_infect_prob`), `E|A'| = ∑_u P(u ∈ A')` |
| `CobraCoverGrowth.lean` | 291 | Lemma 1 (`bips_expected_growth`), MGF (`bips_mgf_le`), Chernoff lower tail (`bips_chernoff_lower`) |
| `CobraCoverNumerics.lean` | 437 | real-number estimates of Lemmas 2 to 4 (`log (1 + x) ≤ x - x²/3`, `(1 + c/23)^T ≥ n`, end-phase tail) |
| `CobraCoverEngine.lean` | 367 | generic round-driven process `roundRun step`, Lemma 2 for any growth rate `c` (`round_small_phase`) |
| `CobraCoverEngineLarge.lean` | 392 | Lemma 3 for any `c` (`round_large_phase`, stopped step + `Dynamics.expList_escape`) |
| `CobraCoverEngineEnd.lean` | 466 | Lemma 4 for any `c` (`round_end_phase`: staying above `9n/10`, healthy-vertex recursion) |
| `CobraCoverSmall.lean`, `CobraCoverLarge.lean` | 71, 144 | pinned Lemmas 2 to 4 (instances of the engine with `c = 1 - λ`) |
| `CobraCoverChain.lean` | 251 | first-hit chaining (`round_first_hit`), geometric tail sums (`sum_range_shift_le`) |
| `CobraCoverSchedule.lean` | 268 | phase lengths: `T₁ + T₂ + T₃ ≤ 60000 log n/c³` under `c ≥ 128 √(log n/n)` (`phase_schedule`) |
| `CobraCoverPhases.lean` | 317 | `GrowthProcess step src c` (hypotheses (H1)–(H5)), `avg_lower_tail_of_mgf`, the three phases chained (`GrowthProcess.fail_le`: failure `≤ 3/n³` after `60000 log n/c³` rounds), restarting (`GrowthProcess.tail_sum_le_log`: tail sums `≤ 130000 log n/c³`) |
| `CobraCoverUnion.lean` | 277 | from BIPS to COBRA for any dual pair: union bound and first-round split (`cover_fail_le`, `cover_fail_le_log`: `≤ 3/n²` after `60002 log n/c³` rounds), restarting COBRA from `C_s` (`cover_tail_sum_le`, `cover_tail_sum_le_log`) |
| `CobraCoverBips.lean` | 57 | BIPS is a `GrowthProcess` with `c = 1 - λ` (`bips_growthProcess`), `growth_of_rate_le` |
| `CobraCover.lean` | 127 | pinned Theorems 1 and 2 (`C₀ = 128`) |
| `CobraCoverIndep.lean` | 95 | independence over a dependent pi type (`avg_pi_prod`, `avg_pi_eval`), MGF of a count of independent events (`pi_count_mgf_le`) |
| `CobraCoverTargets.lean` | 167 | COBRA/BIPS with target sets `tg ρ x` (`tgtCobraStep`, `tgtBipsStep`): pathwise duality and Theorem 4 (`tgt_duality`), MGF and expected size for independent targets |
| `CobraCoverCoin.lean` | 197 | the coin round regrouped by vertex (`coinEquiv`, `coinTgt`), infection probability `(1 + ρ) P - ρ P²` (`coin_hit_prob`), Corollary 1 (`coin_expected_growth`), rate and `N` of Theorem 3 (`coin_rate`, `exists_gap_N`) |
| `CobraCoverBranching.lean` | 208 | pinned coin definitions, `cobraCoin_bips_duality`, Corollary 1, `bipsCoin_growthProcess`, Theorem 3 |

Main idea of the second part: everything after Lemma 1 only uses (H1)–(H5), so the chain of
Lemmas 2 to 4 (`GrowthProcess.fail_le`) and the COBRA union bound/restart (`cover_*`) are proved
once for an abstract process and instantiated twice: BIPS with `c = 1 - λ` (Theorems 1 and 2) and
BIPS with branching factor `1 + p/q` with `c = min 1 (ρ₀ (1 - max λ₀ 0))` (Theorem 3). The coin
processes are target-set processes by definition (`cobraCoinStep p = tgtCobraStep (coinTargets
p)`), so their duality is `tgt_duality`; their independence across vertices goes through the
equivalence `coinEquiv : Choices G 2 × (V → Fin q) ≃ (u : V) → (Fin 2 → N(u)) × Fin q`.

Constants obtained: Theorem 2: `C₀ = 128`, `C = 60000` (probability; the proof gives `3/n³`) and
`C = 130000` (expectation). Theorem 1: `C₀ = 128`, `C = 60002` (probability; the proof gives
`3/n²`) and `C = 130000` (expectation). Theorem 3 and `bipsCoin_infection_time`: with
`c = min 1 (ρ₀ (1 - max λ₀ 0))`, `C = 60000/c³`, `60002/c³`, `130000/c³` and
`N = ⌈(32768/c²)²⌉₊ + 2` (so that `128 √(log n/n) ≤ c` for `n ≥ N`).

## Remaining

Nothing: no `sorry` in `epidemics/`. Current errors: none.
