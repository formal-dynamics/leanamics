# UND-3 progress: plurality consensus of the `k`-colour undecided-state dynamics

Source: Becchetti, Clementi, Natale, Pasquale, Silvestri, *Plurality consensus in the gossip
model*, SODA 2015, arXiv:1407.2565, Theorem 11
(Section 3.6), with the model of Section 2 (Table 1, equations (3)-(4)) and the monochromatic
distance of Section 2.1.

## Status

**Done.** Phase 1 (pinning, commit `e7dbf43`) and phase 2 (proofs) complete. `lake build
Undecided` is warning-free, no `sorry`; the gate checks (re-run locally with the gate's own
`decl_text`) give `SPEC OK`, no forbidden token, changes only in `undecided/`;
`#print axioms` of all pinned theorems and of `plurality_explicit`: only `propext`,
`Classical.choice`, `Quot.sound` (also `python3 ../scripts/check_axioms.py`, 17 declarations,
`Audit.lean` extended). Blueprint section "Many colours (UND-3)" and README paragraph added.

## Pinned (frozen up to `:=`)

`undecided/Undecided/PluralityBasic.lean` (namespace `Undecided.Plurality`):
`Config n k := Fin n → Option (Fin k)` (`none` = undecided), `update` (Table 1, by pattern
matching: its frozen span runs into the docstring and signature of `step`, so do not edit
`step`'s docstring), `step`, `count`, `maxCount`, `md` (`md(c) = ∑ᵢ (cᵢ / c₁)²`), the defining
equations `step_apply`, `count_def`, `maxCount_def`, `md_def` (they freeze the definitions'
semantics), `md_eq_of_plurality`, `md_le_card`, `one_le_md` (paper's (1)),
`expected_count_some`, `expected_count_none` (paper's (3), (4)).
`undecided/Undecided/PluralityBinary.lean`: `opEquiv`, `step_two`, `foldl_two`, `count_two`
(the binary model of `Undecided.Basic` is the case `k = 2`).
`undecided/Undecided/Plurality.lean`: **`plurality_whp`** (the only `sorry`):
`∀ α > 0, ∃ C > 0, ∀ n, C ≤ log n → ∀ k, C k ≤ (n / log n)^{1/3} → ∀ x m, count x none = 0 →
(∀ i ≠ m, (1 + α) cᵢ ≤ c_m) → 1 - C/n ≤ P(all nodes hold m after ⌈C · md x · log n⌉ rounds)`.

All pinned declarations except `plurality_whp` were proved in phase 1; `plurality_whp` is proved
in phase 2 with `C = 10⁵ ((1 + α)²/α)²` (failure probability `≤ 6/n`, `plurality_explicit`).

## Proof route actually taken (constants are huge, `n ≥ e^C`)

Notation: `c = c_m`, `q` undecided, `S = n - q - c = ∑_{j≠m} cⱼ`, `µᵢ = cᵢ(cᵢ+2q)/n`,
`µ_q = (q² + (n-q)² - ∑ cⱼ²)/n`, `µ_S = n - µ_q - µ_m = ∑_{j≠m} µⱼ`, `ℓ = 3 log n`,
`dev µ = √(3ℓ(µ+2ℓ))`, `θ = 1/(1+α)`, `κ = 1 - θ`, `K = 1/(θκ) = (1+α)²/α ≥ 4`,
`B = 2 md(x₀)`, `Φ = µ_m = c(c+2q)/n`.

1. **Concentration** (`PluralityConc.lean`): for a sum of independent `{0,1}` coordinates with
   mean `µ`, `P(X ≥ µ + dev µ) ≤ e^{-ℓ}` and `P(X ≤ µ - dev µ) ≤ e^{-ℓ}` (Bernstein,
   `Dynamics.avg_bernstein`, `σ² = µ + 2ℓ`, `λ = √(3ℓσ²)`).
2. **Good round** (`PluralityRound.lean`): `Good x y` = all `cᵢ(y) ≤ µᵢ + dev`, `c_m(y) ≥ µ_m -
   dev`, `S(y) ≤ µ_S + dev`, `|q(y) - µ_q| ≤ dev`; a bad round has probability
   `≤ (k + 4) e^{-ℓ} = (k+4)/n³`.
3. **Invariant** `Inv`: `cᵢ + 12√(ℓc) ≤ θc` (all `i ≠ m`) and `S + 12B√(ℓc) ≤ Bc`. Kept by a good
   round when `Φ ≥ φ₀ := n/(2k²) ≥ 1024K²ℓ`: generic threshold lemma for `X ∈ {cᵢ, S}`, `t ∈
   {θ, B}`, three cases: zone A (`X ≤ tc/2`), growth (`n - q < n/20`, so `µ_m ≥ 16c/9`), drift
   (`n - q ≥ n/20`, so `c ≥ n/(20(1+B))`, and the deterministic drift
   `X µ_m - µ_X c ≥ (t/2) κ c³/n` beats `dev`; needs `θ²κ²c³ ≥ 2048 n² ℓ`, i.e.
   `n ≥ 4.5·10⁸ K² k³ ℓ`: **this is where `C k ≤ (n/log n)^{1/3}` is used**).
4. **Progress**: identity `µ_m + 2µ_q = n + (n-c-2q)²/n + 2∑ⱼ cⱼ(c - cⱼ)/n` and
   `∑ⱼ cⱼ(c-cⱼ) ≥ κcS`. Outside `Fψ := {4S + q ≤ n/10}`: `Φ' ≥ (1 + η₀/2) Φ`, `η₀ = κ/(4000B)`
   (if `Φ < n/(8(1+B))` then `(1 - g)² ≥ 1/4`; else `η ≥ η₀`).
5. **Stages**: round 1 from `x₀` (`q = 0`) into `Inv ∩ {Φ ≥ φ₀}`; then `T₂` rounds through
   `G t = (Inv ∩ {Φ ≥ φ₀ λ^t}) ∪ Fψ`, `λ = 1 + η₀/2`, `G T₂ ⊆ Fψ` once `φ₀ λ^T₂ > n`
   (`Dynamics.expList_escape`); final `T₃ = ⌈8 log n⌉` rounds: `E[4S'+q'] ≤ 3/4 (4S+q)` on `Fψ`
   and `Fψ` is kept by a good round (UND-1's `fin_stage` pattern).
6. **Assembly**: `T = 1 + T₂ + T₃ ≤ C md log n`, failure `≤ T (k+4)/n³ + (3/4)^T₃ n/10 ≤ 6/n`,
   `C = 10⁵ K²`; pad to `⌈C md log n⌉` rounds by absorption.

## Proved (files, lines, main lemmas)

| file | lines | contents |
| --- | --- | --- |
| `PluralityConc.lean` | 139 | `dev ℓ µ = √(3ℓ(µ+2ℓ))`, `dev_le`; two-sided Bernstein for sums of independent indicators: `tail_up`, `tail_down` (from `Dynamics.avg_bernstein`) |
| `PluralityRound.lean` | 237 | real counts `cnt`, `und`, `oth`; means `mu`, `muU`, `muS`; `Good`; `oth_eq_sum`, `muS_eq_sum`; **`bad_le`**: a bad round has probability `≤ (k+4)e^{-ℓ}` |
| `PluralityAlg.lean` | 178 | `cnt_mu_sub` (ratio drift), `oth_mu_sub_ge`, `muS_le`, `muU_le`, `mu_add_two_muU` (Lemma 1 identity), `W_eq`, `W_ge` |
| `PluralityArith.lean` | 217 | pure reals: `thr_mono`, **`thr_step`**, `key_ratio`, `key_growth`, `key_drift`, `phi_next`, `sq_gap_of_small`, `gap_nonfinal`, `fpsi_expect`, `fpsi_keep` |
| `PluralitySteps.lean` | 302 | `Inv`, `Fpsi`, `Hyp` (numerical conditions), `thr_cases`, `drift_big`, `col_step`, `oth_step`, **`inv_step`** |
| `PluralityProgress.lean` | 275 | **`phi_step`**, **`fpsi_step`**, `muS_first` (`µ_S = (md - 1)µ_m` at `q = 0`), **`first_step`** |
| `PluralityStages.lean` | 303 | `miss`, `miss_comp` (Markov property), `miss_allM_antitone`, `round_le`, `Gset`, **`main_stage`** (via `Dynamics.expList_escape`), `Gset_sub`, `psi`, **`fin_stage`** |
| `PluralityAssembly.lean` | 482 | constants (`K_ge_four`, `theta_kappa`, `inv_kappa_le`), `hyp_h1`-`hyp_h5`, `T₂_le`, `T3_bound`, `p_bound`, `rounds_bound`, `Cmd_le`, `stage_bound`, `start_facts`, **`plurality_explicit`**, `prob_allM_eq`, `cube_of_rpow` |
| `Plurality.lean` | 75 | **`plurality_whp`** (pinned) |

Reusable pieces: `tail_up`/`tail_down` (multiplicative concentration for any count of a
synchronous `K_n` round; could move to `dynamics/`), `miss`/`miss_comp` (phase composition, now
duplicated from UND-1's `missP` for the `k`-colour step; a generic version over any
`step : S → R → S` would serve both), the state-dependent threshold `X + σ√(ℓc) ≤ tc` with
`thr_step` (replaces accumulated multiplicative errors in ratio arguments), the potential
`Φ = c(c + 2q)/n` with `mu_add_two_muU`. Reused from UND-1: `Undecided.le_pow_ceil`,
`Undecided.expList_one_sub`.

## Errors / pitfalls seen

* The statement gate freezes each pinned declaration from its keyword to the first
  line containing `:=`; definition bodies after `:=` are not frozen, hence the pinned defining
  equations `step_apply`, `count_def`, `maxCount_def`, `md_def`.
* `µ` (micro sign U+00B5) is not a Lean identifier character; use `μ` (U+03BC). `λ` is a keyword
  (no `hλ`), `c₋` is not an identifier.
* `maxHeartbeats` is per declaration: a long assembly proof with many `nlinarith` calls times out
  even if each step is fast; split into lemmas with small contexts (`hyp_h1`...`hyp_h5`,
  `stage_bound`, `Cmd_le`), and give `linarith` explicit products.
* Field notation (`hx.col_le`) does not work for `hx : x ∈ Inv ...` (a set membership).
* `rw [mu_next]` rewrites the first `mu _ _` it finds; give the arguments.
* `Real.sqrt_mul` and `← log_pow` patterns: state the target form with `show`/`have e : ... = ...`.
* `Nat.ceil` of a `ℕ`-cast inside `log`: define the number of rounds with the real expression
  and transport `le_pow_ceil` with a cast lemma (`cast_four_sq`).

## Deviations from the paper

1. **Range of `k`: `C k ≤ (n / log n)^{1/3}` with `C = C(α)`, i.e. the paper's exponent with a
   sufficiently small constant, instead of `k = O((n / log n)^{1/3})` with an arbitrary
   constant.** Reasons: (a) the proof of Theorem 11 invokes Lemma 10, which assumes
   `k = O((n / log n)^{1/4})`, so the paper's own proof does not cover its stated range;
   (b) the paper's route bounds the ratios `Cᵢ/C₁` (Lemma 2) and `R(C)` round by round w.h.p.;
   in the plateau `c₁ ≈ n/(2 md)`, the ratio's drift per round is `≈ α/(2 md)` and its one-round
   w.h.p. fluctuation `≈ √(md log n / n)`, so the per-round argument closes iff
   `md^{3/2} ≲ α √(n / log n)`, i.e. `k ≤ ε(α) (n / log n)^{1/3}`; an arbitrary constant would
   need multi-round (martingale) concentration, which neither the paper nor `dynamics/` has;
   (c) simulations (count-level, exact law) at `n = 10⁵, 10⁶`, `k = ⌊(n/log n)^{1/3}⌋`,
   `α = 0.05`: the plurality wins only 2-7 of 20 runs (with `α = 0.2`: 12-20 of 20), while
   with `k ≤ 10` it wins 40/40, always within `0.63 md log n` rounds; (d) the pinned range
   contains `k = O((n / log n)^{1/4})` with any constant once `n` is large, i.e. the range the
   paper's proof (Lemma 10) actually assumes.
2. **Explicit w.h.p.**: `log n ≥ C`, `⌈C md(x) log n⌉` rounds, probability `≥ 1 - C/n` (the paper:
   `O(md(c̄) log n)` and `1 - n^{-Θ(1)}`). The exponent `1` is reachable: every expectation used
   is `≥ n^{1/3}` polylog, and the end game uses an expectation contraction over `O(log n)`
   rounds instead of the paper's final Markov step (which only gives `O(log² n / n)`).
3. **"Within `T` rounds" = "at round `T`"**: monochromatic configurations are absorbing
   (`step_const`).
4. **Plurality colour named `m`** instead of sorting colours (`c₁ ≥ c₂ ≥ ...`); the bias
   hypothesis `(1 + α) cᵢ ≤ c_m` for all `i ≠ m` makes `m` the unique plurality.
5. **`k` is the palette size** (`Fin k`); colours may be absent; `k ≥ 2` is not assumed (`k ≤ 1`
   is trivial). The paper's standing assumption `c₁ > n/k` follows from the bias with `q = 0`.
6. **Sampling model**: uniform with replacement, possibly oneself, which gives exactly the
   paper's (3)-(4) (`expected_count_some`, `expected_count_none`, proved).
7. **`md`** is defined with `c₁ = maxCount x = maxᵢ cᵢ`; for configurations without any colour
   `md = 0` (Lean's `x / 0 = 0`), irrelevant for the theorem.
8. **Finite probability**: probabilities are `expList` expectations over i.i.d. uniform rounds.
9. **Not pinned**: Theorem 8 (the `Ω(md(c̄))` lower bound) and Section 4 (expanders), outside
   the UND-3 target.
10. **Proof route** (phase 2): not the paper's Lemmas 1-10 verbatim; see "Plan": a single
    invariant with state-dependent slack `12√(ℓ c_m)` replaces Lemma 2's accumulated errors, and
    the potential `Φ = c(c+2q)/n` replaces the two-step use of Lemma 1 / Lemma 9.
