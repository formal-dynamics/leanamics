# PROGRESS: EPI-7 (Kermack–McKendrick SIR, deterministic ODE)

Source: `ROADMAP.md`, row EPI-7. Branch `epi7-kermack-mckendrick`.

References:

* W. O. Kermack, A. G. McKendrick, *A contribution to the mathematical theory of epidemics*,
  Proc. R. Soc. Lond. A 115 (1927) 700–721. No numbered theorems; the threshold and the final-size
  relation appear in the analysis of the constant-rate case.
* H. W. Hethcote, *The mathematics of infectious diseases*, SIAM Review 42 (2000) 599–653, §2.3:
  system (2.2) `ds/dt = -β i s`, `di/dt = β i s - γ i`, `r = 1 - s - i`, contact number
  `σ = β / γ`, and **Theorem 2.1**: if `σ s₀ ≤ 1` then `i(t)` decreases to 0; if `σ s₀ > 1` then
  `i(t)` first increases up to `i_max = i₀ + s₀ - 1/σ - ln(σ s₀)/σ`, then decreases to 0; `s(t)` is
  decreasing and `s∞` is the unique root in `(0, 1/σ)` of `i₀ + s₀ - s∞ + ln(s∞/s₀)/σ = 0`. This
  is the precise modern statement cited by the docstrings (text read from the PDF).

## Status

* **Phase 1 (pin statements): done.** `lake build Epidemics` succeeds; the only warnings are
  `declaration uses 'sorry'` (one per pinned theorem, 18).
* **Phase 2 (proofs, docs): done** (2026-10-07). All 18 pinned theorems are proved; no `sorry`,
  `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `set_option` in the package's
  new files. `lake build Epidemics` is warning-free. `#print axioms` (scratch file under `/tmp`,
  and `python3 ../scripts/check_axioms.py` on `Audit.lean`, 25 declarations) reports only
  `propext`, `Classical.choice`, `Quot.sound`. Pinned text is unchanged (checked against the
  phase-1 commit `205e6e5` by a script comparing docstring + text up to `:=`; the only removed
  lines in the pinned files are `sorry` lines and one `import`).

## Pinned (see `PINNED.txt` at the repository root; text up to `:=` is frozen)

All in `epidemics/Epidemics/`, namespace `Epidemics.KermackMcKendrick`, section variables
`{β γ : ℝ} {s i r : ℝ → ℝ}`; every theorem takes `(h : IsSolution β γ s i r)`.

| Declaration | File | Statement in words |
| --- | --- | --- |
| `R₀` (noncomputable def) | `KermackMcKendrickDefs.lean` | `R₀ β γ = β / γ` |
| `sirField` (def) | same | `(s, i, r) ↦ (-(β s i), β s i - γ i, γ i)` on `ℝ × ℝ × ℝ` |
| `IsSolution` (structure, Prop) | same | `0 < β`, `0 < γ`, `IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Set.Ici 0)`, `0 < s 0`, `0 < i 0`, `r 0 = 0`, `s 0 + i 0 + r 0 = 1` |
| `IsSolution.sum_eq_one` | `KermackMcKendrick.lean` | `0 ≤ t → s t + i t + r t = 1` |
| `IsSolution.s_pos` | same | `0 ≤ t → 0 < s t` |
| `IsSolution.i_pos` | same | `0 ≤ t → 0 < i t` |
| `IsSolution.r_nonneg` | same | `0 ≤ t → 0 ≤ r t` |
| `IsSolution.strictAntiOn_s` | same | `StrictAntiOn s (Set.Ici 0)` |
| `IsSolution.strictMonoOn_r` | same | `StrictMonoOn r (Set.Ici 0)` |
| `IsSolution.s_eq_mul_exp` | same | `0 ≤ t → s t = s 0 * exp (-(R₀ β γ * r t))` |
| `IsSolution.strictAntiOn_i` | same | `R₀ β γ * s 0 ≤ 1 → StrictAntiOn i (Set.Ici 0)` |
| `IsSolution.initially_increasing_iff` | same | `(∃ ε > 0, StrictMonoOn i (Set.Icc 0 ε)) ↔ 1 < R₀ β γ * s 0` |
| `IsSolution.tendsto_i` | `KermackMcKendrickLimits.lean` | `Tendsto i atTop (𝓝 0)` |
| `IsSolution.exists_tendsto_s` | same | `∃ sInfty, Tendsto s atTop (𝓝 sInfty)` |
| `IsSolution.tendsto_r` | same | `Tendsto s atTop (𝓝 sInfty) → Tendsto r atTop (𝓝 (1 - sInfty))` |
| `IsSolution.final_size` | same | `Tendsto s atTop (𝓝 sInfty) → sInfty = s 0 * exp (-(R₀ β γ * (1 - sInfty)))` |
| `IsSolution.limit_pos` | same | `Tendsto s atTop (𝓝 sInfty) → 0 < sInfty` |
| `IsSolution.R₀_mul_limit_lt_one` | same | `Tendsto s atTop (𝓝 sInfty) → R₀ β γ * sInfty < 1` |
| `IsSolution.final_size_unique` | same | `Tendsto s atTop (𝓝 sInfty) → 0 < x → R₀ β γ * x ≤ 1 → x = s 0 * exp (-(R₀ β γ * (1 - x))) → x = sInfty` |
| `IsSolution.final_size_unique_of_le_one` | same | same with `x ≤ 1` instead of `R₀ β γ * x ≤ 1` |
| `IsSolution.exists_peak` | `KermackMcKendrickPeak.lean` | `1 < R₀ β γ * s 0 → ∃ tmax > 0, s tmax = 1 / R₀ β γ ∧ StrictMonoOn i (Set.Icc 0 tmax) ∧ StrictAntiOn i (Set.Ici tmax) ∧ i tmax = i 0 + s 0 - 1 / R₀ β γ - log (R₀ β γ * s 0) / R₀ β γ` |

Import chain: `KermackMcKendrickDefs` ← `KermackMcKendrickAux` (+ `KermackMcKendrickCalculus`)
← `KermackMcKendrick` ← `KermackMcKendrickLimitsAux` ← `KermackMcKendrickLimits` ←
`KermackMcKendrickPeak`; all imported (directly or not) by `Epidemics.lean`.

Every statement was checked by hand to be true (proof sketches below) and its elaborated type was
checked with `#check` in a scratch file outside the library.

## Proved

Everything (18/18 theorems). Files (`epidemics/Epidemics/`), lines, content:

| File | Lines | Content |
| --- | --- | --- |
| `KermackMcKendrickDefs.lean` | 52 | pinned `R₀`, `sirField`, `IsSolution` |
| `KermackMcKendrickCalculus.lean` | 105 | generic: constancy, strict monotonicity, monotone limits, `log x - R x` |
| `KermackMcKendrickAux.lean` | 125 | component derivatives, continuity, `R₀` algebra, first integral, barrier, `r` monotone |
| `KermackMcKendrick.lean` | 104 | pinned: conservation, positivity, monotonicity, `s = s₀ e^{-R₀ r}`, threshold |
| `KermackMcKendrickLimitsAux.lean` | 77 | `r < 1`, limits of `s` and `r`, limits of `i` are `0`, `s∞ < s(t)`, root ↔ log form |
| `KermackMcKendrickLimits.lean` | 112 | pinned: limits, final size, `0 < s∞ < 1/R₀`, two uniqueness statements |
| `KermackMcKendrickPeak.lean` | 73 | pinned: `exists_peak` |

Total 648 lines. Docs: `README.md` (results table), `blueprint/src/content.tex` (new section
with `\lean{}` links), `Audit.lean` (18 new `#print axioms` lines).

Main helper lemmas (unpinned):

* `eq_of_hasDerivWithinAt_zero` (zero derivative within `[0, ∞)` ⇒ constant, from
  `constant_of_has_deriv_right_zero`); `strictMonoOn_of_hasDerivWithinAt_pos` /
  `strictAntiOn_of_hasDerivWithinAt_neg` (sign of the derivative on the interior of a convex
  `D ⊆ [0, ∞)`); `exists_tendsto_of_antitoneOn` / `exists_tendsto_of_monotoneOn` (via `f (max t 0)`
  and `tendsto_atTop_ciInf`/`ciSup`); `log_sub_mul_lt_of_mul_le_one` /
  `log_sub_mul_lt_of_one_le_mul` (from `Real.log_lt_sub_one_of_pos`).
* `IsSolution.hasDerivWithinAt_s/i/r` (projections `hasFDerivAt_fst/snd.comp_hasDerivWithinAt`
  of the `IsIntegralCurveOn` field), `IsSolution.s_mul_exp_eq` (first integral `s e^{R₀ r} = s₀`),
  `IsSolution.half_mul_exp_le_i` (barrier: `i ≥ i₀ e^{-γ t}/2` via
  `image_le_of_deriv_right_lt_deriv_boundary'`, no integrals or Gronwall),
  `IsSolution.not_tendsto_i_pos` (MVT `exists_hasDerivAt_eq_slope` on a window of length
  `4/(γ L)`), `IsSolution.limit_lt_s`, `IsSolution.log_sub_eq_of_final_size`.

Reusable pieces: the whole `KermackMcKendrickCalculus.lean` is model-independent (any ODE
on `[0, ∞)` stated with `HasDerivWithinAt … (Ici 0)`, e.g. CRN-2's Kurtz limit or other
compartmental models); the barrier pattern proves positivity for any `x' = x · g(t, …)` with a
lower bound on `g`.

## Plan followed in phase 2 (kept for reference)

Difference from this plan: `i_pos` was proved with neither (a) nor (b) of step 3, but with the
barrier `i ≥ i₀ e^{-γ t}/2` (`IsSolution.half_mul_exp_le_i`); the limits helpers went to
`KermackMcKendrickLimitsAux.lean` and the generic monotone-limit lemmas to
`KermackMcKendrickCalculus.lean`.

0. **Component derivatives** (helper file `KermackMcKendrickAux.lean`, imported by
   `KermackMcKendrick.lean`). Tested in a scratch file; this compiles:
   ```lean
   theorem IsSolution.hasDerivWithinAt_s (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) :
       HasDerivWithinAt s (-(β * s t * i t)) (Set.Ici 0) t := by
     have h2 := hasFDerivAt_fst.comp_hasDerivWithinAt t (h.isIntegralCurveOn t ht)
     simpa [sirField, Function.comp_def] using h2
   -- i: (hasFDerivAt_fst.comp _ hasFDerivAt_snd).comp_hasDerivWithinAt t (h.isIntegralCurveOn t ht)
   -- r: (hasFDerivAt_snd.comp _ hasFDerivAt_snd).comp_hasDerivWithinAt t (h.isIntegralCurveOn t ht)
   ```
   Then: `ContinuousOn s/i/r (Set.Ici 0)` (from `HasDerivWithinAt.continuousWithinAt`),
   `HasDerivAt` at `t > 0` (`HasDerivWithinAt.hasDerivAt` with `Ici_mem_nhds`), `R₀_pos`,
   `R₀ β γ * γ = β`, and a generic lemma "derivative within `Ici 0` vanishes on `[0, ∞)` ⇒
   constant on `[0, ∞)`" (`constant_of_has_deriv_right_zero` on `Icc 0 t`, after `mono` to
   `Ici x`).
1. `sum_eq_one`: derivative of `s + i + r` is `0`; constant lemma; `sum_zero`.
2. `s_eq_mul_exp`: `d/dt [s · exp(R₀ r)] = exp(R₀ r) (s' + R₀ s r') = 0` (uses `γ ≠ 0`, no
   positivity); constant lemma; `r_zero`. Then `s_pos` from `exp_pos`, `s_zero_pos`.
3. `i_pos`: either (a) `G t = ∫ u in 0..t, (β s u - γ)` (`s` continuous on `Ici 0`;
   `intervalIntegral.integral_hasDerivWithinAt_right`), `d/dt [i · exp(-G)] = 0`, so
   `i t = i 0 · exp (G t) > 0`; or (b) Gronwall: if `i t₁ = 0`, the time reversal
   `u ↦ i (t₁ - u)` satisfies `|j'| ≤ K |j|` on `[0, t₁]` (`K = β · sup_{[0,t₁]} |s| + γ`, from
   `IsCompact.exists_bound_of_continuousOn`), so `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`
   gives `i 0 = 0`; conclude by IVT/connectedness.
4. `strictAntiOn_s`, `strictMonoOn_r`: `strictAntiOn_of_deriv_neg` / `strictMonoOn_of_deriv_pos`
   on `convex_Ici 0` (`interior_Ici` = `Ioi 0`, `deriv` from `HasDerivAt.deriv`). `r_nonneg` from
   monotonicity and `r_zero`.
5. `strictAntiOn_i`: for `t > 0`, `s t < s 0`, so `β s t - γ < β s 0 - γ ≤ 0` (`R₀ s₀ ≤ 1` ⇔
   `β s₀ ≤ γ`), `i' = i (β s - γ) < 0`; `strictAntiOn_of_deriv_neg`.
6. `initially_increasing_iff`: (→) if `R₀ s₀ ≤ 1`, step 5 contradicts `i 0 < i ε`.
   (←) `t ↦ i t * (β s t - γ)` is continuous within `Ici 0` at `0` and positive there, so positive
   on some `[0, ε]`; `strictMonoOn_of_deriv_pos` on `Icc 0 ε`.
7. Limits (helper `KermackMcKendrickLimitsAux.lean`): `s (max t 0)` is antitone and bounded below by
   0 ⇒ `tendsto_atTop_ciInf`, transfer with `Tendsto.congr'` (eventually `t ≥ 0`); similarly `r`
   increasing, bounded by 1 (conservation, `s, i > 0`) ⇒ converges; `i = 1 - s - r` converges to
   `L`; if `L > 0` then eventually `i ≥ L/2`, so `r t ≥ r T + γ L/2 (t - T)` (mean value,
   `Convex.mul_sub_le_image_sub_of_le_deriv`) is unbounded: contradiction. `tendsto_r` from
   conservation.
8. `final_size`: pass to the limit in `s_eq_mul_exp` (`tendsto_nhds_unique`, continuity of `exp`).
   `limit_pos`: `s∞ = s₀ exp(…) > 0`.
9. `R₀_mul_limit_lt_one`: if `R₀ s∞ ≥ 1`, then `s t > s∞` for all `t ≥ 0` (strict antitone), so
   `β s t > γ`, `i' > 0`, `i t ≥ i 0 > 0` for all `t ≥ 0`, contradicting `tendsto_i`.
10. `final_size_unique`: `g x = log x + R₀ (1 - x)`; for `0 < a < b ≤ 1/R₀`,
    `g b - g a = log (b/a) - R₀ (b - a) > (b - a)/b - R₀ (b - a) ≥ 0` (`Real.log_lt_sub_one_of_pos`
    applied to `a/b`); both `x` and `s∞` solve `g = log s₀ + R₀`.
    `final_size_unique_of_le_one`: `s₀ < 1` (`i₀ > 0`), so `g 1 > log s₀ + R₀`; either `x ≤ 1/R₀`
    (previous lemma) or `1/R₀ < x ≤ 1`, where `g` is decreasing (`log (b/a) < b/a - 1`), so
    `g x ≥ g 1 > log s₀ + R₀`: not a root. (Alternatively concavity of `log`,
    `strictConcaveOn_log_Ioi`.)
11. `exists_peak`: invariant `i + s - log s / R₀ = 1 - log s₀ / R₀` on `[0, ∞)` (algebra from
    `s_eq_mul_exp`, `sum_eq_one`, `log_exp`); IVT (`intermediate_value_Icc'`) on `[0, T]` with
    `s T < 1/R₀` (from `R₀_mul_limit_lt_one` and the limit) gives `tmax` with `s tmax = 1/R₀`,
    `tmax > 0` since `s 0 > 1/R₀`; `i' > 0` on `[0, tmax)`, `i' < 0` on `(tmax, ∞)` by strict
    antitonicity of `s`; peak value from the invariant and `i 0 + s 0 = 1`.
12. Docs: README table, blueprint entries, `Audit.lean` `#print axioms` lines for the 18 theorems.

## Errors

No statement turned out false or unprovable. Problems met and fixed during phase 2:

* `convert … using 1` on `HasDerivWithinAt` goals descended into mismatched instance paths
  (`Real.instAddCommGroup` vs `Real.normedAddCommGroup.toAddCommGroup`); fixed by
  `HasDerivWithinAt.congr_deriv`, which only rewrites the derivative value.
* `HasDerivAt.neg` produced Pi-negation forms (`-fun y ↦ …`); avoided by putting the barrier in the
  lower slot of `image_le_of_deriv_right_lt_deriv_boundary'` (no negation needed).
* Declaration order in the pinned files (`s_pos` before `s_eq_mul_exp`, `r_nonneg` before
  `strictMonoOn_r`, `tendsto_i` before `exists_tendsto_s`): the substance lives in helpers
  (`s_mul_exp_eq`, `strictMonoOn_r_of_pos`, `exists_tendsto_s_aux`) used by both.
* `Set.left_mem_Ici` is deprecated in this Mathlib; use `Set.self_mem_Ici`.

## Deviations from the paper

1. **Special case of Kermack–McKendrick 1927.** Their model has infectivity and removal rates
   depending on the age of infection; as in the roadmap and in Hethcote §2.3, we formalize the
   constant-rate special case (the SIR ODE). Docstrings cite Hethcote 2000 (system (2.2),
   Theorem 2.1) for numbering, since the 1927 paper has no numbered theorems.
2. **Solution as hypothesis, on `[0, ∞)`.** Hethcote states existence, uniqueness and positive
   invariance of the triangle `T`; we do not construct solutions (as the task requires). The ODE is
   Mathlib's `IsIntegralCurveOn` of `fun _ ↦ sirField β γ` on `Set.Ici 0`, i.e. derivatives within
   `[0, ∞)` (one-sided at `0`); values for `t < 0` are irrelevant. Positivity is proved, not assumed.
3. **`ℝ³` as `ℝ × ℝ × ℝ`, components as three functions.** The prompt's `(s, i, r) : ℝ → ℝ³` is the
   curve `fun t ↦ (s t, i t, r t)`; the theorems speak about `s`, `i`, `r` directly. We keep `r` in
   the state with `r' = γ i` (Hethcote eliminates it by `r = 1 - s - i`; here conservation is a
   theorem).
4. **Initial data.** Hethcote allows `s₀, i₀ ≥ 0` and `r(0) = 1 - s₀ - i₀ ≥ 0`; we fix `r(0) = 0`,
   `s(0), i(0) > 0` (task). Hence `i₀ + s₀ = 1`, and his equation
   `i₀ + s₀ - s∞ + ln(s∞/s₀)/σ = 0` becomes the roadmap's `s∞ = s₀ exp(-R₀(1 - s∞))`. The peak
   value is stated verbatim as `i₀ + s₀ - 1/R₀ - log(R₀ s₀)/R₀`.
5. **"Initially increases"** is formalized as `∃ ε > 0, StrictMonoOn i (Set.Icc 0 ε)` (a statement
   about `i`, not merely the sign of `i'(0)`, which would be a tautology).
6. **Threshold, subcritical case.** Hethcote's "if `σ s₀ ≤ 1`, `i(t)` decreases to zero" is split
   into `strictAntiOn_i` (strictly decreasing on `[0, ∞)`) and `tendsto_i` (which holds for every
   solution).
7. **Limits.** "`s∞` exists" is `∃ sInfty, Tendsto s atTop (𝓝 sInfty)`; the properties of `s∞` are
   stated for any limit (hypothesis `Tendsto s atTop (𝓝 sInfty)`), avoiding a `limUnder`
   definition. `i∞ = 0` is `Tendsto i atTop (𝓝 0)`; `r∞ = 1 - s∞` is `tendsto_r`.
8. **Uniqueness of the final size.** Hethcote's "unique root in `(0, 1/σ)`" is stated on the slightly
   larger `(0, 1/R₀]` (`R₀ x ≤ 1`), together with `0 < s∞` and `R₀ s∞ < 1`; we also add uniqueness
   on `(0, 1]` (`final_size_unique_of_le_one`), the physically meaningful range.
9. **Extras beyond the task list**, all from Hethcote's Theorem 2.1: `strictAntiOn_s`,
   `strictMonoOn_r`, `strictAntiOn_i`, `tendsto_r`, `limit_pos`, `R₀_mul_limit_lt_one`, the two
   uniqueness statements and `exists_peak`.
