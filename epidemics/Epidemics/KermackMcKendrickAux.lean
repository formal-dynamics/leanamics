import Epidemics.KermackMcKendrickDefs
import Epidemics.KermackMcKendrickCalculus

/-! # The Kermack–McKendrick SIR model: basic API of solutions (EPI-7)

From `IsSolution β γ s i r`: the derivatives of the three components within `[0, ∞)`, their
continuity on `[0, ∞)`, and the algebra of `R₀ = β / γ`.
-/

namespace Epidemics.KermackMcKendrick

open Set

variable {β γ : ℝ} {s i r : ℝ → ℝ}

/-- `s' = -β s i` on `[0, ∞)`. -/
theorem IsSolution.hasDerivWithinAt_s (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt s (-(β * s t * i t)) (Ici 0) t := by
  have h2 := hasFDerivAt_fst.comp_hasDerivWithinAt t (h.isIntegralCurveOn t ht)
  simpa [sirField, Function.comp_def] using h2

/-- `i' = β s i - γ i` on `[0, ∞)`. -/
theorem IsSolution.hasDerivWithinAt_i (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt i (β * s t * i t - γ * i t) (Ici 0) t := by
  have h2 := (hasFDerivAt_fst.comp _ hasFDerivAt_snd).comp_hasDerivWithinAt t
    (h.isIntegralCurveOn t ht)
  simpa [sirField, Function.comp_def] using h2

/-- `r' = γ i` on `[0, ∞)`. -/
theorem IsSolution.hasDerivWithinAt_r (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt r (γ * i t) (Ici 0) t := by
  have h2 := (hasFDerivAt_snd.comp _ hasFDerivAt_snd).comp_hasDerivWithinAt t
    (h.isIntegralCurveOn t ht)
  simpa [sirField, Function.comp_def] using h2

/-- `s` is continuous on `[0, ∞)`. -/
theorem IsSolution.continuousOn_s (h : IsSolution β γ s i r) : ContinuousOn s (Ici 0) :=
  continuousOn_of_hasDerivWithinAt fun _ ht ↦ h.hasDerivWithinAt_s ht

/-- `i` is continuous on `[0, ∞)`. -/
theorem IsSolution.continuousOn_i (h : IsSolution β γ s i r) : ContinuousOn i (Ici 0) :=
  continuousOn_of_hasDerivWithinAt fun _ ht ↦ h.hasDerivWithinAt_i ht

/-- `r` is continuous on `[0, ∞)`. -/
theorem IsSolution.continuousOn_r (h : IsSolution β γ s i r) : ContinuousOn r (Ici 0) :=
  continuousOn_of_hasDerivWithinAt fun _ ht ↦ h.hasDerivWithinAt_r ht

/-- `r' = γ i` at every `t > 0` (two-sided derivative). -/
theorem IsSolution.hasDerivAt_r (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 < t) :
    HasDerivAt r (γ * i t) t :=
  (h.hasDerivWithinAt_r ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- `R₀ > 0`. -/
theorem IsSolution.R₀_pos (h : IsSolution β γ s i r) : 0 < R₀ β γ :=
  div_pos h.beta_pos h.gamma_pos

/-- `R₀ γ = β`. -/
theorem IsSolution.R₀_mul_gamma (h : IsSolution β γ s i r) : R₀ β γ * γ = β :=
  div_mul_cancel₀ β h.gamma_pos.ne'

/-- `R₀ x ≤ 1 ↔ β x ≤ γ`. -/
theorem IsSolution.R₀_mul_le_one_iff (h : IsSolution β γ s i r) {x : ℝ} :
    R₀ β γ * x ≤ 1 ↔ β * x ≤ γ := by
  rw [R₀, div_mul_eq_mul_div, div_le_one h.gamma_pos]

/-- `R₀ x < 1 ↔ β x < γ`. -/
theorem IsSolution.R₀_mul_lt_one_iff (h : IsSolution β γ s i r) {x : ℝ} :
    R₀ β γ * x < 1 ↔ β * x < γ := by
  rw [R₀, div_mul_eq_mul_div, div_lt_one h.gamma_pos]

/-- `1 < R₀ x ↔ γ < β x`. -/
theorem IsSolution.one_lt_R₀_mul_iff (h : IsSolution β γ s i r) {x : ℝ} :
    1 < R₀ β γ * x ↔ γ < β * x := by
  rw [← not_le, h.R₀_mul_le_one_iff, not_le]

/-- `s(0) < 1`, since `i(0) > 0`, `r(0) = 0` and the fractions sum to one. -/
theorem IsSolution.s_zero_lt_one (h : IsSolution β γ s i r) : s 0 < 1 := by
  linarith [h.sum_zero, h.r_zero, h.i_zero_pos]

/-- `i(0) + s(0) = 1`. -/
theorem IsSolution.i_zero_add_s_zero (h : IsSolution β γ s i r) : i 0 + s 0 = 1 := by
  linarith [h.sum_zero, h.r_zero]

/-- The first integral of Kermack–McKendrick (1927): `s · exp(R₀ r)` is constant on `[0, ∞)`
(its derivative is `exp(R₀ r) (-β s i + R₀ s γ i) = 0`), hence equal to `s(0)` as `r(0) = 0`. -/
theorem IsSolution.s_mul_exp_eq (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) :
    s t * Real.exp (R₀ β γ * r t) = s 0 := by
  have hd : ∀ u, 0 ≤ u →
      HasDerivWithinAt (fun u ↦ s u * Real.exp (R₀ β γ * r u)) 0 (Ici 0) u := by
    intro u hu
    refine ((h.hasDerivWithinAt_s hu).mul
      ((h.hasDerivWithinAt_r hu).const_mul (R₀ β γ)).exp).congr_deriv ?_
    linear_combination (s u * i u * Real.exp (R₀ β γ * r u)) * h.R₀_mul_gamma
  simpa [h.r_zero] using eq_of_hasDerivWithinAt_zero hd ht

/-- A barrier keeping the infected fraction positive: if `s > 0` on `[0, ∞)`, then
`i(t) ≥ i(0) e^{-γ t} / 2` for all `t ≥ 0`. Where `i` would touch the barrier `b`,
`b' = -γ b = -γ i < β s i - γ i = i'`, so `i` cannot cross it. -/
theorem IsSolution.half_mul_exp_le_i (h : IsSolution β γ s i r) (hs : ∀ u, 0 ≤ u → 0 < s u)
    {t : ℝ} (ht : 0 ≤ t) : i 0 / 2 * Real.exp (-γ * t) ≤ i t := by
  have hb : ∀ x, HasDerivAt (fun x ↦ i 0 / 2 * Real.exp (-γ * x))
      (i 0 / 2 * (Real.exp (-γ * x) * (-γ * 1))) x :=
    fun x ↦ ((hasDerivAt_id' x).const_mul (-γ)).exp.const_mul (i 0 / 2)
  refine image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := t)
    (fun x _ ↦ (hb x).continuousAt.continuousWithinAt) (fun x _ ↦ (hb x).hasDerivWithinAt)
    ?_ (h.continuousOn_i.mono Icc_subset_Ici_self)
    (fun x hx ↦ (h.hasDerivWithinAt_i hx.1).mono (Ici_subset_Ici.2 hx.1)) ?_ ⟨ht, le_rfl⟩
  · simp only [mul_zero, Real.exp_zero, mul_one]
    linarith [h.i_zero_pos]
  · intro x hx heq
    have hi : 0 < i x := heq ▸ by have := h.i_zero_pos; positivity
    have hsi : 0 < β * s x * i x := mul_pos (mul_pos h.beta_pos (hs x hx.1)) hi
    have hl : i 0 / 2 * (Real.exp (-γ * x) * (-γ * 1)) = -γ * i x := by
      rw [← heq]
      ring
    rw [hl]
    linarith

/-- If `i > 0` on `[0, ∞)`, then `r` (with `r' = γ i`) is strictly increasing on `[0, ∞)`. -/
theorem IsSolution.strictMonoOn_r_of_pos (h : IsSolution β γ s i r)
    (hi : ∀ u, 0 ≤ u → 0 < i u) : StrictMonoOn r (Ici 0) :=
  strictMonoOn_of_hasDerivWithinAt_pos (fun _ hu ↦ h.hasDerivWithinAt_r hu) (convex_Ici 0)
    subset_rfl fun u hu ↦ mul_pos h.gamma_pos (hi u (interior_subset hu))

end Epidemics.KermackMcKendrick
