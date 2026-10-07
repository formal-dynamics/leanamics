import Epidemics.KermackMcKendrickAux

/-! # The Kermack–McKendrick SIR model: invariants and the threshold (EPI-7)

For every solution of the Kermack–McKendrick system on `[0, ∞)` (`IsSolution β γ s i r`, see
`Epidemics.KermackMcKendrickDefs`):

* conservation `s + i + r = 1` and positivity `s, i > 0`, `r ≥ 0`;
* `s` is strictly decreasing and `r` strictly increasing (Hethcote 2000, Theorem 2.1);
* the first integral `s(t) = s(0) exp(-R₀ r(t))`, from `ds/dr = -R₀ s` (Kermack–McKendrick 1927);
* the threshold: if `R₀ s(0) ≤ 1` then `i` is strictly decreasing (Hethcote 2000, Theorem 2.1), and
  `i` initially increases iff `R₀ s(0) > 1`.

Limits and the final-size equation are in `Epidemics.KermackMcKendrickLimits`, the epidemic peak in
`Epidemics.KermackMcKendrickPeak`.
-/

namespace Epidemics.KermackMcKendrick

variable {β γ : ℝ} {s i r : ℝ → ℝ}

/-- Conservation of the population: `s(t) + i(t) + r(t) = 1` for all `t ≥ 0` (the derivative of
`s + i + r` vanishes; Hethcote 2000, §2.3). -/
theorem IsSolution.sum_eq_one (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) :
    s t + i t + r t = 1 := by
  have hd : ∀ u, 0 ≤ u → HasDerivWithinAt (fun u ↦ s u + i u + r u) 0 (Set.Ici 0) u := by
    intro u hu
    refine (((h.hasDerivWithinAt_s hu).add (h.hasDerivWithinAt_i hu)).add
      (h.hasDerivWithinAt_r hu)).congr_deriv ?_
    ring
  linarith [eq_of_hasDerivWithinAt_zero hd ht, h.sum_zero]

/-- Positivity of the susceptible fraction: `s(t) > 0` for all `t ≥ 0`. -/
theorem IsSolution.s_pos (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) : 0 < s t := by
  have := h.s_mul_exp_eq ht
  have he := Real.exp_pos (R₀ β γ * r t)
  by_contra hle
  nlinarith [h.s_zero_pos]

/-- Positivity of the infected fraction: `i(t) > 0` for all `t ≥ 0`. -/
theorem IsSolution.i_pos (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) : 0 < i t := by
  have := h.i_zero_pos
  exact lt_of_lt_of_le (by positivity) (h.half_mul_exp_le_i (fun _ hu ↦ h.s_pos hu) ht)

/-- Nonnegativity of the recovered fraction: `r(t) ≥ 0` for all `t ≥ 0`. -/
theorem IsSolution.r_nonneg (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ r t := by
  simpa [h.r_zero] using
    (h.strictMonoOn_r_of_pos fun _ hu ↦ h.i_pos hu).monotoneOn Set.self_mem_Ici ht ht

/-- The susceptible fraction is strictly decreasing on `[0, ∞)` (Hethcote 2000, Theorem 2.1). -/
theorem IsSolution.strictAntiOn_s (h : IsSolution β γ s i r) : StrictAntiOn s (Set.Ici 0) := by
  exact strictAntiOn_of_hasDerivWithinAt_neg (fun _ hu ↦ h.hasDerivWithinAt_s hu) (convex_Ici 0)
    subset_rfl fun _ hu ↦ neg_lt_zero.2 <|
      mul_pos (mul_pos h.beta_pos (h.s_pos (interior_subset hu))) (h.i_pos (interior_subset hu))

/-- The recovered fraction is strictly increasing on `[0, ∞)`. -/
theorem IsSolution.strictMonoOn_r (h : IsSolution β γ s i r) : StrictMonoOn r (Set.Ici 0) := by
  exact h.strictMonoOn_r_of_pos fun _ hu ↦ h.i_pos hu

/-- The first integral of Kermack–McKendrick (1927): since `ds/dr = -R₀ s` and `r(0) = 0`,
`s(t) = s(0) exp(-R₀ r(t))` for all `t ≥ 0`. -/
theorem IsSolution.s_eq_mul_exp (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) :
    s t = s 0 * Real.exp (-(R₀ β γ * r t)) := by
  rw [← h.s_mul_exp_eq ht, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Threshold theorem, subcritical case (Hethcote 2000, Theorem 2.1): if `R₀ s(0) ≤ 1`, the
infected fraction is strictly decreasing on `[0, ∞)`, so there is no epidemic. -/
theorem IsSolution.strictAntiOn_i (h : IsSolution β γ s i r) (hR : R₀ β γ * s 0 ≤ 1) :
    StrictAntiOn i (Set.Ici 0) := by
  have hγ : β * s 0 ≤ γ := h.R₀_mul_le_one_iff.1 hR
  refine strictAntiOn_of_hasDerivWithinAt_neg (fun _ hu ↦ h.hasDerivWithinAt_i hu)
    (convex_Ici 0) subset_rfl fun u hu ↦ ?_
  have hu0 : 0 < u := by simpa [interior_Ici] using hu
  have hsu : β * s u < β * s 0 :=
    mul_lt_mul_of_pos_left (h.strictAntiOn_s Set.self_mem_Ici hu0.le hu0) h.beta_pos
  rw [show β * s u * i u - γ * i u = (β * s u - γ) * i u by ring]
  exact mul_neg_of_neg_of_pos (by linarith) (h.i_pos hu0.le)

/-- Threshold theorem (Kermack–McKendrick 1927; Hethcote 2000, Theorem 2.1): the infected fraction
initially increases, i.e. is strictly increasing on some interval `[0, ε]` with `ε > 0`, iff
`R₀ s(0) > 1`. -/
theorem IsSolution.initially_increasing_iff (h : IsSolution β γ s i r) :
    (∃ ε > 0, StrictMonoOn i (Set.Icc 0 ε)) ↔ 1 < R₀ β γ * s 0 := by
  constructor
  · rintro ⟨ε, hε, hmono⟩
    by_contra hle
    have h1 : i 0 < i ε := hmono (Set.left_mem_Icc.2 hε.le) (Set.right_mem_Icc.2 hε.le) hε
    have h2 : i ε < i 0 := h.strictAntiOn_i (not_lt.1 hle) Set.self_mem_Ici hε.le hε
    exact lt_asymm h1 h2
  · intro hR
    have hγ : γ < β * s 0 := h.one_lt_R₀_mul_iff.1 hR
    have hs0 := h.continuousOn_s 0 Set.self_mem_Ici
    have hi0 := h.continuousOn_i 0 Set.self_mem_Ici
    have hcont : ContinuousWithinAt (fun t ↦ β * s t * i t - γ * i t) (Set.Ici 0) 0 :=
      ((continuousWithinAt_const.mul hs0).mul hi0).sub (continuousWithinAt_const.mul hi0)
    have hpos : 0 < β * s 0 * i 0 - γ * i 0 := by
      rw [show β * s 0 * i 0 - γ * i 0 = (β * s 0 - γ) * i 0 by ring]
      exact mul_pos (by linarith) h.i_zero_pos
    obtain ⟨ε, hε, hsub⟩ :=
      mem_nhdsGE_iff_exists_Icc_subset.1 (hcont.eventually (lt_mem_nhds hpos))
    exact ⟨ε, hε, strictMonoOn_of_hasDerivWithinAt_pos (fun _ hu ↦ h.hasDerivWithinAt_i hu)
      (convex_Icc 0 ε) Set.Icc_subset_Ici_self fun u hu ↦ hsub (interior_subset hu)⟩

end Epidemics.KermackMcKendrick
