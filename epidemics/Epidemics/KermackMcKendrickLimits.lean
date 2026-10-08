import Epidemics.KermackMcKendrickLimitsAux

/-! # The Kermack–McKendrick SIR model: limits and the final-size equation (EPI-7)

For every solution of the Kermack–McKendrick system on `[0, ∞)` (`IsSolution β γ s i r`):

* the epidemic dies out, `i(t) → 0`, and the limit `s∞ = lim s(t)` exists; then `r(t) → 1 - s∞`;
* the final-size equation `s∞ = s(0) exp(-R₀ (1 - s∞))` (Kermack–McKendrick 1927; Hethcote 2000,
  Theorem 2.1, with `i(0) + s(0) = 1`);
* `0 < s∞ < 1 / R₀`, and `s∞` is the unique root of the final-size equation in `(0, 1 / R₀]`
  (Hethcote 2000, Theorem 2.1) and also in `(0, 1]`.
-/

namespace Epidemics.KermackMcKendrick

open Filter Topology

variable {β γ : ℝ} {s i r : ℝ → ℝ}

/-- The epidemic dies out: `i(t) → 0` as `t → ∞` (Hethcote 2000, Theorem 2.1). -/
theorem IsSolution.tendsto_i (h : IsSolution β γ s i r) : Tendsto i atTop (𝓝 0) := by
  obtain ⟨sI, hs⟩ := h.exists_tendsto_s_aux
  obtain ⟨rI, hr⟩ := h.exists_tendsto_r
  have hi : Tendsto i atTop (𝓝 (1 - sI - rI)) := by
    refine ((tendsto_const_nhds.sub hs).sub hr).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [h.sum_eq_one ht]
  rwa [h.limit_i_eq_zero hi] at hi

/-- The final susceptible fraction `s∞ = lim_{t → ∞} s(t)` exists. -/
theorem IsSolution.exists_tendsto_s (h : IsSolution β γ s i r) :
    ∃ sInfty, Tendsto s atTop (𝓝 sInfty) := by
  exact h.exists_tendsto_s_aux

/-- The recovered fraction tends to `1 - s∞` (since `i(t) → 0` and `s + i + r = 1`). -/
theorem IsSolution.tendsto_r (h : IsSolution β γ s i r) {sInfty : ℝ}
    (hs : Tendsto s atTop (𝓝 sInfty)) : Tendsto r atTop (𝓝 (1 - sInfty)) := by
  have hr : Tendsto (fun t ↦ 1 - s t - i t) atTop (𝓝 (1 - sInfty - 0)) :=
    (tendsto_const_nhds.sub hs).sub h.tendsto_i
  rw [sub_zero] at hr
  refine hr.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  linarith [h.sum_eq_one ht]

/-- The final-size equation (Kermack–McKendrick 1927; Hethcote 2000, Theorem 2.1 with
`i(0) + s(0) = 1`): `s∞ = s(0) exp(-R₀ (1 - s∞))`. -/
theorem IsSolution.final_size (h : IsSolution β γ s i r) {sInfty : ℝ}
    (hs : Tendsto s atTop (𝓝 sInfty)) : sInfty = s 0 * Real.exp (-(R₀ β γ * (1 - sInfty))) := by
  have hlim : Tendsto (fun t ↦ s 0 * Real.exp (-(R₀ β γ * r t))) atTop
      (𝓝 (s 0 * Real.exp (-(R₀ β γ * (1 - sInfty))))) :=
    tendsto_const_nhds.mul (((h.tendsto_r hs).const_mul (R₀ β γ)).neg.rexp)
  refine tendsto_nhds_unique hs (hlim.congr' ?_)
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact (h.s_eq_mul_exp ht).symm

/-- Some individuals escape the epidemic: `s∞ > 0` (Hethcote 2000, Theorem 2.1). -/
theorem IsSolution.limit_pos (h : IsSolution β γ s i r) {sInfty : ℝ}
    (hs : Tendsto s atTop (𝓝 sInfty)) : 0 < sInfty := by
  rw [h.final_size hs]
  exact mul_pos h.s_zero_pos (Real.exp_pos _)

/-- The epidemic ends below the threshold: `R₀ s∞ < 1`, i.e. `s∞ < 1 / R₀` (Hethcote 2000,
Theorem 2.1). -/
theorem IsSolution.R₀_mul_limit_lt_one (h : IsSolution β γ s i r) {sInfty : ℝ}
    (hs : Tendsto s atTop (𝓝 sInfty)) : R₀ β γ * sInfty < 1 := by
  by_contra hle
  rw [h.R₀_mul_lt_one_iff, not_lt] at hle
  have hpos : ∀ u ∈ interior (Set.Ici (0 : ℝ)), 0 < β * s u * i u - γ * i u := by
    intro u hu
    have hu0 : 0 ≤ u := interior_subset hu
    have hsu : β * sInfty < β * s u := mul_lt_mul_of_pos_left (h.limit_lt_s hs hu0) h.beta_pos
    rw [show β * s u * i u - γ * i u = (β * s u - γ) * i u by ring]
    exact mul_pos (by linarith) (h.i_pos hu0)
  have hmono : StrictMonoOn i (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (fun _ hu ↦ h.hasDerivWithinAt_i hu) (convex_Ici 0)
      subset_rfl hpos
  have h0 : i 0 ≤ 0 := ge_of_tendsto h.tendsto_i <| by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact hmono.monotoneOn Set.self_mem_Ici ht ht
  linarith [h.i_zero_pos]

/-- Uniqueness (Hethcote 2000, Theorem 2.1): `s∞` is the only root `x` of the final-size equation
`x = s(0) exp(-R₀ (1 - x))` with `0 < x ≤ 1 / R₀`. -/
theorem IsSolution.final_size_unique (h : IsSolution β γ s i r) {sInfty : ℝ}
    (hs : Tendsto s atTop (𝓝 sInfty)) {x : ℝ} (hx0 : 0 < x) (hx1 : R₀ β γ * x ≤ 1)
    (hx : x = s 0 * Real.exp (-(R₀ β γ * (1 - x)))) : x = sInfty := by
  have hsI : 0 < sInfty := h.limit_pos hs
  have e1 := h.log_sub_eq_of_final_size hx
  have e2 := h.log_sub_eq_of_final_size (h.final_size hs)
  rcases lt_trichotomy x sInfty with hlt | heq | hgt
  · linarith [log_sub_mul_lt_of_mul_le_one hx0 hlt (h.R₀_mul_limit_lt_one hs).le]
  · exact heq
  · linarith [log_sub_mul_lt_of_mul_le_one hsI hgt hx1]

/-- Uniqueness among fractions: `s∞` is the only root `x` of the final-size equation
`x = s(0) exp(-R₀ (1 - x))` with `0 < x ≤ 1`. -/
theorem IsSolution.final_size_unique_of_le_one (h : IsSolution β γ s i r) {sInfty : ℝ}
    (hs : Tendsto s atTop (𝓝 sInfty)) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hx : x = s 0 * Real.exp (-(R₀ β γ * (1 - x)))) : x = sInfty := by
  by_cases hRx : R₀ β γ * x ≤ 1
  · exact h.final_size_unique hs hx0 hRx hx
  · exfalso
    have e1 := h.log_sub_eq_of_final_size hx
    have hs0 : Real.log (s 0) < 0 := Real.log_neg h.s_zero_pos h.s_zero_lt_one
    rcases hx1.lt_or_eq with hlt | rfl
    · have := log_sub_mul_lt_of_one_le_mul hx0 hlt (not_le.1 hRx).le
      rw [Real.log_one, mul_one] at this
      linarith
    · rw [Real.log_one, mul_one] at e1
      linarith

end Epidemics.KermackMcKendrick
