import Epidemics.KermackMcKendrickLimits

/-! # The Kermack–McKendrick SIR model: the epidemic peak (EPI-7)

Above the threshold (`R₀ s(0) > 1`), the infected fraction increases until the susceptible fraction
reaches `1 / R₀`, and decreases afterwards; its maximum is
`i_max = i(0) + s(0) - 1 / R₀ - log(R₀ s(0)) / R₀` (Hethcote 2000, Theorem 2.1).
-/

namespace Epidemics.KermackMcKendrick

open Filter Topology

variable {β γ : ℝ} {s i r : ℝ → ℝ}

/-- Threshold theorem, supercritical case (Hethcote 2000, Theorem 2.1): if `R₀ s(0) > 1`, there is
a time `tmax > 0` with `s(tmax) = 1 / R₀` such that `i` is strictly increasing on `[0, tmax]` and
strictly decreasing on `[tmax, ∞)`, and the peak value is
`i(tmax) = i(0) + s(0) - 1 / R₀ - log(R₀ s(0)) / R₀`. -/
theorem IsSolution.exists_peak (h : IsSolution β γ s i r) (hR : 1 < R₀ β γ * s 0) :
    ∃ tmax > 0, s tmax = 1 / R₀ β γ ∧ StrictMonoOn i (Set.Icc 0 tmax) ∧
      StrictAntiOn i (Set.Ici tmax) ∧
      i tmax = i 0 + s 0 - 1 / R₀ β γ - Real.log (R₀ β γ * s 0) / R₀ β γ := by
  have hR0 := h.R₀_pos
  obtain ⟨sI, hs⟩ := h.exists_tendsto_s
  have hsI : sI < 1 / R₀ β γ := by
    rw [lt_div_iff₀ hR0, mul_comm]
    exact h.R₀_mul_limit_lt_one hs
  have hp0 : 1 / R₀ β γ < s 0 := by
    rw [div_lt_iff₀ hR0, mul_comm]
    exact hR
  obtain ⟨T, hT, hT0⟩ := ((hs.eventually (gt_mem_nhds hsI)).and (eventually_ge_atTop 0)).exists
  obtain ⟨tmax, htm, hstm⟩ := intermediate_value_Icc' hT0
    (h.continuousOn_s.mono Set.Icc_subset_Ici_self) ⟨hT.le, hp0.le⟩
  have htm0 : 0 < tmax := by
    rcases htm.1.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hstm
      linarith
  have hβp : β * (1 / R₀ β γ) = γ := by
    rw [R₀, one_div_div]
    field_simp [h.beta_pos.ne']
  refine ⟨tmax, htm0, hstm, ?_, ?_, ?_⟩
  · refine strictMonoOn_of_hasDerivWithinAt_pos (fun _ hu ↦ h.hasDerivWithinAt_i hu)
      (convex_Icc 0 tmax) Set.Icc_subset_Ici_self fun u hu ↦ ?_
    rw [interior_Icc] at hu
    have hsu : β * s tmax < β * s u :=
      mul_lt_mul_of_pos_left (h.strictAntiOn_s hu.1.le htm0.le hu.2) h.beta_pos
    rw [hstm, hβp] at hsu
    rw [show β * s u * i u - γ * i u = (β * s u - γ) * i u by ring]
    exact mul_pos (by linarith) (h.i_pos hu.1.le)
  · refine strictAntiOn_of_hasDerivWithinAt_neg (fun _ hu ↦ h.hasDerivWithinAt_i hu)
      (convex_Ici tmax) (Set.Ici_subset_Ici.2 htm0.le) fun u hu ↦ ?_
    rw [interior_Ici] at hu
    have hu0 : 0 ≤ u := htm0.le.trans hu.le
    have hsu : β * s u < β * s tmax :=
      mul_lt_mul_of_pos_left (h.strictAntiOn_s htm0.le hu0 hu) h.beta_pos
    rw [hstm, hβp] at hsu
    rw [show β * s u * i u - γ * i u = (β * s u - γ) * i u by ring]
    exact mul_neg_of_neg_of_pos (by linarith) (h.i_pos hu0)
  · have e1 := congrArg Real.log ((h.s_eq_mul_exp htm0.le).symm.trans hstm)
    rw [Real.log_mul h.s_zero_pos.ne' (Real.exp_pos _).ne', Real.log_exp, one_div,
      Real.log_inv] at e1
    have e2 := h.sum_eq_one htm0.le
    rw [hstm] at e2
    have hRR : R₀ β γ * (1 / R₀ β γ) = 1 := mul_one_div_cancel hR0.ne'
    have key : R₀ β γ * i tmax = R₀ β γ - 1 - (Real.log (R₀ β γ) + Real.log (s 0)) := by
      linear_combination e1 + R₀ β γ * e2 - hRR
    rw [Real.log_mul hR0.ne' h.s_zero_pos.ne', h.i_zero_add_s_zero]
    field_simp
    linear_combination key

end Epidemics.KermackMcKendrick
