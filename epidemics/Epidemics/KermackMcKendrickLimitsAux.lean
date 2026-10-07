import Epidemics.KermackMcKendrick

/-! # The Kermack–McKendrick SIR model: helpers for the limits (EPI-7)

* `s` and `r` converge (monotone and bounded on `[0, ∞)`);
* every limit of `i` is `0`: if `i → L > 0`, then `r' = γ i ≥ γ L / 2` eventually, and the mean
  value theorem makes `r` grow by more than `1`, contradicting `0 ≤ r < 1`;
* a limit of `s` lies strictly below every value of `s` on `[0, ∞)`;
* a root `x` of the final-size equation satisfies `log x - R₀ x = log s(0) - R₀`.
-/

namespace Epidemics.KermackMcKendrick

open Set Filter Topology

variable {β γ : ℝ} {s i r : ℝ → ℝ}

/-- `r(t) < 1` for all `t ≥ 0`, since `s(t), i(t) > 0` and `s + i + r = 1`. -/
theorem IsSolution.r_lt_one (h : IsSolution β γ s i r) {t : ℝ} (ht : 0 ≤ t) : r t < 1 := by
  linarith [h.sum_eq_one ht, h.s_pos ht, h.i_pos ht]

/-- The susceptible fraction converges as `t → ∞` (antitone, bounded below by `0`). -/
theorem IsSolution.exists_tendsto_s_aux (h : IsSolution β γ s i r) :
    ∃ L, Tendsto s atTop (𝓝 L) :=
  exists_tendsto_of_antitoneOn h.strictAntiOn_s.antitoneOn fun _ ht ↦ (h.s_pos ht).le

/-- The recovered fraction converges as `t → ∞` (monotone, bounded above by `1`). -/
theorem IsSolution.exists_tendsto_r (h : IsSolution β γ s i r) :
    ∃ L, Tendsto r atTop (𝓝 L) :=
  exists_tendsto_of_monotoneOn h.strictMonoOn_r.monotoneOn fun _ ht ↦ (h.r_lt_one ht).le

/-- A limit of `i` cannot be positive: otherwise `r` would grow without bound. -/
theorem IsSolution.not_tendsto_i_pos (h : IsSolution β γ s i r) {L : ℝ} (hL : 0 < L)
    (hi : Tendsto i atTop (𝓝 L)) : False := by
  obtain ⟨T, hT⟩ := eventually_atTop.1
    ((hi.eventually (lt_mem_nhds (half_lt_self hL))).and (eventually_ge_atTop 0))
  have hT0 : 0 ≤ T := (hT T le_rfl).2
  have hγL : 0 < γ * L := mul_pos h.gamma_pos hL
  have hTb : T < T + 4 / (γ * L) := lt_add_of_pos_right T (by positivity)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope r (fun x ↦ γ * i x) hTb
    (h.continuousOn_r.mono fun x hx ↦ hT0.trans hx.1)
    (fun x hx ↦ h.hasDerivAt_r (hT0.trans_lt hx.1))
  have hic : L / 2 < i c := (hT c hc.1.le).1
  rw [add_sub_cancel_left, eq_div_iff (by positivity)] at hslope
  have hgrow : 2 < γ * i c * (4 / (γ * L)) := by
    have hγ0 : γ ≠ 0 := h.gamma_pos.ne'
    rw [show γ * i c * (4 / (γ * L)) = 4 * i c / L by field_simp, lt_div_iff₀ hL]
    linarith
  linarith [h.r_lt_one (hT0.trans hTb.le), h.r_nonneg hT0]

/-- Every limit of `i` is `0`. -/
theorem IsSolution.limit_i_eq_zero (h : IsSolution β γ s i r) {L : ℝ}
    (hi : Tendsto i atTop (𝓝 L)) : L = 0 := by
  have hL0 : 0 ≤ L :=
    ge_of_tendsto hi (by filter_upwards [eventually_ge_atTop 0] with t ht using (h.i_pos ht).le)
  by_contra hne
  exact h.not_tendsto_i_pos (lt_of_le_of_ne hL0 (Ne.symm hne)) hi

/-- A limit `L` of `s` lies strictly below `s(t)` for every `t ≥ 0`. -/
theorem IsSolution.limit_lt_s (h : IsSolution β γ s i r) {L : ℝ} (hs : Tendsto s atTop (𝓝 L))
    {t : ℝ} (ht : 0 ≤ t) : L < s t := by
  have ht1 : 0 ≤ t + 1 := by linarith
  have hle : L ≤ s (t + 1) := le_of_tendsto hs <| by
    filter_upwards [eventually_ge_atTop (t + 1)] with u hu
    exact h.strictAntiOn_s.antitoneOn ht1 (ht1.trans hu) hu
  exact hle.trans_lt (h.strictAntiOn_s ht ht1 (lt_add_one t))

/-- A root `x` of the final-size equation `x = s(0) exp(-R₀ (1 - x))` satisfies
`log x - R₀ x = log s(0) - R₀`. -/
theorem IsSolution.log_sub_eq_of_final_size (h : IsSolution β γ s i r) {x : ℝ}
    (hx : x = s 0 * Real.exp (-(R₀ β γ * (1 - x)))) :
    Real.log x - R₀ β γ * x = Real.log (s 0) - R₀ β γ := by
  have hlog := congrArg Real.log hx
  rw [Real.log_mul h.s_zero_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  linear_combination hlog

end Epidemics.KermackMcKendrick
