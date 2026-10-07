import Mathlib

/-! # One-variable calculus on `[0, ∞)` for the Kermack–McKendrick model (EPI-7)

Generic helpers, independent of the SIR system:

* a function whose derivative within `[0, ∞)` vanishes there is constant on `[0, ∞)`;
* a function differentiable within `[0, ∞)` whose derivative is positive (negative) on the interior
  of a convex subset `D ⊆ [0, ∞)` is strictly monotone (antitone) on `D`;
* a function monotone (antitone) on `[0, ∞)` and bounded above (below) there converges at `+∞`;
* monotonicity of `x ↦ log x - R x`: increasing where `R x ≤ 1`, decreasing where `R x ≥ 1`
  (used for the uniqueness of the final size, Hethcote 2000, Theorem 2.1).
-/

namespace Epidemics.KermackMcKendrick

open Set Filter Topology

/-- A function whose derivative within `[0, ∞)` vanishes at every point of `[0, ∞)` is constant
on `[0, ∞)`. -/
theorem eq_of_hasDerivWithinAt_zero {f : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f 0 (Ici 0) t) {t : ℝ} (ht : 0 ≤ t) : f t = f 0 :=
  constant_of_has_deriv_right_zero
    (fun x hx ↦ (hf x hx.1).continuousWithinAt.mono Icc_subset_Ici_self)
    (fun x hx ↦ (hf x hx.1).mono (Ici_subset_Ici.2 hx.1)) t ⟨ht, le_rfl⟩

/-- A function differentiable within `[0, ∞)` is continuous on `[0, ∞)`. -/
theorem continuousOn_of_hasDerivWithinAt {f f' : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Ici 0) t) : ContinuousOn f (Ici 0) :=
  fun t ht ↦ (hf t ht).continuousWithinAt

/-- At an interior point of `D ⊆ [0, ∞)`, the derivative within `[0, ∞)` is the derivative. -/
theorem deriv_eq_of_mem_interior {f f' : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Ici 0) t) {D : Set ℝ} (hD0 : D ⊆ Ici 0)
    {t : ℝ} (ht : t ∈ interior D) : deriv f t = f' t := by
  have ht0 : 0 < t := by simpa [interior_Ici] using interior_mono hD0 ht
  exact ((hf t ht0.le).hasDerivAt (Ici_mem_nhds ht0)).deriv

/-- Positive derivative on the interior of a convex `D ⊆ [0, ∞)` gives strict monotonicity on
`D`. -/
theorem strictMonoOn_of_hasDerivWithinAt_pos {f f' : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Ici 0) t) {D : Set ℝ} (hD : Convex ℝ D)
    (hD0 : D ⊆ Ici 0) (hpos : ∀ t ∈ interior D, 0 < f' t) : StrictMonoOn f D :=
  strictMonoOn_of_deriv_pos hD ((continuousOn_of_hasDerivWithinAt hf).mono hD0)
    fun t ht ↦ (deriv_eq_of_mem_interior hf hD0 ht).symm ▸ hpos t ht

/-- Negative derivative on the interior of a convex `D ⊆ [0, ∞)` gives strict antitonicity on
`D`. -/
theorem strictAntiOn_of_hasDerivWithinAt_neg {f f' : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Ici 0) t) {D : Set ℝ} (hD : Convex ℝ D)
    (hD0 : D ⊆ Ici 0) (hneg : ∀ t ∈ interior D, f' t < 0) : StrictAntiOn f D :=
  strictAntiOn_of_deriv_neg hD ((continuousOn_of_hasDerivWithinAt hf).mono hD0)
    fun t ht ↦ (deriv_eq_of_mem_interior hf hD0 ht).symm ▸ hneg t ht

/-- A function antitone on `[0, ∞)` and bounded below there converges as `t → ∞`. -/
theorem exists_tendsto_of_antitoneOn {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 0)) {m : ℝ}
    (hm : ∀ t, 0 ≤ t → m ≤ f t) : ∃ L, Tendsto f atTop (𝓝 L) := by
  have hanti : Antitone fun t ↦ f (max t 0) := fun a b hab ↦
    hf (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl)
  have hbdd : BddBelow (range fun t ↦ f (max t 0)) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hm _ (le_max_right t 0)
  refine ⟨_, (tendsto_atTop_ciInf hanti hbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [max_eq_left ht]

/-- A function monotone on `[0, ∞)` and bounded above there converges as `t → ∞`. -/
theorem exists_tendsto_of_monotoneOn {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0)) {M : ℝ}
    (hM : ∀ t, 0 ≤ t → f t ≤ M) : ∃ L, Tendsto f atTop (𝓝 L) := by
  have hmono : Monotone fun t ↦ f (max t 0) := fun a b hab ↦
    hf (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl)
  have hbdd : BddAbove (range fun t ↦ f (max t 0)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hM _ (le_max_right t 0)
  refine ⟨_, (tendsto_atTop_ciSup hmono hbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [max_eq_left ht]

/-- `x ↦ log x - R x` is strictly increasing on `(0, 1 / R]`: if `0 < a < b` and `R b ≤ 1` then
`log a - R a < log b - R b`. -/
theorem log_sub_mul_lt_of_mul_le_one {R a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : R * b ≤ 1) :
    Real.log a - R * a < Real.log b - R * b := by
  have hb0 : 0 < b := ha.trans hab
  have h1 := Real.log_lt_sub_one_of_pos (div_pos ha hb0) (div_lt_one hb0 |>.2 hab).ne
  rw [Real.log_div ha.ne' hb0.ne'] at h1
  have h2 : a / b - 1 ≤ R * (a - b) := by
    rw [div_sub_one hb0.ne', div_le_iff₀ hb0]
    nlinarith [mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 hb)]
  linarith

/-- `x ↦ log x - R x` is strictly decreasing on `[1 / R, ∞)`: if `0 < a < b` and `1 ≤ R a` then
`log b - R b < log a - R a`. -/
theorem log_sub_mul_lt_of_one_le_mul {R a b : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : 1 ≤ R * a) :
    Real.log b - R * b < Real.log a - R * a := by
  have hb0 : 0 < b := ha.trans hab
  have h1 := Real.log_lt_sub_one_of_pos (div_pos hb0 ha) (one_lt_div ha |>.2 hab).ne'
  rw [Real.log_div hb0.ne' ha.ne'] at h1
  have h2 : b / a - 1 ≤ R * (b - a) := by
    rw [div_sub_one ha.ne', div_le_iff₀ ha]
    nlinarith [mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 ha1)]
  linarith

end Epidemics.KermackMcKendrick
