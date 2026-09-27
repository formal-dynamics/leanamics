import Dynamics.Kernel

/-! # Existence of stationary weights by Cesàro averages and compactness -/
namespace Dynamics
open Finset Filter Topology
namespace Kernel
variable {α : Type*} [Fintype α]

/-- Evolve a distribution by one transition. -/
noncomputable def advance (K : Kernel α) (p : Distribution α) : Distribution α where
  weight b := ∑ a, p.weight a * (K a).weight b
  nonneg b := sum_nonneg fun a _ => mul_nonneg (p.nonneg a) ((K a).nonneg b)
  sum_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, (K _).sum_one, mul_one]
    exact p.sum_one

/-- Distribution of the state at time `n`. -/
noncomputable def law (K : Kernel α) (p : Distribution α) : ℕ → Distribution α
  | 0 => p
  | n + 1 => K.advance (K.law p n)

/-- Cesàro averages over the first `n + 1` distributions. -/
noncomputable def cesaro (K : Kernel α) (p : Distribution α) (n : ℕ) : Distribution α where
  weight a := (∑ t ∈ range (n + 1), (K.law p t).weight a) / (n + 1 : ℝ)
  nonneg a := div_nonneg (sum_nonneg fun t _ => (K.law p t).nonneg a) (by positivity)
  sum_one := by
    rw [← sum_div, sum_comm]
    simp_rw [(K.law p _).sum_one]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    exact div_self (by positivity)

lemma weight_le_one (p : Distribution α) (a : α) : p.weight a ≤ 1 := by
  rw [← p.sum_one]
  exact single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

/-- The defect of stationarity telescopes to two endpoint distributions. -/
lemma cesaro_defect (K : Kernel α) (p : Distribution α) (n : ℕ) (b : α) :
    (K.advance (K.cesaro p n)).weight b - (K.cesaro p n).weight b =
      ((K.law p (n + 1)).weight b - p.weight b) / (n + 1 : ℝ) := by
  simp only [advance, cesaro, div_mul_eq_mul_div, ← sum_div]
  simp_rw [sum_mul]
  rw [sum_comm]
  have h (t : ℕ) : (∑ a, (K.law p t).weight a * (K a).weight b) =
      (K.law p (t + 1)).weight b := rfl
  simp_rw [h]
  rw [← sub_div]
  congr 1
  have ht := sum_range_sub (fun t => (K.law p t).weight b) (n + 1)
  simpa [sum_sub_distrib, law] using ht

/-- Every stochastic matrix on a finite nonempty type has a stationary distribution. -/
theorem exists_stationary [Nonempty α] (K : Kernel α) : ∃ p, K.Stationary p := by
  let p := Distribution.uniform α
  obtain ⟨w, hw, φ, hφ, hwφ⟩ := (isCompact_stdSimplex ℝ α).tendsto_subseq
    (fun n => show (K.cesaro p n).weight ∈ stdSimplex ℝ α from
      ⟨(K.cesaro p n).nonneg, (K.cesaro p n).sum_one⟩)
  refine ⟨⟨w, hw.1, hw.2⟩, fun b => ?_⟩
  have hcoord (a : α) : Tendsto (fun n => (K.cesaro p (φ n)).weight a) atTop (𝓝 (w a)) :=
    (tendsto_pi_nhds.mp hwφ) a
  have hlim : Tendsto
      (fun n => (K.advance (K.cesaro p (φ n))).weight b - (K.cesaro p (φ n)).weight b)
      atTop (𝓝 ((∑ a, w a * (K a).weight b) - w b)) :=
    (tendsto_finsetSum _ (fun a _ => (hcoord a).mul_const _)).sub (hcoord b)
  have hz : Tendsto
      (fun n => (K.advance (K.cesaro p n)).weight b - (K.cesaro p n).weight b)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => (n + 1 : ℝ)⁻¹)
    · intro n
      rw [cesaro_defect, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
      have hb : |(K.law p (n + 1)).weight b - p.weight b| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(K.law p (n + 1)).nonneg b, p.nonneg b,
          weight_le_one (K.law p (n + 1)) b, weight_le_one p b]
      simpa [one_div] using div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ n + 1)
    · have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (show Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) from tendsto_inv_atTop_zero).comp
          (hn.comp (tendsto_add_atTop_nat 1))
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim (hz.comp hφ.tendsto_atTop))

end Kernel
end Dynamics
