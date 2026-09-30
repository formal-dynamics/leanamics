import ThreeMajority.Chernoff
import Dynamics.Concentration

/-!
# Tail bounds used by the plurality analysis

The upper-bound proofs of Section 3 need three concentration statements for
a sum `X = ∑ᵢ Yᵢ(ωᵢ)` of independent `{0,1}`-valued coordinates:

* the multiplicative Chernoff lower tail `P(X ≤ (1-δ)μ) ≤ exp(-δ²μ/2)`
  (used in Lemma 3.4), obtained from the binary development's
  `ThreeMajority.avg_tail_le_log` and the scalar bound
  `(1-δ) log(1-δ) ≥ -δ + δ²/2`;
* the closed-form upper tail `ThreeMajority.avg_tail_ge_log_le`, reused as is
  (Lemma 3.7);
* Markov's inequality `P(X ≥ 1) ≤ 𝔼X` (Lemma 3.7).

Bernstein's and Hoeffding's inequalities come from `Dynamics.Concentration`.
The binary development states its Chernoff bounds with its own copy
`ThreeMajority.avg` of `Dynamics.avg`; the two agree definitionally
(`threeMajority_avg_eq`).
-/

namespace Plurality

open Finset Real Dynamics

lemma threeMajority_avg_eq {α : Type*} [Fintype α] (f : α → ℝ) :
    ThreeMajority.avg f = Dynamics.avg f := rfl

/-- `log x ≥ (x - 1/x)/2` for `0 < x ≤ 1`. -/
lemma half_sub_inv_le_log {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : (x - x⁻¹) / 2 ≤ Real.log x := by
  -- `ψ x = log x - (x - 1/x)/2` has `ψ' = -(x-1)²/(2x²) ≤ 0` and `ψ 1 = 0`
  have hderiv (y : ℝ) (hy : 0 < y) :
      HasDerivAt (fun y => Real.log y - (y - y⁻¹) / 2) (-(y - 1) ^ 2 / (2 * y ^ 2)) y := by
    have h := ((hasDerivAt_log hy.ne').sub
      (((hasDerivAt_id' y).sub (hasDerivAt_inv hy.ne')).div_const 2))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hanti : AntitoneOn (fun y => Real.log y - (y - y⁻¹) / 2) (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      rw [(hderiv y hy).deriv]
      have : 0 < 2 * y ^ 2 := by have := Set.mem_Ioi.mp hy; positivity
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (y - 1)]) this.le
  have h := hanti (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr one_pos) hx1
  simp only [Real.log_one, inv_one, sub_self, zero_div] at h
  linarith

/-- `(1 - δ) log(1 - δ) ≥ -δ + δ²/2` for `0 ≤ δ < 1`. -/
lemma one_sub_mul_log_one_sub_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    -δ + δ ^ 2 / 2 ≤ (1 - δ) * Real.log (1 - δ) := by
  have hx0 : 0 < 1 - δ := by linarith
  have h := half_sub_inv_le_log hx0 (by linarith)
  have h' := mul_le_mul_of_nonneg_left h hx0.le
  have e : (1 - δ) * ((1 - δ - (1 - δ)⁻¹) / 2) = -δ + δ ^ 2 / 2 := by
    field_simp
    ring
  linarith

variable {n : ℕ} {γ : Type*} [Fintype γ]

/-- **Multiplicative Chernoff lower tail**: `P(X ≤ (1-δ)μ) ≤ exp(-δ²μ/2)` for
`0 ≤ δ < 1`, where `μ = 𝔼X`. -/
theorem chernoff_lower [Nonempty γ] (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    avg (fun x : Fin n → γ =>
        if ∑ i, Y i (x i) ≤ (1 - δ) * ∑ i, avg (Y i) then (1 : ℝ) else 0)
      ≤ exp (-(δ ^ 2 * (∑ i, avg (Y i)) / 2)) := by
  set μ := ∑ i, avg (Y i) with hμ
  have hμ0 : 0 ≤ μ := sum_nonneg fun i _ =>
    avg_nonneg fun x => by rcases hY i x with h | h <;> simp [h]
  rcases hμ0.lt_or_eq with hμpos | hμzero
  · rcases hδ0.lt_or_eq with _ | hδzero
    · have hk0 : 0 < (1 - δ) * μ := mul_pos (by linarith) hμpos
      have hkμ : (1 - δ) * μ ≤ μ := by nlinarith
      have h := ThreeMajority.avg_tail_le_log Y hY hμ hk0 hkμ
      simp only [threeMajority_avg_eq] at h
      refine h.trans (exp_le_exp.mpr ?_)
      have hdiv : (1 - δ) * μ / μ = 1 - δ := by field_simp
      rw [hdiv]
      have := one_sub_mul_log_one_sub_ge hδ0 hδ1
      nlinarith
    · subst hδzero
      simp only [sub_zero, one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_mul, zero_div, neg_zero, exp_zero]
      calc _ ≤ avg (fun _ : Fin n → γ => (1 : ℝ)) := avg_le_avg fun x => by split <;> norm_num
        _ = 1 := avg_const 1
  · rw [← hμzero]
    simp only [mul_zero, zero_div, neg_zero, exp_zero]
    calc _ ≤ avg (fun _ : Fin n → γ => (1 : ℝ)) := avg_le_avg fun x => by split <;> norm_num
      _ = 1 := avg_const 1

/-- **Markov's inequality** for a sum of `{0,1}` coordinates: `P(X ≥ 1) ≤ 𝔼X`. -/
theorem markov_one (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1) :
    avg (fun x : Fin n → γ => if 1 ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0)
      ≤ ∑ i, avg (Y i) := by
  have hpt (x : Fin n → γ) : (if 1 ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0) ≤ ∑ i, Y i (x i) := by
    split_ifs with h
    · exact h
    · exact sum_nonneg fun i _ => by rcases hY i (x i) with h | h <;> simp [h]
  calc _ ≤ avg (fun x : Fin n → γ => ∑ i, Y i (x i)) := avg_le_avg hpt
    _ = ∑ i, avg (fun x : Fin n → γ => Y i (x i)) := avg_sum univ _
    _ ≤ ∑ i, avg (Y i) := by
        refine sum_le_sum fun i _ => le_of_eq ?_
        rcases isEmpty_or_nonempty γ with hγ | hγ
        · have : IsEmpty (Fin n → γ) := by
            refine ⟨fun x => hγ.false (x i)⟩
          simp [avg]
        · exact avg_eval n i (Y i)

end Plurality
