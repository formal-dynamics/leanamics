import Dynamics.Azuma

/-! # Weighted supermartingales along finite paths

A round-based process `l.foldl step s`, driven by i.i.d. uniform rounds, together with a per-step
weight `φ` and a potential `F`. If one round never increases `exp (φ s r) * F (step s r)` in
expectation, then `exp (∑_path φ) * F (state)` is a supermartingale, so its expectation after `T`
rounds is at most `F s` (`expList_exp_pathSum_le`, from the core
`Dynamics.expList_exp_incrementSum_le`). Markov's inequality then bounds the
probability that the path sum of `φ` is large (`expList_ind_le_of_weight`). The path sum
`pathSum` is the core `Dynamics.incrementSum` (with its algebra: `incrementSum_add`,
`incrementSum_mono`, ...).

This replaces the stopping-time arguments of Angluin, Aspnes and Eisenstat [AAE08, §4.2] by a
fixed horizon: the counters of [AAE08, Table 1] are path sums of indicators.
-/

namespace Undecided.Sequential
open Dynamics

section Generic
variable {S R : Type*} (step : S → R → S)

/-- The sum of `φ` along the path from `s` driven by the rounds of `l`: the core
`Dynamics.incrementSum`, under the name used in the statements below. -/
noncomputable abbrev pathSum (φ : S → R → ℝ) (s : S) (l : List R) : ℝ := incrementSum step φ s l

variable {step}

/-- **Finite-horizon supermartingale.** If one round never increases `exp φ · F` in expectation,
then `exp (∑_path φ) · F (state)` has expectation at most `F s` after any number of rounds
(the core's `Dynamics.expList_exp_incrementSum_le`). -/
theorem expList_exp_pathSum_le [Fintype R] {φ : S → R → ℝ} {F : S → ℝ}
    (h : ∀ s, avg (fun r => Real.exp (φ s r) * F (step s r)) ≤ F s) (T : ℕ) (s : S) :
    expList R T (fun l => Real.exp (pathSum step φ s l) * F (l.foldl step s)) ≤ F s :=
  expList_exp_incrementSum_le step h T s

/-- **Markov's inequality** for the supermartingale of `expList_exp_pathSum_le`: an event on which
`exp (∑_path φ) · F (state) ≥ m > 0` has probability at most `F s / m`. -/
theorem expList_ind_le_of_weight [Fintype R] {φ : S → R → ℝ} {F : S → ℝ} (hF : ∀ s, 0 ≤ F s)
    (h : ∀ s, avg (fun r => Real.exp (φ s r) * F (step s r)) ≤ F s) (T : ℕ) (s : S)
    (E : List R → Prop) [DecidablePred E] {m : ℝ} (hm : 0 < m)
    (hE : ∀ l, E l → m ≤ Real.exp (pathSum step φ s l) * F (l.foldl step s)) :
    expList R T (fun l => if E l then 1 else 0) ≤ F s / m := by
  have hpt (l : List R) : (if E l then (1 : ℝ) else 0) ≤
      m⁻¹ * (Real.exp (pathSum step φ s l) * F (l.foldl step s)) := by
    split_ifs with hl
    · rw [← div_eq_inv_mul, le_div_iff₀ hm, one_mul]
      exact hE l hl
    · exact mul_nonneg (inv_nonneg.mpr hm.le) (mul_nonneg (Real.exp_pos _).le (hF _))
  calc expList R T (fun l => if E l then 1 else 0)
      ≤ expList R T (fun l => m⁻¹ * (Real.exp (pathSum step φ s l) * F (l.foldl step s))) :=
        expList_le_expList hpt
    _ = m⁻¹ * expList R T (fun l => Real.exp (pathSum step φ s l) * F (l.foldl step s)) :=
        expList_const_mul _ _ _
    _ ≤ m⁻¹ * F s := mul_le_mul_of_nonneg_left (expList_exp_pathSum_le h T s)
        (inv_nonneg.mpr hm.le)
    _ = F s / m := by rw [div_eq_inv_mul]

end Generic

end Undecided.Sequential
