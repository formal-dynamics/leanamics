import Dynamics.Uniform

/-! # Weighted supermartingales along finite paths

A round-based process `l.foldl step s`, driven by i.i.d. uniform rounds, together with a per-step
weight `φ` and a potential `F`. If one round never increases `exp (φ s r) * F (step s r)` in
expectation, then `exp (∑_path φ) * F (state)` is a supermartingale, so its expectation after `T`
rounds is at most `F s` (`expList_exp_pathSum_le`). Markov's inequality then bounds the
probability that the path sum of `φ` is large (`expList_ind_le_of_weight`).

This replaces the stopping-time arguments of Angluin, Aspnes and Eisenstat [AAE08, §4.2] by a
fixed horizon: the counters of [AAE08, Table 1] are path sums of indicators.
-/

namespace Undecided.Sequential
open Dynamics

section Generic
variable {S R : Type*} (step : S → R → S)

/-- The sum of `φ` along the path from `s` driven by the rounds of `l`. -/
def pathSum (φ : S → R → ℝ) : S → List R → ℝ
  | _, [] => 0
  | s, r :: l => φ s r + pathSum φ (step s r) l

variable {step}

@[simp] lemma pathSum_nil (φ : S → R → ℝ) (s : S) : pathSum step φ s [] = 0 := rfl

@[simp] lemma pathSum_cons (φ : S → R → ℝ) (s : S) (r : R) (l : List R) :
    pathSum step φ s (r :: l) = φ s r + pathSum step φ (step s r) l := rfl

lemma pathSum_add (φ ψ : S → R → ℝ) (s : S) (l : List R) :
    pathSum step (fun s r => φ s r + ψ s r) s l = pathSum step φ s l + pathSum step ψ s l := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp only [pathSum_cons, ih]; ring

lemma pathSum_sub (φ ψ : S → R → ℝ) (s : S) (l : List R) :
    pathSum step (fun s r => φ s r - ψ s r) s l = pathSum step φ s l - pathSum step ψ s l := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp only [pathSum_cons, ih]; ring

lemma pathSum_const_mul (c : ℝ) (φ : S → R → ℝ) (s : S) (l : List R) :
    pathSum step (fun s r => c * φ s r) s l = c * pathSum step φ s l := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp only [pathSum_cons, ih]; ring

lemma pathSum_mono {φ ψ : S → R → ℝ} (h : ∀ s r, φ s r ≤ ψ s r) (s : S) (l : List R) :
    pathSum step φ s l ≤ pathSum step ψ s l := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp only [pathSum_cons]; exact add_le_add (h s r) (ih _)

@[simp] lemma pathSum_zero (s : S) (l : List R) : pathSum step (fun _ _ => 0) s l = 0 := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp [ih]

lemma pathSum_nonneg {φ : S → R → ℝ} (h : ∀ s r, 0 ≤ φ s r) (s : S) (l : List R) :
    0 ≤ pathSum step φ s l := by
  simpa using pathSum_mono (step := step) (φ := fun _ _ => 0) h s l

/-- **Finite-horizon supermartingale.** If one round never increases `exp φ · F` in expectation,
then `exp (∑_path φ) · F (state)` has expectation at most `F s` after any number of rounds. -/
theorem expList_exp_pathSum_le [Fintype R] {φ : S → R → ℝ} {F : S → ℝ}
    (h : ∀ s, avg (fun r => Real.exp (φ s r) * F (step s r)) ≤ F s) (T : ℕ) (s : S) :
    expList R T (fun l => Real.exp (pathSum step φ s l) * F (l.foldl step s)) ≤ F s := by
  induction T generalizing s with
  | zero => simp
  | succ T ih =>
    rw [expList_succ]
    refine le_trans (avg_le_avg fun r => ?_) (h s)
    have he : (fun l => Real.exp (pathSum step φ s (r :: l)) * F ((r :: l).foldl step s)) =
        fun l => Real.exp (φ s r) *
          (Real.exp (pathSum step φ (step s r) l) * F (l.foldl step (step s r))) := by
      funext l
      rw [pathSum_cons, Real.exp_add, List.foldl_cons, mul_assoc]
    rw [he, expList_const_mul]
    exact mul_le_mul_of_nonneg_left (ih _) (Real.exp_pos _).le

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

section Lists
variable {α : Type*} [Fintype α]

/-- `expList α T` only evaluates its argument on lists of length `T`. -/
lemma expList_le_expList_of_length {T : ℕ} {F G : List α → ℝ}
    (h : ∀ l : List α, l.length = T → F l ≤ G l) : expList α T F ≤ expList α T G := by
  induction T generalizing F G with
  | zero => exact h [] rfl
  | succ T ih =>
    rw [expList_succ, expList_succ]
    exact avg_le_avg fun a => ih fun l hl => h (a :: l) (by simp [hl])

/-- The complementary event has the complementary probability. -/
lemma expList_one_sub [Nonempty α] (T : ℕ) (G : List α → ℝ) :
    expList α T (fun l => 1 - G l) = 1 - expList α T G := by
  have h := expList_add (α := α) T (fun _ => 1) (fun l => (-1) * G l)
  simp only [expList_const, expList_const_mul] at h
  rw [show (fun l => 1 - G l) = fun l => 1 + (-1) * G l by funext l; ring, h]
  ring

end Lists

end Undecided.Sequential
