import Undecided.SequentialPotentials

/-! # The gap stays positive

While `u = x - y ≥ 0`, an interaction raises `u` (`xb`, `xy`) at least as often as it lowers it
(`yb`, `yx`): the two rates differ by `b u / (n(n-1)) ≥ 0`. Hence, for `t ≥ 0`,
`exp(-(t²/2) S_ch - t max(u, 0))` is a supermartingale, with `S_ch` the number of
state-changing interactions (`stepM`, using `cosh t ≤ exp(t²/2)`). This replaces the coupling
with a fair random walk and Azuma's inequality in the proof of [AAE08, Theorem 2].
-/

namespace Undecided.Sequential
open Dynamics Real

variable {n : ℕ}

/-- Weight of PM: `-(t²/2) I_ch`. -/
noncomputable def wM (t : ℝ) (i r : Op) : ℝ := -(t ^ 2 / 2) * (vbI i r + xyI i r)

/-- Potential of PM: `exp(-t max(x - y, 0))`. -/
noncomputable def fM (t : ℝ) (x y _b : ℝ) : ℝ := exp (-(t * max (x - y) 0))

/-- The numerator of the one-step formula of PM is nonpositive. -/
lemma gap_numerator (x y b t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hxy : y + 1 ≤ x ∨ x ≤ y) :
    x * b * (exp (-(t ^ 2 / 2)) * exp (-(t * max (x + 1 - y) 0)) -
        exp (-(t * max (x - y) 0))) +
      y * b * (exp (-(t ^ 2 / 2)) * exp (-(t * max (x - (y + 1)) 0)) -
        exp (-(t * max (x - y) 0))) +
      x * y * (exp (-(t ^ 2 / 2)) * exp (-(t * max (x - (y - 1)) 0)) -
        exp (-(t * max (x - y) 0))) +
      x * y * (exp (-(t ^ 2 / 2)) * exp (-(t * max (x - 1 - y) 0)) -
        exp (-(t * max (x - y) 0))) ≤ 0 := by
  have hk1 : exp (-(t ^ 2 / 2)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hk0 : 0 < exp (-(t ^ 2 / 2)) := exp_pos _
  rcases hxy with h | h
  · -- `u ≥ 1`: the two directions are `exp(∓t)` times the current potential
    have m0 : max (x - y) 0 = x - y := max_eq_left (by linarith)
    have m1 : max (x + 1 - y) 0 = x - y + 1 := by rw [max_eq_left (by linarith)]; ring
    have m2 : max (x - (y + 1)) 0 = x - y - 1 := by rw [max_eq_left (by linarith)]; ring
    have m3 : max (x - (y - 1)) 0 = x - y + 1 := by rw [max_eq_left (by linarith)]; ring
    have m4 : max (x - 1 - y) 0 = x - y - 1 := by rw [max_eq_left (by linarith)]; ring
    rw [m0, m1, m2, m3, m4]
    set P := exp (-(t * (x - y))) with hP
    have hplus : exp (-(t * (x - y + 1))) = P * exp (-t) := by rw [hP, ← exp_add]; ring_nf
    have hminus : exp (-(t * (x - y - 1))) = P * exp t := by rw [hP, ← exp_add]; ring_nf
    rw [hplus, hminus]
    have hP0 : 0 < P := exp_pos _
    set A := x * b + x * y
    set B := y * b + x * y
    have hAB : B ≤ A := by nlinarith
    have hB0 : 0 ≤ B := by positivity
    have hcosh : exp (-(t ^ 2 / 2)) * ((exp t + exp (-t)) / 2) ≤ 1 := by
      have h1 := cosh_le_exp_half_sq t
      rw [cosh_eq] at h1
      have h2 : exp (-(t ^ 2 / 2)) * exp (t ^ 2 / 2) = 1 := by rw [← exp_add]; simp
      calc exp (-(t ^ 2 / 2)) * ((exp t + exp (-t)) / 2)
          ≤ exp (-(t ^ 2 / 2)) * exp (t ^ 2 / 2) := mul_le_mul_of_nonneg_left h1 hk0.le
        _ = 1 := h2
    have hmono : exp (-t) ≤ exp t := exp_le_exp.mpr (by linarith)
    -- `A e^{-t} + B e^{t} ≤ (A + B) cosh t`
    have hmix : A * exp (-t) + B * exp t ≤ (A + B) * ((exp t + exp (-t)) / 2) := by
      nlinarith
    have hsum : exp (-(t ^ 2 / 2)) * (A * exp (-t) + B * exp t) ≤ A + B := by
      calc exp (-(t ^ 2 / 2)) * (A * exp (-t) + B * exp t)
          ≤ exp (-(t ^ 2 / 2)) * ((A + B) * ((exp t + exp (-t)) / 2)) :=
            mul_le_mul_of_nonneg_left hmix hk0.le
        _ = (A + B) * (exp (-(t ^ 2 / 2)) * ((exp t + exp (-t)) / 2)) := by ring
        _ ≤ (A + B) * 1 := mul_le_mul_of_nonneg_left hcosh (by linarith)
        _ = A + B := mul_one _
    have : x * b * (exp (-(t ^ 2 / 2)) * (P * exp (-t)) - P) +
        y * b * (exp (-(t ^ 2 / 2)) * (P * exp t) - P) +
        x * y * (exp (-(t ^ 2 / 2)) * (P * exp (-t)) - P) +
        x * y * (exp (-(t ^ 2 / 2)) * (P * exp t) - P) =
        P * (exp (-(t ^ 2 / 2)) * (A * exp (-t) + B * exp t) - (A + B)) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hP0.le (by linarith)
  · -- `u ≤ 0`: the potential is `1`, its maximum
    have m0 : max (x - y) 0 = 0 := max_eq_right (by linarith)
    rw [m0, mul_zero, neg_zero, exp_zero]
    have hle : ∀ w : ℝ, exp (-(t ^ 2 / 2)) * exp (-(t * max w 0)) - 1 ≤ 0 := by
      intro w
      have : exp (-(t * max w 0)) ≤ 1 :=
        exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (le_max_right _ _)))
      nlinarith [exp_pos (-(t * max w 0))]
    have hxb : 0 ≤ x * b := mul_nonneg hx hb
    have hyb : 0 ≤ y * b := mul_nonneg hy hb
    have hxy' : 0 ≤ x * y := mul_nonneg hx hy
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hxb (hle (x + 1 - y)),
      mul_nonpos_of_nonneg_of_nonpos hyb (hle (x - (y + 1))),
      mul_nonpos_of_nonneg_of_nonpos hxy' (hle (x - (y - 1))),
      mul_nonpos_of_nonneg_of_nonpos hxy' (hle (x - 1 - y))]

/-- **PM, one step.** -/
theorem stepM (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (s : Config n) :
    avg (fun p : Interaction n => exp (wM t (s p.1.1) (s p.1.2)) * cpot (fM t) (step s p)) ≤
      cpot (fM t) s := by
  unfold cpot
  rw [avg_step_counts hn s (wM t) 0 (fun i r h => by simp [wM, vbI_idle h, xyI_idle h]) (fM t)]
  have hch : ∀ i r : Op, ¬ Idle i r → wM t i r = -(t ^ 2 / 2) := by
    intro i r h
    unfold Idle at h
    cases i <;> cases r <;> simp_all [wM, vbI, xyI]
  rw [hch .a .u (by simp [Idle]), hch .b .u (by simp [Idle]), hch .a .b (by simp [Idle]),
    hch .b .a (by simp [Idle]), exp_zero, one_mul]
  refine add_div_le_self ?_ (two_le_cast hn)
  simp only [fM]
  have hxy : (count s .b : ℝ) + 1 ≤ count s .a ∨ (count s .a : ℝ) ≤ count s .b := by
    rcases lt_or_ge (count s .b) (count s .a) with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  exact gap_numerator _ _ _ t (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ht hxy

end Undecided.Sequential
