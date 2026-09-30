import ThreeMajority.Bounds

/-!
# Numerical facts for large `n`

The paper's statements hold "for sufficiently large `n`". The formal versions
make this explicit through a lower bound on `L = log n`, and express the powers
`n^{1/4}`, `n^{3/10}`, `n^{-1/5}` of the paper as real powers
`(n : ℝ) ^ (a : ℝ) = exp (a L)`. The bounds below are all derived from
the single-term Taylor bound `ThreeMajority.exp_ge_pow` and the series for
`log (1 - x)` in Mathlib.
-/

namespace Plurality

open Real

lemma rpow_eq_exp {n : ℕ} (hn : 1 ≤ n) (a : ℝ) : (n : ℝ) ^ a = exp (a * Real.log n) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn), mul_comm]

lemma natCast_eq_exp {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) = exp (Real.log n) :=
  (exp_log (by exact_mod_cast hn)).symm

/-- `exp y ≥ y⁷ / 5040`. -/
lemma exp_ge_pow_seven {y : ℝ} (hy : 0 ≤ y) : y ^ 7 / 5040 ≤ exp y := by
  have h := ThreeMajority.exp_ge_pow hy 7
  norm_num [Nat.factorial] at h
  linarith

/-- `exp y ≥ 1500` for `y ≥ 10`. -/
lemma fifteen_hundred_le_exp {y : ℝ} (hy : 10 ≤ y) : 1500 ≤ exp y := by
  have h := exp_ge_pow_seven (by linarith : (0 : ℝ) ≤ y)
  have : (10 : ℝ) ^ 7 ≤ y ^ 7 := pow_le_pow_left₀ (by norm_num) hy 7
  linarith

/-- `exp y ≥ 33.4 y²` for `y ≥ 12`. -/
lemma sq_mul_le_exp {y : ℝ} (hy : 12 ≤ y) : 34 * y ^ 2 ≤ exp y := by
  have h := exp_ge_pow_seven (by linarith : (0 : ℝ) ≤ y)
  have h5 : (12 : ℝ) ^ 5 ≤ y ^ 5 := pow_le_pow_left₀ (by norm_num) hy 5
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  nlinarith

/-- `exp y ≥ 8712 y` for `y ≥ 20`. -/
lemma mul_le_exp {y : ℝ} (hy : 20 ≤ y) : 8712 * y ≤ exp y := by
  have h := exp_ge_pow_seven (by linarith : (0 : ℝ) ≤ y)
  have h6 : (20 : ℝ) ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ (by norm_num) hy 6
  nlinarith

/-- `log (17/16) ≥ 0.0603`, from the series of `log (1 - 1/17)`. -/
lemma log_seventeen_sixteen : (603 / 10000 : ℝ) ≤ Real.log (17 / 16) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 17) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have e : Real.log (17 / 16) = -Real.log (16 / 17) := by
    rw [← Real.log_inv]; norm_num
  rw [e]
  have := (abs_le.mp h).2
  linarith

/-- `log (3L) ≤ 2 + 3L/20` (tangent bound at `exp 3 ≥ 20`). -/
lemma log_three_mul_le {L : ℝ} (hL : 0 < L) : Real.log (3 * L) ≤ 2 + 3 * L / 20 := by
  have h := ThreeMajority.log_le_tangent_div (show 0 < 3 * L by positivity) (exp_pos 3)
  rw [Real.log_exp] at h
  have : 3 * L / exp 3 ≤ 3 * L / 20 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) ThreeMajority.exp_three_ge_twenty
  linarith

end Plurality
