import Dynamics.Scalar

/-! # Many values: scalar facts for the fast consensus proof

Real-number facts behind `binary_consensus_fast` (no probability involved): the quadratic
saturation thresholds `q_j = (N/4) (1/2)^(2^j)`, with `q_0 = N/8`, `4 q_j² / N = q_(j+1)`
(`quad_threshold_succ`) and `q_T ≤ 1/4` once `N ≤ 2 ^ 2 ^ T`; and `max_sq_div_le`: flooring the
thresholds at `β ≤ N/4` is compatible with `q ↦ 4q²/N`.

The generic facts of the proof (round counts of geometric and doubly exponential growth,
`exists_lt_pow_mul` and `exists_le_two_pow_two_pow`; the failure budget `mul_one_div_sq_le`;
`nat_ceil_mul_le_of_le`) are in `Dynamics/Scalar.lean`.
-/

namespace Median

open Real

/-! ### The quadratic saturation thresholds `q_j = (N/4) (1/2)^(2^j)` -/

/-- The first quadratic saturation threshold is `q_0 = N/8`. -/
lemma quad_threshold_zero (N : ℝ) : N / 4 * (1 / 2 : ℝ) ^ 2 ^ 0 = N / 8 := by
  norm_num
  ring

/-- The quadratic saturation thresholds square their relative size: `4 q_j² / N = q_(j+1)`. -/
lemma quad_threshold_succ {N : ℝ} (hN : N ≠ 0) (j : ℕ) :
    4 * (N / 4 * (1 / 2 : ℝ) ^ 2 ^ j) ^ 2 / N = N / 4 * (1 / 2 : ℝ) ^ 2 ^ (j + 1) := by
  have e : (1 / 2 : ℝ) ^ 2 ^ (j + 1) = ((1 / 2 : ℝ) ^ 2 ^ j) ^ 2 := by
    rw [pow_succ, pow_mul]
  rw [e]
  field_simp

/-- Once `N ≤ 2 ^ 2 ^ T`, the threshold `q_T` is at most `1/4`. -/
lemma quad_threshold_small {N : ℝ} (hN : 0 < N) {T : ℕ} (hT : N ≤ 2 ^ 2 ^ T) :
    N / 4 * (1 / 2 : ℝ) ^ 2 ^ T ≤ 1 / 4 := by
  have e : (1 / 2 : ℝ) ^ 2 ^ T = 1 / (2 : ℝ) ^ 2 ^ T := by rw [div_pow, one_pow]
  rw [e]
  have h1 : 1 / (2 : ℝ) ^ 2 ^ T ≤ 1 / N := one_div_le_one_div_of_le hN hT
  have h2 : N / 4 * (1 / (2 : ℝ) ^ 2 ^ T) ≤ N / 4 * (1 / N) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : N / 4 * (1 / N) = 1 / 4 := by field_simp
  linarith

/-- Flooring at `β` is compatible with the quadratic recursion `q ↦ 4q²/N` when
`0 ≤ β ≤ N/4`: `max (4 (max q β)² / N) β ≤ max (4 q² / N) β`. -/
lemma max_sq_div_le {q β N : ℝ} (hβ0 : 0 ≤ β) (hN : 0 < N) (hβN : 4 * β ≤ N) :
    max (4 * (max q β) ^ 2 / N) β ≤ max (4 * q ^ 2 / N) β := by
  rcases le_total q β with h | h
  · rw [max_eq_right h]
    have h4 : 4 * β ^ 2 / N ≤ β := by
      rw [div_le_iff₀ hN]
      have p := mul_le_mul_of_nonneg_left hβN hβ0
      linarith only [p]
    rw [max_eq_right h4]
    exact le_max_right _ _
  · rw [max_eq_left h]

end Median
