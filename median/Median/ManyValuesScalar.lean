import Mathlib

/-! # Many values: scalar facts for the fast consensus proof

Real-number facts behind `binary_consensus_fast` (no probability involved):

* `log_two_ge`, `le_pow_ceil_real`: `log 2 ≥ 1/2`, and `w ≤ q ^ ⌈log w / log q⌉₊`;
* `exists_lt_pow_mul`: growing by a factor `q > 1` per step from `Δ > 0`, the value exceeds
  `N ≥ Δ` within `log (N/Δ) / log q + 2` steps (round count of the growth phase);
* `exists_le_two_pow_two_pow`: `2 ^ 2 ^ T` exceeds `N ≥ 2` within `2 log log N + 3` steps
  (round count of the quadratic saturation phase);
* the quadratic saturation thresholds `q_j = (N/4) (1/2)^(2^j)`: `q_0 = N/8`,
  `4 q_j² / N = q_(j+1)` (`quad_threshold_succ`), and `q_T ≤ 1/4` once `N ≤ 2 ^ 2 ^ T`;
  `max_sq_div_le`: flooring the thresholds at `β ≤ N/4` is compatible with `q ↦ 4q²/N`;
* `mul_one_div_sq_le`: the failure budget `S · N⁻² ≤ C/N` for `S ≤ C N`;
* `nat_ceil_mul_le_of_le`: `⌈a y⌉₊ ≤ ⌈b y⌉₊` for `0 ≤ a ≤ b`, whatever the sign of `y`.
-/

namespace Median

open Real

/-- `log 2 ≥ 1/2`. -/
lemma log_two_ge : (1 / 2 : ℝ) ≤ log 2 := by
  have := log_two_gt_d9
  norm_num at this
  linarith

/-- `log 2 ≤ 1`. -/
lemma log_two_le_one : log (2 : ℝ) ≤ 1 := by
  have := log_two_lt_d9
  norm_num at this
  linarith

/-- `w ≤ q ^ ⌈log w / log q⌉₊` for `w ≥ 1` and `q > 1` (a real version of `le_pow_ceil`). -/
lemma le_pow_ceil_real {w : ℝ} (hw : 1 ≤ w) {q : ℝ} (hq : 1 < q) :
    w ≤ q ^ ⌈log w / log q⌉₊ := by
  have hlq : 0 < log q := log_pos hq
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hpow0 : 0 < q ^ ⌈log w / log q⌉₊ := pow_pos (lt_trans zero_lt_one hq) _
  rw [← log_le_log_iff hw0 hpow0, log_pow]
  have := Nat.le_ceil (log w / log q)
  rwa [div_le_iff₀ hlq] at this

/-- **Geometric growth.** Growing by a factor `q > 1` per step from `Δ > 0`, the value exceeds
`N ≥ Δ` after some `T ≤ log (N/Δ) / log q + 2` steps. -/
lemma exists_lt_pow_mul {q : ℝ} (hq : 1 < q) {Δ N : ℝ} (hΔ : 0 < Δ) (hΔN : Δ ≤ N) :
    ∃ T : ℕ, N < q ^ T * Δ ∧ (T : ℝ) ≤ log (N / Δ) / log q + 2 := by
  have hlq : 0 < log q := log_pos hq
  have hw : 1 ≤ N / Δ := (one_le_div hΔ).mpr hΔN
  refine ⟨⌈log (N / Δ) / log q⌉₊ + 1, ?_, ?_⟩
  · have h1 := le_pow_ceil_real hw hq
    rw [div_le_iff₀ hΔ] at h1
    have hpos : 0 < q ^ ⌈log (N / Δ) / log q⌉₊ * Δ :=
      mul_pos (pow_pos (lt_trans zero_lt_one hq) _) hΔ
    calc N ≤ q ^ ⌈log (N / Δ) / log q⌉₊ * Δ := h1
      _ < q ^ ⌈log (N / Δ) / log q⌉₊ * Δ * q := lt_mul_of_one_lt_right hpos hq
      _ = q ^ (⌈log (N / Δ) / log q⌉₊ + 1) * Δ := by ring
  · have h1 : ((⌈log (N / Δ) / log q⌉₊ : ℕ) : ℝ) < log (N / Δ) / log q + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (log_nonneg hw) hlq.le)
    push_cast
    linarith only [h1]

/-- **Doubly exponential growth.** If `N ≥ 2`, then `N ≤ 2 ^ 2 ^ T` for some
`T ≤ 2 log log N + 3`. -/
lemma exists_le_two_pow_two_pow {N : ℝ} (hN : 2 ≤ N) :
    ∃ T : ℕ, N ≤ 2 ^ 2 ^ T ∧ (T : ℝ) ≤ 2 * log (log N) + 3 := by
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl2' := log_two_ge
  have hl21 := log_two_le_one
  have hN0 : 0 < N := by linarith
  have hLN : log 2 ≤ log N := log_le_log (by norm_num) hN
  have hW1 : 1 ≤ log N / log 2 := by
    rw [le_div_iff₀ hl2]
    linarith
  refine ⟨⌈log (log N / log 2) / log 2⌉₊, ?_, ?_⟩
  · have hJ := le_pow_ceil_real hW1 (show (1 : ℝ) < 2 by norm_num)
    rw [div_le_iff₀ hl2] at hJ
    rw [← log_le_log_iff hN0 (by positivity), log_pow]
    push_cast
    exact hJ
  · have hlogW0 : 0 ≤ log (log N / log 2) := log_nonneg hW1
    have hW2 : log N / log 2 ≤ 2 * log N := by
      rw [div_le_iff₀ hl2]
      have p := mul_le_mul_of_nonneg_left hl2' (hl2.le.trans hLN)
      linarith only [p]
    have hlogW : log (log N / log 2) ≤ log 2 + log (log N) := by
      have h := log_le_log (by linarith) hW2
      rwa [log_mul (by norm_num) (by linarith)] at h
    have h1 : ((⌈log (log N / log 2) / log 2⌉₊ : ℕ) : ℝ) < log (log N / log 2) / log 2 + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hlogW0 hl2.le)
    have h2 : log (log N / log 2) / log 2 ≤ 2 * log (log N / log 2) := by
      rw [div_le_iff₀ hl2]
      have p := mul_le_mul_of_nonneg_left hl2' hlogW0
      linarith only [p]
    linarith only [h1, h2, hlogW, hl21]

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

/-- **The failure budget.** `S · N⁻² ≤ C/N` whenever `S ≤ C N` (and `N > 0`). -/
lemma mul_one_div_sq_le {N S C : ℝ} (hN : 0 < N) (hS : S ≤ C * N) :
    S * (1 / N ^ 2) ≤ C / N := by
  rw [mul_one_div, div_le_div_iff₀ (by positivity) hN]
  have p := mul_le_mul_of_nonneg_right hS hN.le
  calc S * N ≤ C * N * N := p
    _ = C * N ^ 2 := by ring

/-- `⌈a y⌉₊ ≤ ⌈b y⌉₊` for `0 ≤ a ≤ b`, whatever the sign of `y` (both vanish if `y ≤ 0`). -/
lemma nat_ceil_mul_le_of_le {a b y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : ⌈a * y⌉₊ ≤ ⌈b * y⌉₊ := by
  rcases le_total 0 y with hy | hy
  · exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hab hy)
  · rw [Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos ha hy)]
    exact Nat.zero_le _

end Median
