import Mathlib

/-!
# Scalar facts shared by the packages

Real and natural-number inequalities that several model packages used to prove locally, mostly
to count rounds and phases in high-probability statements. No probability is involved.

* Round budgets: ceilings add up (`ceil_add_ceil_le`, `mul_ceil_le_ceil`), and
  `⌈a y⌉₊ ≤ ⌈b y⌉₊` for `0 ≤ a ≤ b` (`nat_ceil_mul_le_of_le`).
* Phase counts: `w ≤ q ^ ⌈log w / log q⌉₊` for `q > 1` (`le_pow_ceil_real`, and `le_pow_ceil`
  for `w = n : ℕ`); geometric growth by a factor `q` passes `N` within `log (N/Δ) / log q + 2`
  steps (`exists_lt_pow_mul`), and `2 ^ 2 ^ T` passes `N ≥ 2` within `2 log log N + 3` steps
  (`exists_le_two_pow_two_pow`).
* Powers of logarithms: `c³ ≤ x` once `3c ≤ log x` (`pow_three_le_of_log`),
  `log n ^ 3 / 6 ≤ n` (`log_cube_le`) and `log x ^ 4 / 24 ≤ x` (`log_pow_four_div_le`), all from
  Mathlib's `Real.pow_div_factorial_le_exp`; and `ε/2 ≤ log (1 + ε)` on `[0, 1]`
  (`half_le_log_one_add`).
* The failure budget `S · N⁻² ≤ C/N` for `S ≤ C N` (`mul_one_div_sq_le`).

The bounds `1/2 ≤ log 2 ≤ 1` and the monotonicity of `√(ℓ x)` in `x` are used directly from
Mathlib (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`, `Real.sqrt_le_sqrt`). Each docstring names
the package lemmas that the statement replaces.
-/

namespace Dynamics

open Real

/-! ### Round budgets -/

/-- Two ceilings fit under a third: `⌈a⌉₊ + ⌈b⌉₊ ≤ ⌈c⌉₊` when `a + b + 2 ≤ c`. Replaces
`Median.ceil_add_ceil_le`. -/
theorem ceil_add_ceil_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b + 2 ≤ c) :
    ⌈a⌉₊ + ⌈b⌉₊ ≤ ⌈c⌉₊ := by
  have ha' := Nat.ceil_lt_add_one ha
  have hb' := Nat.ceil_lt_add_one hb
  have hc := Nat.le_ceil c
  have : ((⌈a⌉₊ + ⌈b⌉₊ : ℕ) : ℝ) ≤ ⌈c⌉₊ := by
    push_cast
    linarith
  exact_mod_cast this

/-- `k` copies of `⌈a⌉₊` fit under `⌈b⌉₊` when `k (a + 1) ≤ b`. Replaces
`Median.mul_ceil_le_ceil`. -/
theorem mul_ceil_le_ceil {k : ℕ} {a b : ℝ} (ha : 0 ≤ a) (h : k * (a + 1) ≤ b) :
    k * ⌈a⌉₊ ≤ ⌈b⌉₊ := by
  have ha' := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one ha).le (Nat.cast_nonneg (α := ℝ) k)
  have hb := Nat.le_ceil b
  have : ((k * ⌈a⌉₊ : ℕ) : ℝ) ≤ ⌈b⌉₊ := by
    push_cast
    linarith
  exact_mod_cast this

/-- `⌈a y⌉₊ ≤ ⌈b y⌉₊` for `0 ≤ a ≤ b`, whatever the sign of `y` (both vanish if `y ≤ 0`).
Replaces `Median.nat_ceil_mul_le_of_le`. -/
theorem nat_ceil_mul_le_of_le {a b y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ⌈a * y⌉₊ ≤ ⌈b * y⌉₊ := by
  rcases le_total 0 y with hy | hy
  · exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hab hy)
  · rw [Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos ha hy)]
    exact Nat.zero_le _

/-! ### Phase counts -/

/-- `w ≤ q ^ ⌈log w / log q⌉₊` for `w ≥ 1` and `q > 1`. Replaces `Median.le_pow_ceil_real`. -/
theorem le_pow_ceil_real {w : ℝ} (hw : 1 ≤ w) {q : ℝ} (hq : 1 < q) :
    w ≤ q ^ ⌈log w / log q⌉₊ := by
  have hlq : 0 < log q := log_pos hq
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hpow0 : 0 < q ^ ⌈log w / log q⌉₊ := pow_pos (lt_trans zero_lt_one hq) _
  rw [← log_le_log_iff hw0 hpow0, log_pow]
  have := Nat.le_ceil (log w / log q)
  rwa [div_le_iff₀ hlq] at this

/-- `n ≤ q ^ ⌈log n / log q⌉₊` for `n ≥ 1` and `q > 1`: after that many phases of growth by a
factor `q`, a quantity starting at `1` exceeds `n`. Replaces `Median.le_pow_ceil`,
`Plurality.le_pow_ceil` and `Undecided.le_pow_ceil`. -/
theorem le_pow_ceil {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 1 < q) :
    (n : ℝ) ≤ q ^ ⌈log n / log q⌉₊ :=
  le_pow_ceil_real (by exact_mod_cast hn) hq

/-- **Geometric growth.** Growing by a factor `q > 1` per step from `Δ > 0`, the value exceeds
`N ≥ Δ` after some `T ≤ log (N/Δ) / log q + 2` steps. Replaces `Median.exists_lt_pow_mul`. -/
theorem exists_lt_pow_mul {q : ℝ} (hq : 1 < q) {Δ N : ℝ} (hΔ : 0 < Δ) (hΔN : Δ ≤ N) :
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
`T ≤ 2 log log N + 3`. Replaces `Median.exists_le_two_pow_two_pow`. -/
theorem exists_le_two_pow_two_pow {N : ℝ} (hN : 2 ≤ N) :
    ∃ T : ℕ, N ≤ 2 ^ 2 ^ T ∧ (T : ℝ) ≤ 2 * log (log N) + 3 := by
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl2' : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hl21 : log (2 : ℝ) ≤ 1 := by linarith [log_two_lt_d9]
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

/-! ### Powers of logarithms -/

/-- `c³ ≤ x` as soon as `3c ≤ log x`, since `c ≤ eᶜ`. Replaces `Median.pow_three_le_of_log`. -/
theorem pow_three_le_of_log {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (h : 3 * c ≤ log x) :
    c ^ 3 ≤ x := by
  have hce : c ≤ exp c := by linarith [add_one_le_exp c]
  calc c ^ 3 ≤ exp c ^ 3 := pow_le_pow_left₀ hc hce 3
    _ = exp (3 * c) := by rw [← exp_nat_mul]; norm_num
    _ ≤ exp (log x) := exp_le_exp.mpr h
    _ = x := exp_log hx

/-- `(log n)³ / 6 ≤ n` for `n ≥ 1` (`eˣ ≥ x³/6` at `x = log n`). Replaces
`Undecided.log_cube_le`. -/
theorem log_cube_le {n : ℕ} (hn : 1 ≤ n) : log (n : ℝ) ^ 3 / 6 ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ log n := log_nonneg (by exact_mod_cast hn)
  have h1 := pow_div_factorial_le_exp (log (n : ℝ)) hL0 3
  rw [exp_log hn0] at h1
  norm_num [Nat.factorial] at h1
  linarith

/-- `(log x)⁴ / 24 ≤ x` for `x > 0` with `log x ≥ 0`. Replaces `Median.log_pow_four_div_le`. -/
theorem log_pow_four_div_le {x : ℝ} (hx : 0 < x) (hL : 0 ≤ log x) : log x ^ 4 / 24 ≤ x := by
  have h := pow_div_factorial_le_exp (log x) hL 4
  rw [exp_log hx] at h
  norm_num [Nat.factorial] at h
  linarith

/-- `ε/2 ≤ log (1 + ε)` for `0 ≤ ε ≤ 1`, from `1 - 1/x ≤ log x`. Replaces
`Undecided.Plurality.half_le_log_one_add`. -/
theorem half_le_log_one_add {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : ε / 2 ≤ log (1 + ε) := by
  have h := one_sub_inv_le_log_of_pos (x := 1 + ε) (by linarith)
  have e : 1 - (1 + ε)⁻¹ = ε / (1 + ε) := by field_simp; ring
  rw [e] at h
  have : ε / 2 ≤ ε / (1 + ε) := div_le_div_of_nonneg_left h0 (by linarith) (by linarith)
  linarith

/-! ### Failure budgets -/

/-- **The failure budget.** `S · N⁻² ≤ C/N` whenever `S ≤ C N` (and `N > 0`). Replaces
`Median.mul_one_div_sq_le`. -/
theorem mul_one_div_sq_le {N S C : ℝ} (hN : 0 < N) (hS : S ≤ C * N) :
    S * (1 / N ^ 2) ≤ C / N := by
  rw [mul_one_div, div_le_div_iff₀ (by positivity) hN]
  have p := mul_le_mul_of_nonneg_right hS hN.le
  calc S * N ≤ C * N * N := p
    _ = C * N ^ 2 := by ring

end Dynamics
