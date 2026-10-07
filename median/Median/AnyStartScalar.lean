import Mathlib

/-! # Any start: scalar inequalities

Real-number facts used by `Median/AnyStart.lean`, stated for arbitrary reals:

* round budgets: ceilings add up (`ceil_add_ceil_le`, `mul_ceil_le_ceil`);
* the union bound of the reduction to two values: `c³ ≤ x` once `3c ≤ log x`
  (`pow_three_le_of_log`), hence `x (c/x)³ ≤ (3c + 3)/x` (`mul_div_pow_three_le`);
* the constants of symmetry breaking near balance (`sq_mul_one_sub_sq_ge`,
  `le_abs_two_mul_add`, `near_const_le`);
* the error of the escape phase (`escape_error_le`), from `log x ^ 4 / 24 ≤ x`
  (`log_pow_four_div_le`).
-/

namespace Median
open Real

/-! ### Round budgets -/

/-- Two ceilings fit under a third: `⌈a⌉₊ + ⌈b⌉₊ ≤ ⌈c⌉₊` when `a + b + 2 ≤ c`. -/
lemma ceil_add_ceil_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b + 2 ≤ c) :
    ⌈a⌉₊ + ⌈b⌉₊ ≤ ⌈c⌉₊ := by
  have ha' := Nat.ceil_lt_add_one ha
  have hb' := Nat.ceil_lt_add_one hb
  have hc := Nat.le_ceil c
  have : ((⌈a⌉₊ + ⌈b⌉₊ : ℕ) : ℝ) ≤ ⌈c⌉₊ := by
    push_cast
    linarith
  exact_mod_cast this

/-- `k` copies of `⌈a⌉₊` fit under `⌈b⌉₊` when `k (a + 1) ≤ b`. -/
lemma mul_ceil_le_ceil {k : ℕ} {a b : ℝ} (ha : 0 ≤ a) (h : k * (a + 1) ≤ b) :
    k * ⌈a⌉₊ ≤ ⌈b⌉₊ := by
  have ha' := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one ha).le (Nat.cast_nonneg (α := ℝ) k)
  have hb := Nat.le_ceil b
  have : ((k * ⌈a⌉₊ : ℕ) : ℝ) ≤ ⌈b⌉₊ := by
    push_cast
    linarith
  exact_mod_cast this

/-! ### The union bound over values -/

/-- `c³ ≤ x` as soon as `3c ≤ log x`, since `c ≤ eᶜ`. -/
lemma pow_three_le_of_log {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (h : 3 * c ≤ log x) :
    c ^ 3 ≤ x := by
  have hce : c ≤ exp c := by linarith [add_one_le_exp c]
  calc c ^ 3 ≤ exp c ^ 3 := pow_le_pow_left₀ hc hce 3
    _ = exp (3 * c) := by rw [← exp_nat_mul]; norm_num
    _ ≤ exp (log x) := exp_le_exp.mpr h
    _ = x := exp_log hx

/-- `x (c/x)³ ≤ (3c + 3)/x` when `c³ ≤ x`: three amplified blocks beat a union bound over `x`
values. -/
lemma mul_div_pow_three_le {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (h : c ^ 3 ≤ x) :
    x * (c / x) ^ 3 ≤ (3 * c + 3) / x := by
  have e : x * (c / x) ^ 3 = c ^ 3 / x ^ 2 := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) hx]
  have h1 := mul_le_mul_of_nonneg_right h hx.le
  have h2 : 0 ≤ (3 * c + 2) * x ^ 2 := by positivity
  nlinarith

/-! ### Symmetry breaking near balance -/

/-- `z² (1 - z²) ≥ 1/10` for `z ∈ [3/8, 5/8]`. -/
lemma sq_mul_one_sub_sq_ge {z : ℝ} (h1 : 3 / 8 ≤ z) (h2 : z ≤ 5 / 8) :
    1 / 10 ≤ z ^ 2 * (1 - z ^ 2) := by
  have hw1 : 9 / 64 ≤ z ^ 2 := by nlinarith
  have hw2 : z ^ 2 ≤ 25 / 64 := by nlinarith
  linarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hw2)]

/-- A large fluctuation survives a small shift: if `4 Z² ≥ s²/10` and `|m| ≤ 3s/128`, then
`|2Z + m| ≥ s/4`. -/
lemma le_abs_two_mul_add {s Z m : ℝ} (hZ : s ^ 2 / 10 ≤ 4 * Z ^ 2) (hm : |m| ≤ 3 / 128 * s) :
    s / 4 ≤ |2 * Z + m| := by
  by_contra hlt
  push Not at hlt
  have h1 : |2 * Z| < 35 / 128 * s := by
    have := abs_sub_abs_le_abs_sub (2 * Z) (-m)
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  have h2 : (2 * Z) ^ 2 < (35 / 128 * s) ^ 2 := by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num)
  linarith [sq_nonneg s]

/-- The contraction near balance: `1 - (9/64)(1 - e^{-1/1024}) ≤ e^{-5/65536}`. -/
lemma near_const_le : 1 - 9 / 64 * (1 - exp (-(1 / 1024))) ≤ exp (-(5 / 65536)) := by
  have h1 : exp (-(1 / 1024 : ℝ)) ≤ 1024 / 1025 := by
    have h := add_one_le_exp (1 / 1024 : ℝ)
    rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    linarith
  have h2 := add_one_le_exp (-(5 / 65536 : ℝ))
  linarith

/-! ### The escape phase -/

/-- `(log x)⁴ / 24 ≤ x` for `x > 0` with `log x ≥ 0`. -/
lemma log_pow_four_div_le {x : ℝ} (hx : 0 < x) (hL : 0 ≤ log x) : log x ^ 4 / 24 ≤ x := by
  have h := pow_div_factorial_le_exp (log x) hL 4
  rw [exp_log hx] at h
  norm_num [Nat.factorial] at h
  linarith

/-- **The error of the escape phase.** With `L = log x ≥ 8192` and `2¹⁷ L ≤ T ≤ 2¹⁷ L + 1`,
for `p ≤ 1`: `e^{√L/2} (e^{-T/65536} p + T e^{1/131072 - √x/512}) ≤ 2/x`. The first term is
at most `e^{√L/2 - 2L} ≤ e^{-L}`; in the second, `e^{√L/2} ≤ x`, `T ≤ x` and
`√x ≥ L²/5` make it at most `x · x · x⁻³`. -/
lemma escape_error_le {x p : ℝ} {T : ℕ} (hx : 0 < x) (hL : 8192 ≤ log x)
    (hT1 : 131072 * log x ≤ T) (hT2 : (T : ℝ) ≤ 131072 * log x + 1) (hp1 : p ≤ 1) :
    exp (√(log x) / 2) * (exp (-(1 / 65536)) ^ T * p + T * exp (1 / 131072 - √x / 512))
      ≤ 2 / x := by
  have hx4 := log_pow_four_div_le hx (by linarith)
  have hexp : exp (log x) = x := exp_log hx
  obtain ⟨L, hLdef⟩ : ∃ L, L = log x := ⟨_, rfl⟩
  rw [← hLdef] at hL hT1 hT2 hx4 hexp ⊢
  have hL0 : 0 ≤ L := by linarith
  have hL4 : 8192 ^ 3 * L ≤ L ^ 4 := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hL 3) hL0
    linarith
  have hTx : (T : ℝ) ≤ x := by linarith
  have hsL : √L / 2 ≤ L := by
    have := mul_le_mul_of_nonneg_left (one_le_sqrt.mpr (by linarith : (1 : ℝ) ≤ L))
      (sqrt_nonneg L)
    linarith [mul_self_sqrt hL0]
  have hsx : L ^ 2 / 5 ≤ √x := le_sqrt_of_sq_le (by linarith [sq_nonneg (L ^ 2)])
  have hLL : 8192 * L ≤ L ^ 2 := by nlinarith
  -- the contraction term: `e^{√L/2} e^{-T/65536} p ≤ e^{-L} = 1/x`
  have hA : exp (√L / 2) * (exp (-(1 / 65536)) ^ T * p) ≤ 1 / x := by
    rw [← exp_nat_mul]
    calc exp (√L / 2) * (exp (T * -(1 / 65536)) * p)
        ≤ exp (√L / 2) * exp (T * -(1 / 65536)) :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (exp_pos _).le hp1) (exp_pos _).le
      _ = exp (√L / 2 + T * -(1 / 65536)) := (exp_add _ _).symm
      _ ≤ exp (-L) := exp_le_exp.mpr (by linarith)
      _ = 1 / x := by rw [exp_neg, hexp, one_div]
  -- the error term: `e^{√L/2} ≤ x`, `T ≤ x` and `e^{1/131072 - √x/512} ≤ e^{-3L} = 1/x³`
  have hB : exp (√L / 2) * (T * exp (1 / 131072 - √x / 512)) ≤ 1 / x := by
    have he1 : exp (√L / 2) ≤ x := hexp ▸ exp_le_exp.mpr hsL
    have he3 : exp (1 / 131072 - √x / 512) ≤ 1 / x ^ 3 := by
      calc exp (1 / 131072 - √x / 512) ≤ exp (-(3 * L)) := exp_le_exp.mpr (by linarith)
        _ = 1 / x ^ 3 := by
          rw [exp_neg, show (3 : ℝ) * L = ((3 : ℕ) : ℝ) * L by norm_num, exp_nat_mul, hexp,
            one_div]
    calc exp (√L / 2) * (T * exp (1 / 131072 - √x / 512))
        ≤ x * (x * (1 / x ^ 3)) :=
          mul_le_mul he1 (mul_le_mul hTx he3 (exp_pos _).le hx.le) (by positivity) hx.le
      _ = 1 / x := by field_simp
  rw [mul_add]
  calc _ ≤ 1 / x + 1 / x := add_le_add hA hB
    _ = 2 / x := by ring
