import Undecided.SequentialConsensus

/-! # From the explicit bounds to the `∃ C` statements

`prob_notCons_le` and `prob_notAllX_le` hold for `n ≥ 16` with an arbitrary level `L`. Choosing
`L = (c + 2) log n` turns `9 n e^{-L}` into `9 / n^{c+1}`, and the time
`256L + 34576nL + 6336n` into at most `40000 (c + 2) n log n`. A gap of `C √n log n` with
`C ≥ 40000 (c + 2)` makes `exp (-u₀² / (2N)) ≤ n^{-c}`. For `n < 16`, the constant
`C ≥ 16^c` makes the statements vacuous.
-/

namespace Undecided.Sequential
open Dynamics Real

variable {n : ℕ}

/-- The constant of the main theorems, for error exponent `c`. -/
noncomputable def constC (c : ℕ) : ℝ := 40000 * (c + 2) + 16 ^ c

lemma constC_ge (c : ℕ) : 40000 * ((c : ℝ) + 2) ≤ constC c := by
  unfold constC; have : (0 : ℝ) ≤ 16 ^ c := by positivity
  linarith

lemma nonempty_interaction (hn : 2 ≤ n) : Nonempty (Interaction n) :=
  ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩

lemma one_le_log (hn : 16 ≤ n) : 1 ≤ log n := by
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  rw [le_log_iff_exp_le (by linarith)]
  have := exp_one_lt_d9
  linarith

lemma exp_neg_nat_mul_log (hn : 0 < n) (k : ℕ) : exp (-((k : ℝ) * log n)) = 1 / (n : ℝ) ^ k := by
  rw [exp_neg, exp_nat_mul, exp_log (by exact_mod_cast hn), one_div]

/-- For `n < 16` the bound `1 - C / n^c` is not positive. -/
lemma small_n (c : ℕ) (hn : 2 ≤ n) (hsmall : n < 16) : 1 - constC c / (n : ℝ) ^ c ≤ 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) ^ c := by positivity
  have hle : (n : ℝ) ^ c ≤ 16 ^ c := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast hsmall.le
  have : (n : ℝ) ^ c ≤ constC c := by
    unfold constC; have : (0 : ℝ) ≤ 40000 * (c + 2) := by positivity
    linarith
  rw [sub_nonpos, le_div_iff₀ hpos, one_mul]
  exact this

/-- The time threshold of `prob_notCons_le` at level `L = (c + 2) log n`. -/
lemma threshold_le (c : ℕ) (hn : 16 ≤ n) (T : ℕ) (hT : constC c * n * log n ≤ T) :
    256 * (((c + 2 : ℕ) : ℝ) * log n) + 34576 * n * (((c + 2 : ℕ) : ℝ) * log n) + 6336 * n ≤
      T := by
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := one_le_log hn
  have hC := constC_ge c
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  have hnl : 0 ≤ (n : ℝ) * log n := by positivity
  have h1 : 256 * (((c : ℝ) + 2) * log n) ≤ 16 * ((c + 2) * (n * log n)) := by
    have hcl : 0 ≤ ((c : ℝ) + 2) * log n := by positivity
    nlinarith [mul_nonneg hcl (by linarith : (0 : ℝ) ≤ n - 16)]
  have h2 : 6336 * (n : ℝ) ≤ 3168 * ((c + 2) * (n * log n)) := by nlinarith
  have h3 : 40000 * ((c : ℝ) + 2) * (n * log n) ≤ constC c * n * log n := by
    rw [mul_assoc (constC c)]
    exact mul_le_mul_of_nonneg_right hC hnl
  nlinarith

/-- The error term `9 n e^{-L} + n^{-c}` is at most `C / n^c`. -/
lemma error_le (c : ℕ) (hn : 16 ≤ n) (ε : ℝ) (hε : ε ≤ 1 / (n : ℝ) ^ c) :
    9 * n * exp (-(((c + 2 : ℕ) : ℝ) * log n)) + ε ≤ constC c / (n : ℝ) ^ c := by
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ c := by positivity
  rw [exp_neg_nat_mul_log (by omega)]
  have h9 : 9 * (n : ℝ) * (1 / (n : ℝ) ^ (c + 2)) ≤ 9 / (n : ℝ) ^ c := by
    rw [pow_add, mul_one_div, div_le_div_iff₀ (by positivity) hpos]
    nlinarith [mul_nonneg (mul_nonneg hpos.le (by linarith : (0 : ℝ) ≤ n))
      (by linarith : (0 : ℝ) ≤ n - 1)]
  have hC := constC_ge c
  have h10 : 9 / (n : ℝ) ^ c + 1 / (n : ℝ) ^ c ≤ constC c / (n : ℝ) ^ c := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hpos.le
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    linarith
  linarith

/-- A gap of `C √n log n` beats the fluctuations: `exp (-u₀² / (2N)) ≤ n^{-c}`. -/
lemma gap_error_le (c : ℕ) (hn : 16 ≤ n) (u₀ : ℝ) (hu : constC c * √(n : ℝ) * log n ≤ u₀) :
    exp (-(u₀ ^ 2 / (2 * (60 * n * (((c + 2 : ℕ) : ℝ) * log n) + 11 * n)))) ≤
      1 / (n : ℝ) ^ c := by
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := one_le_log hn
  have hC := constC_ge c
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [← exp_neg_nat_mul_log (by omega)]
  apply exp_le_exp.mpr
  rw [neg_le_neg_iff]
  push_cast
  have hN : 0 < 2 * (60 * (n : ℝ) * ((c + 2) * log n) + 11 * n) := by positivity
  rw [le_div_iff₀ hN]
  -- `u₀² ≥ C² n log² n`
  have hsq : (√(n : ℝ)) ^ 2 = n := sq_sqrt (by positivity)
  have hC0 : 0 ≤ constC c * √(n : ℝ) * log n := by
    have : 0 ≤ constC c := by linarith
    positivity
  have hu2 : (constC c * √(n : ℝ) * log n) ^ 2 ≤ u₀ ^ 2 := pow_le_pow_left₀ hC0 hu 2
  have hexp : (constC c * √(n : ℝ) * log n) ^ 2 = constC c ^ 2 * n * log n ^ 2 := by
    rw [mul_pow, mul_pow, hsq]
  rw [hexp] at hu2
  -- `2N ≤ 142 (c + 2) n log n` and `C² ≥ 142 c (c + 2)`
  have hnl : 0 ≤ (n : ℝ) * log n := by positivity
  have h2N : 2 * (60 * (n : ℝ) * ((c + 2) * log n) + 11 * n) ≤ 142 * (c + 2) * (n * log n) := by
    nlinarith
  have hCsq : 142 * (c : ℝ) * (c + 2) ≤ constC c ^ 2 := by nlinarith
  have hlhs : (c : ℝ) * log n * (2 * (60 * (n : ℝ) * ((c + 2) * log n) + 11 * n)) ≤
      (c : ℝ) * log n * (142 * (c + 2) * (n * log n)) :=
    mul_le_mul_of_nonneg_left h2N (by positivity)
  have hmid : (c : ℝ) * log n * (142 * (c + 2) * (n * log n)) =
      142 * (c : ℝ) * (c + 2) * (n * log n ^ 2) := by ring
  have hfin : 142 * (c : ℝ) * (c + 2) * (n * log n ^ 2) ≤ constC c ^ 2 * n * log n ^ 2 := by
    rw [mul_assoc (constC c ^ 2)]
    exact mul_le_mul_of_nonneg_right hCsq (by positivity)
  linarith

/-- The non-blank hypothesis of [AAE08, Theorem 1] in terms of counts. -/
lemma nonblank_of_exists {s : Config n} (h : ∃ v, s v ≠ .u) : 1 ≤ count s .a + count s .b := by
  obtain ⟨v, hv⟩ := h
  cases hs : s v with
  | a => have := one_le_count hs; omega
  | b => have := one_le_count hs; omega
  | u => exact absurd hs hv

end Undecided.Sequential
