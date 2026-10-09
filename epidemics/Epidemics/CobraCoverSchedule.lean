import Epidemics.CobraCoverNumerics

/-! # Phase lengths for the BIPS infection time (EPI-4, Theorem 2)

Under `1 - λ ≥ 128 √(log n / n)`, the three phase lengths
`T₁ = ⌈13 m / y + 72 log n / y²⌉₊`, `T₂ = ⌈24 log n / y⌉₊` and `T₃ = ⌈8 log n / y⌉₊`,
with `m = ⌈4000 log n / y²⌉₊` and `y = 1 - λ`, add up to at most `60000 log n / y³`.
-/

namespace Epidemics
open Real

/-- The three phase lengths, once each ceiling has been opened, add up to at most
`60000 log n / y³`. Kept separate so the arithmetic does not share a heartbeat budget
with the gap estimates. -/
lemma phase_sum_le {n : ℕ} {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (hlog0 : 0 < log (n : ℝ))
    (h16 : (16 : ℝ) ≤ 24 * log (n : ℝ)) :
    52000 * log (n : ℝ) / y ^ 3 + 72 * log (n : ℝ) / y ^ 2 + 32 * log (n : ℝ) / y +
      13 / y + 3 ≤ 60000 * log (n : ℝ) / y ^ 3 := by
  have hy2le : y ^ 2 ≤ 1 := pow_le_one₀ hy0.le hy1
  have hy3le : y ^ 3 ≤ 1 := pow_le_one₀ hy0.le hy1
  have hy3 : 0 < y ^ 3 := pow_pos hy0 3
  have hinv2 : (y ^ 2)⁻¹ * y ^ 3 = y := by
    rw [pow_succ y 2, ← mul_assoc, inv_mul_cancel₀ (pow_pos hy0 2).ne', one_mul]
  have hcancel2 (a : ℝ) : a / y ^ 2 * y ^ 3 = a * y := by
    rw [div_eq_mul_inv, mul_assoc, hinv2]
  have hinv1 : y⁻¹ * y ^ 3 = y ^ 2 := by
    rw [pow_succ' y 2, ← mul_assoc, inv_mul_cancel₀ hy0.ne', one_mul]
  have hcancel1 (a : ℝ) : a / y * y ^ 3 = a * y ^ 2 := by
    rw [div_eq_mul_inv, mul_assoc, hinv1]
  have hBeq : 72 * log (n : ℝ) * y / y ^ 3 = 72 * log (n : ℝ) / y ^ 2 := by
    rw [div_eq_iff hy3.ne']
    exact (hcancel2 (72 * log (n : ℝ))).symm
  have hCeq : 32 * log (n : ℝ) * y ^ 2 / y ^ 3 = 32 * log (n : ℝ) / y := by
    rw [div_eq_iff hy3.ne']
    exact (hcancel1 (32 * log (n : ℝ))).symm
  have hDeq : (13 : ℝ) * y ^ 2 / y ^ 3 = 13 / y := by
    rw [div_eq_iff hy3.ne']
    exact (hcancel1 13).symm
  have hEeq : 3 * y ^ 3 / y ^ 3 = (3 : ℝ) := by
    rw [div_eq_iff hy3.ne']
  have h72 : 72 * log (n : ℝ) * y ≤ 72 * log (n : ℝ) := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hy1 (mul_nonneg (by norm_num) hlog0.le)).trans_eq
      (one_mul _)
  have h32 : 32 * log (n : ℝ) * y ^ 2 ≤ 32 * log (n : ℝ) := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hy2le (mul_nonneg (by norm_num) hlog0.le)).trans_eq
      (one_mul _)
  have h13b : (13 : ℝ) * y ^ 2 ≤ 13 :=
    (mul_le_mul_of_nonneg_left hy2le (by norm_num : (0 : ℝ) ≤ 13)).trans_eq (mul_one _)
  have h3b : (3 : ℝ) * y ^ 3 ≤ 3 :=
    (mul_le_mul_of_nonneg_left hy3le (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (mul_one _)
  have h104 : (72 + 32 : ℝ) = 104 := by norm_num
  have h128c : (104 + 24 : ℝ) = 128 := by norm_num
  have hconst : (13 + 3 : ℝ) = 16 := by norm_num
  have hrest : 72 * log (n : ℝ) + 32 * log (n : ℝ) + 13 + 3 ≤ 128 * log (n : ℝ) := by
    calc 72 * log (n : ℝ) + 32 * log (n : ℝ) + 13 + 3
        = (72 + 32) * log (n : ℝ) + (13 + 3) := by ring
      _ = 104 * log (n : ℝ) + 16 := by rw [h104, hconst]
      _ ≤ 104 * log (n : ℝ) + 24 * log (n : ℝ) := add_le_add_right h16 _
      _ = (104 + 24) * log (n : ℝ) := by ring
      _ = 128 * log (n : ℝ) := by rw [h128c]
  have hextra : 72 * log (n : ℝ) * y + 32 * log (n : ℝ) * y ^ 2 + (13 : ℝ) * y ^ 2 +
      3 * y ^ 3 ≤ 128 * log (n : ℝ) :=
    (add_le_add (add_le_add (add_le_add h72 h32) h13b) h3b).trans hrest
  have hcoef : (52000 : ℝ) + 128 ≤ 60000 := by norm_num
  have hfact : 52000 * log (n : ℝ) + 128 * log (n : ℝ) =
      (52000 + 128) * log (n : ℝ) := (add_mul 52000 128 (log (n : ℝ))).symm
  have hmain : 52000 * log (n : ℝ) + 128 * log (n : ℝ) ≤ 60000 * log (n : ℝ) := by
    rw [hfact]
    exact mul_le_mul_of_nonneg_right hcoef hlog0.le
  have hnumRaw := (add_le_add_right hextra (52000 * log (n : ℝ))).trans hmain
  have hnum : 52000 * log (n : ℝ) + 72 * log (n : ℝ) * y + 32 * log (n : ℝ) * y ^ 2 +
      13 * y ^ 2 + 3 * y ^ 3 ≤ 60000 * log (n : ℝ) := by
    simpa [← add_assoc] using hnumRaw
  have hquot :
      (52000 * log (n : ℝ) + 72 * log (n : ℝ) * y + 32 * log (n : ℝ) * y ^ 2 +
        13 * y ^ 2 + 3 * y ^ 3) / y ^ 3 ≤ 60000 * log (n : ℝ) / y ^ 3 :=
    div_le_div_of_nonneg_right hnum hy3.le
  have hpieces : 52000 * log (n : ℝ) / y ^ 3 + 72 * log (n : ℝ) / y ^ 2 +
      32 * log (n : ℝ) / y + 13 / y + 3 =
      52000 * log (n : ℝ) / y ^ 3 + 72 * log (n : ℝ) * y / y ^ 3 +
        32 * log (n : ℝ) * y ^ 2 / y ^ 3 + 13 * y ^ 2 / y ^ 3 + 3 * y ^ 3 / y ^ 3 := by
    conv_lhs => rw [← hBeq, ← hCeq, ← hDeq, ← hEeq]
  -- `add_div` is applied to explicit arguments: rewriting it searches the wrong subterm.
  let a := 52000 * log (n : ℝ)
  let b := 72 * log (n : ℝ) * y
  let c := 32 * log (n : ℝ) * y ^ 2
  let d := (13 : ℝ) * y ^ 2
  let e := 3 * y ^ 3
  let z := y ^ 3
  have hjoin : a / z + b / z + c / z + d / z + e / z = (a + b + c + d + e) / z := by
    have h1 : a / z + b / z = (a + b) / z := (add_div a b z).symm
    have h2 : (a + b) / z + c / z = (a + b + c) / z := (add_div (a + b) c z).symm
    have h3 : (a + b + c) / z + d / z = (a + b + c + d) / z :=
      (add_div (a + b + c) d z).symm
    have h4 : (a + b + c + d) / z + e / z = (a + b + c + d + e) / z :=
      (add_div (a + b + c + d) e z).symm
    calc a / z + b / z + c / z + d / z + e / z
        = (a + b) / z + c / z + d / z + e / z := by
          conv_lhs => arg 1; arg 1; arg 1; rw [h1]
      _ = (a + b + c) / z + d / z + e / z := by
          conv_lhs => arg 1; arg 1; rw [h2]
      _ = (a + b + c + d) / z + e / z := by
          conv_lhs => arg 1; rw [h3]
      _ = (a + b + c + d + e) / z := h4
  rw [hpieces]
  have hsame : 52000 * log (n : ℝ) / y ^ 3 + 72 * log (n : ℝ) * y / y ^ 3 +
      32 * log (n : ℝ) * y ^ 2 / y ^ 3 + 13 * y ^ 2 / y ^ 3 + 3 * y ^ 3 / y ^ 3 =
      a / z + b / z + c / z + d / z + e / z := rfl
  exact (hsame.trans hjoin).trans_le hquot

lemma phase_schedule {n : ℕ} {y : ℝ} (hn : 2 ≤ n) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hgap : 128 * √(log (n : ℝ) / n) ≤ y) {m T₁ T₂ T₃ : ℕ}
    (hm : m = Nat.ceil (4000 * log (n : ℝ) / y ^ 2))
    (hT₁ : T₁ = Nat.ceil (13 * (m : ℝ) / y + 72 * log (n : ℝ) / y ^ 2))
    (hT₂ : T₂ = Nat.ceil (24 * log (n : ℝ) / y))
    (hT₃ : T₃ = Nat.ceil (8 * log (n : ℝ) / y)) :
    16385 ≤ n ∧ 2 * m ≤ n ∧ 4000 * log (n : ℝ) / y ^ 2 ≤ (9 * n / 10 : ℕ) ∧
      (T₂ : ℝ) ≤ n ∧ (T₁ + T₂ + T₃ : ℝ) ≤ 60000 * log (n : ℝ) / y ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hy2 : 0 < y ^ 2 := by positivity
  have hsqrt : √(log (n : ℝ) / n) ≤ y / 128 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
    linarith
  have hratio : 0 ≤ log (n : ℝ) / n := div_nonneg hlog0.le hn0.le
  have hsq := pow_le_pow_left₀ (sqrt_nonneg _) hsqrt 2
  rw [sq_sqrt hratio] at hsq
  have hsq' : log (n : ℝ) / n ≤ y ^ 2 / 16384 := by
    have : (y / 128) ^ 2 = y ^ 2 / 16384 := by ring
    linarith
  have hcross : log (n : ℝ) * 16384 ≤ (n : ℝ) * y ^ 2 := by
    rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 16384)] at hsq'
    linarith
  have hy2le : y ^ 2 ≤ 1 := pow_le_one₀ hy0.le hy1
  have hy3le : y ^ 3 ≤ 1 := pow_le_one₀ hy0.le hy1
  have hlogSmall : log (n : ℝ) ≤ (n : ℝ) / 16384 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16384)]
    have : log (n : ℝ) * 16384 ≤ (n : ℝ) * 1 := by nlinarith
    linarith
  have hnbig : 16385 ≤ n := gap_card_ge hn hlogSmall
  have hquarter : 4000 * log (n : ℝ) / y ^ 2 ≤ (n : ℝ) / 4 := by
    have hcoef : (4000 : ℝ) * 4 ≤ 16384 := by norm_num
    rw [div_le_div_iff₀ hy2 (by norm_num : (0 : ℝ) < 4)]
    have hmul := mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 4000)
    nlinarith [hcoef, hmul]
  have hmlt : (m : ℝ) < 4000 * log (n : ℝ) / y ^ 2 + 1 := by
    rw [hm]
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hlog0.le) hy2.le)
  have hone : (1 : ℝ) ≤ (n : ℝ) / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    exact_mod_cast (show 4 ≤ n by omega)
  have hmhalf : (m : ℝ) < (n : ℝ) / 2 := by linarith
  have htwo : 2 * m ≤ n := by
    have hlt : ((2 * m : ℕ) : ℝ) < n := by
      have : (2 : ℝ) * m < n := by linarith
      simpa using this
    exact Nat.le_of_lt (by exact_mod_cast hlt)
  have hfloor : ⌊(9 : ℝ) * n / 10⌋₊ = 9 * n / 10 := by
    have heq : (9 : ℝ) * n / 10 = ((9 * n : ℕ) : ℝ) / 10 := by push_cast; ring
    rw [heq]
    exact Nat.floor_div_eq_div (9 * n) 10
  have hsub : (9 : ℝ) * n / 10 - 1 < (9 * n / 10 : ℕ) := by
    have hlt := Nat.lt_floor_add_one ((9 : ℝ) * n / 10)
    rw [hfloor] at hlt
    linarith
  have h14 : (n : ℝ) / 4 ≤ (9 : ℝ) * n / 10 - 1 := by
    have h20 : (20 : ℝ) ≤ 13 * n := by exact_mod_cast (show 20 ≤ 13 * n by omega)
    have hstep : (n : ℝ) / 4 + 1 ≤ (9 : ℝ) * n / 10 := by
      field_simp
      linarith
    linarith
  have hnat : 4000 * log (n : ℝ) / y ^ 2 ≤ (9 * n / 10 : ℕ) := by linarith
  have hlogy2 : log (n : ℝ) / y ^ 2 ≤ (n : ℝ) / 16384 := by
    rw [div_le_div_iff₀ hy2 (by norm_num : (0 : ℝ) < 16384)]
    linarith
  have hsqlog : (log (n : ℝ) / y) ^ 2 ≤ (n : ℝ) * log (n : ℝ) / 16384 := by
    calc (log (n : ℝ) / y) ^ 2 = log (n : ℝ) * (log (n : ℝ) / y ^ 2) := by ring
      _ ≤ log (n : ℝ) * ((n : ℝ) / 16384) := mul_le_mul_of_nonneg_left hlogy2 hlog0.le
      _ = (n : ℝ) * log (n : ℝ) / 16384 := by ring
  have h128 : √(16384 : ℝ) = 128 := by
    rw [show (16384 : ℝ) = 128 ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  have hroot : log (n : ℝ) / y ≤ √((n : ℝ) * log (n : ℝ)) / 128 := by
    have hle := sqrt_le_sqrt hsqlog
    rw [sqrt_sq (div_nonneg hlog0.le hy0.le)] at hle
    have hdiv : √((n : ℝ) * log (n : ℝ) / 16384) =
        √((n : ℝ) * log (n : ℝ)) / 128 := by
      rw [sqrt_div (mul_nonneg hn0.le hlog0.le) 16384, h128]
    linarith
  have hlogn : log (n : ℝ) ≤ n := by
    have := log_le_sub_one_of_pos hn0
    linarith
  have hsqrtn : √((n : ℝ) * log (n : ℝ)) ≤ n := by
    have hsqn : (n : ℝ) * log (n : ℝ) ≤ n ^ 2 := by nlinarith
    have := sqrt_le_sqrt hsqn
    rwa [sqrt_sq hn0.le] at this
  have h24 : 24 * log (n : ℝ) / y + 1 ≤ n := by
    have hmul := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 24)
    have hcoef : (24 : ℝ) / 128 = 3 / 16 := by norm_num
    have hlin : (3 / 16) * (n : ℝ) + 1 ≤ n := by
      have h16 : (16 : ℝ) ≤ 13 * n := by exact_mod_cast (show 16 ≤ 13 * n by omega)
      linarith
    have hsqrtle : (3 / 16) * √((n : ℝ) * log (n : ℝ)) ≤ (3 / 16) * n :=
      mul_le_mul_of_nonneg_left hsqrtn (by norm_num : (0 : ℝ) ≤ 3 / 16)
    have hrew : 24 * (√((n : ℝ) * log (n : ℝ)) / 128) =
        (3 / 16) * √((n : ℝ) * log (n : ℝ)) := by
      have hsplit : 24 * (√((n : ℝ) * log (n : ℝ)) / 128) =
          (24 / 128) * √((n : ℝ) * log (n : ℝ)) := by ring
      rw [hsplit, hcoef]
    have hassoc : 24 * log (n : ℝ) / y = 24 * (log (n : ℝ) / y) := by ring
    calc 24 * log (n : ℝ) / y + 1 = 24 * (log (n : ℝ) / y) + 1 := by rw [hassoc]
      _ ≤ 24 * (√((n : ℝ) * log (n : ℝ)) / 128) + 1 := by linarith only [hmul]
      _ = (3 / 16) * √((n : ℝ) * log (n : ℝ)) + 1 := by rw [hrew]
      _ ≤ (3 / 16) * n + 1 := by linarith only [hsqrtle]
      _ ≤ n := hlin
  have hT2lt : (T₂ : ℝ) < 24 * log (n : ℝ) / y + 1 := by
    rw [hT₂]
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hlog0.le) hy0.le)
  have hT2le : (T₂ : ℝ) ≤ n := le_of_lt (hT2lt.trans_le h24)
  have hT1lt : (T₁ : ℝ) < 13 * (m : ℝ) / y + 72 * log (n : ℝ) / y ^ 2 + 1 := by
    rw [hT₁]
    exact Nat.ceil_lt_add_one (by positivity)
  have hT3lt : (T₃ : ℝ) < 8 * log (n : ℝ) / y + 1 := by
    rw [hT₃]
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hlog0.le) hy0.le)
  have h13 : 13 * (m : ℝ) / y < 52000 * log (n : ℝ) / y ^ 3 + 13 / y := by
    have hmul := mul_lt_mul_of_pos_left hmlt (div_pos (by norm_num : (0 : ℝ) < 13) hy0)
    have heq : (13 / y) * (4000 * log (n : ℝ) / y ^ 2 + 1) =
        52000 * log (n : ℝ) / y ^ 3 + 13 / y := by ring
    have hform : 13 * (m : ℝ) / y = (13 / y) * (m : ℝ) := by ring
    linarith
  have hsumle : (T₁ + T₂ + T₃ : ℝ) ≤
      52000 * log (n : ℝ) / y ^ 3 + 72 * log (n : ℝ) / y ^ 2 + 32 * log (n : ℝ) / y +
        13 / y + 3 := by
    have h1 := le_of_lt hT1lt
    have h2 := le_of_lt hT2lt
    have h3 := le_of_lt hT3lt
    have h4 := le_of_lt h13
    have h32log : 24 * log (n : ℝ) / y + 8 * log (n : ℝ) / y = 32 * log (n : ℝ) / y := by
      rw [← add_div]
      congr 1
      ring
    calc (T₁ : ℝ) + T₂ + T₃
        ≤ (13 * (m : ℝ) / y + 72 * log (n : ℝ) / y ^ 2 + 1) + (24 * log (n : ℝ) / y + 1) +
            (8 * log (n : ℝ) / y + 1) := by linarith only [h1, h2, h3]
      _ = 13 * (m : ℝ) / y + 72 * log (n : ℝ) / y ^ 2 +
            (24 * log (n : ℝ) / y + 8 * log (n : ℝ) / y) + 3 := by ring
      _ = 13 * (m : ℝ) / y + 72 * log (n : ℝ) / y ^ 2 + 32 * log (n : ℝ) / y + 3 := by
          rw [h32log]
      _ ≤ 52000 * log (n : ℝ) / y ^ 3 + 13 / y + 72 * log (n : ℝ) / y ^ 2 +
            32 * log (n : ℝ) / y + 3 := by linarith only [h4]
      _ = 52000 * log (n : ℝ) / y ^ 3 + 72 * log (n : ℝ) / y ^ 2 + 32 * log (n : ℝ) / y +
            13 / y + 3 := by ring
  have h16 : (16 : ℝ) ≤ 24 * log (n : ℝ) := by
    have hlog2 : log 2 ≤ log (n : ℝ) :=
      log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn)
    have := log_two_gt_d9
    nlinarith
  have hcomp : 52000 * log (n : ℝ) / y ^ 3 + 72 * log (n : ℝ) / y ^ 2 +
      32 * log (n : ℝ) / y + 13 / y + 3 ≤ 60000 * log (n : ℝ) / y ^ 3 :=
    phase_sum_le hy0 hy1 hlog0 h16
  refine ⟨hnbig, htwo, hnat, hT2le, ?_⟩
  exact le_trans hsumle hcomp

end Epidemics
