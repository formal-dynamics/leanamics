import Undecided.LowerBoundBasic
import Undecided.PluralityAssembly

/-! # Real inequalities for the `Ω(md(c))` lower bound

Range conversions `(C k) ≤ (n / log n)^{1/b} → (C k)^b log n ≤ n`, the deviation
`dev ℓ μ ≤ μ / 2` for a large mean, and the numerical bounds on `exp` used by the
descent and the plateau.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- From `C k ≤ (N / L)^{1/b}` to `(C k)^b L ≤ N`. -/
lemma pow_of_rpow {b : ℕ} {C k L N : ℝ} (hb : 0 < b) (hCk : 0 ≤ C * k) (hL : 0 < L)
    (hN : 0 ≤ N) (h : C * k ≤ (N / L) ^ ((1 : ℝ) / b)) : (C * k) ^ b * L ≤ N := by
  have hb0 : b ≠ 0 := hb.ne'
  have hpow := pow_le_pow_left₀ hCk h b
  rw [show (1 : ℝ) / (b : ℝ) = (b : ℝ)⁻¹ by field_simp,
    rpow_inv_natCast_pow (div_nonneg hN hL.le) hb0] at hpow
  rwa [le_div_iff₀ hL] at hpow

lemma one_lt_n_of_log {C : ℝ} (hC : 0 < C) {n : ℕ} (hL : C ≤ log n) : 1 < n := by
  by_contra h
  have : (n : ℝ) ≤ 1 := by exact_mod_cast not_lt.mp h
  have := log_nonpos (Nat.cast_nonneg n) this
  linarith

lemma log_pos_of_log {C : ℝ} (hC : 0 < C) {n : ℕ} (hL : C ≤ log n) : 0 < log n := by
  linarith

/-- `(k + 4) / n³ ≤ 5 / n²` for `2 ≤ n` and `k ≤ n`. -/
lemma bad_prob_le {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    ((k : ℝ) + 4) / (n : ℝ) ^ 3 ≤ 5 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rw [div_le_div_iff₀ hn3 hn2]
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (k : ℝ) + 4 ≤ n + 4 := by linarith
  have h2 : (n : ℝ) + 4 ≤ 5 * n := by linarith
  calc ((k : ℝ) + 4) * (n : ℝ) ^ 2 ≤ (n + 4) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (5 * n) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 5 * (n : ℝ) ^ 3 := by ring

/-- `5 / n² ≤ 5 / n` for `1 ≤ n`. -/
lemma five_div_sq_le {n : ℕ} (hn : 1 ≤ n) : 5 / (n : ℝ) ^ 2 ≤ 5 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) hn0 hpow

/-- A mean at least `14 ℓ` has deviation at most half the mean. -/
lemma dev_le_half {ℓ μ : ℝ} (hℓ : 0 ≤ ℓ) (hμ : 14 * ℓ ≤ μ) : dev ℓ μ ≤ μ / 2 := by
  have hsq : 3 * ℓ * (μ + 2 * ℓ) ≤ (μ / 2) ^ 2 := by nlinarith
  calc dev ℓ μ = √(3 * ℓ * (μ + 2 * ℓ)) := rfl
    _ ≤ √((μ / 2) ^ 2) := sqrt_le_sqrt hsq
    _ = μ / 2 := sqrt_sq (by linarith)

lemma exp_one_le_three : exp 1 ≤ 3 := by
  linarith [exp_one_lt_d9]

lemma exp_half_le_two : exp (1 / 2) ≤ 2 := by
  have hsq : exp (1 / 2) ^ 2 = exp 1 := by
    rw [← exp_nat_mul]
    ring_nf
  have hpos : (0 : ℝ) ≤ exp (1 / 2) := exp_nonneg _
  rw [← sq_le_sq₀ hpos (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsq]
  linarith [exp_one_lt_d9]

/-- `(1 + x)^t ≤ exp(x t)` for `0 ≤ x`. -/
lemma pow_one_add_le_exp {x : ℝ} (hx : 0 ≤ x) (t : ℕ) : (1 + x) ^ t ≤ exp (x * t) := by
  have hcomm : (1 + x) ^ t = (x + 1) ^ t := by ring
  rw [hcomm]
  calc (x + 1) ^ t ≤ exp x ^ t := pow_le_pow_left₀ (by linarith) (add_one_le_exp x) t
    _ = exp ((t : ℝ) * x) := by rw [← exp_nat_mul]
    _ = exp (x * t) := by ring_nf

lemma two_pow_ge_two_mul (j : ℕ) (hj : 1 ≤ j) : 2 * j ≤ 2 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero => norm_num
    | succ j =>
      have hij := ih (by omega)
      have h2 : (2 : ℕ) ≤ 2 ^ (j + 1) := by
        have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      calc 2 * (j + 2) = 2 * (j + 1) + 2 := by ring
        _ ≤ 2 ^ (j + 1) + 2 := by omega
        _ ≤ 2 ^ (j + 1) + 2 ^ (j + 1) := by omega
        _ = 2 ^ (j + 2) := by ring

/-- `∑_{j < N} exp(-2^j) ≤ 5/6`. -/
lemma sum_exp_neg_two_pow_le (N : ℕ) :
    ∑ j ∈ Finset.range N, exp (-((2 : ℝ) ^ j)) ≤ 5 / 6 := by
  cases N with
  | zero => norm_num
  | succ N =>
    rw [Finset.sum_range_succ']
    have hhalf : exp (-((2 : ℝ) ^ (0 : ℕ))) ≤ 1 / 2 := by
      have : exp (-(1 : ℝ)) ≤ 1 / 2 := by
        rw [exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by norm_num)]
        linarith [add_one_le_exp (1 : ℝ)]
      simpa using this
    let r : ℝ := exp (-2)
    have hr0 : 0 ≤ r := exp_nonneg _
    have hr1 : r < 1 := by
      dsimp [r]
      rw [← exp_zero]
      exact exp_lt_exp.mpr (by norm_num)
    have hterm : ∀ i, exp (-((2 : ℝ) ^ (i + 1))) ≤ r ^ (i + 1) := by
      intro i
      have hpow : 2 * (i + 1) ≤ 2 ^ (i + 1) := two_pow_ge_two_mul (i + 1) (by omega)
      have hpowR : (2 : ℝ) * ((i + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by exact_mod_cast hpow
      have hneg : -((2 : ℝ) ^ (i + 1)) ≤ -(2 * ((i + 1 : ℕ) : ℝ)) := by linarith
      have hexp : exp (-((2 : ℝ) ^ (i + 1))) ≤ exp (-(2 * ((i + 1 : ℕ) : ℝ))) :=
        exp_le_exp.mpr hneg
      have heq : exp (-(2 * ((i + 1 : ℕ) : ℝ))) = r ^ (i + 1) := by
        rw [show -(2 * ((i + 1 : ℕ) : ℝ)) = ((i + 1 : ℕ) : ℝ) * (-2) by ring, ← exp_nat_mul]
      exact hexp.trans_eq heq
    have hsumle : ∑ i ∈ Finset.range N, exp (-((2 : ℝ) ^ (i + 1))) ≤
        ∑ i ∈ Finset.range N, r ^ (i + 1) :=
      sum_le_sum fun i _ => hterm i
    have hden : 0 < 1 - r := by linarith
    have hgeom : ∑ i ∈ Finset.range N, r ^ i ≤ 1 / (1 - r) := by
      rw [geom_sum_eq hr1.ne]
      have hrN : 0 ≤ r ^ N := by positivity
      have hrewrite : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
        have : r - 1 = -(1 - r) := by ring
        rw [this, div_neg]
        ring
      rw [hrewrite, div_le_div_iff₀ hden hden]
      nlinarith
    have hshift : ∑ i ∈ Finset.range N, r ^ (i + 1) = r * ∑ i ∈ Finset.range N, r ^ i := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [pow_succ]
      ring
    have htail : ∑ i ∈ Finset.range N, r ^ (i + 1) ≤ r / (1 - r) := by
      rw [hshift]
      have hmul : r * ∑ i ∈ Finset.range N, r ^ i ≤ r * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hgeom hr0
      calc r * ∑ i ∈ Finset.range N, r ^ i ≤ r * (1 / (1 - r)) := hmul
        _ = r / (1 - r) := by ring
    have hthird : r / (1 - r) ≤ 1 / 3 := by
      have he2 : (4 : ℝ) ≤ exp 2 := by
        have h1 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
        calc (4 : ℝ) = 2 * 2 := by norm_num
          _ ≤ exp 1 * exp 1 := mul_le_mul h1 h1 (by norm_num) (exp_nonneg _)
          _ = exp 2 := by rw [← exp_add]; ring_nf
      have hr' : r = 1 / exp 2 := by
        dsimp [r]
        rw [exp_neg, inv_eq_one_div]
      have hden : 0 < 1 - 1 / exp 2 := by
        have hpos : (0 : ℝ) < exp 2 := exp_pos _
        have hone : (1 : ℝ) < exp 2 := by linarith
        rw [sub_pos, one_div, inv_lt_one_iff₀]
        exact Or.inr hone
      rw [hr', div_le_div_iff₀ hden (by norm_num)]
      field_simp
      nlinarith
    linarith

lemma clog_two_le (m : ℕ) : Nat.clog 2 m ≤ m := by
  rcases m with _ | m
  · simp [Nat.clog_of_right_le_one (by omega : (0 : ℕ) ≤ 1)]
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact (Nat.lt_pow_self (by norm_num : 1 < 2)).le

/-- `log₂` of a positive integer at most `2n` is at most `2 log n + 2`. -/
lemma clog_two_le_two_log {n m : ℕ} (hn : 1 < n) (hm : m ≤ 2 * n) (hm0 : 0 < m) :
    (Nat.clog 2 m : ℝ) ≤ 2 * log n + 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : 1 / 2 ≤ log 2 := by
    rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
    exact exp_half_le_two
  have hlog2pos : (0 : ℝ) < log 2 := by linarith
  rcases Nat.eq_zero_or_pos (Nat.clog 2 m) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero]
    have hlogn : 0 ≤ log n := log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    linarith
  · have hlt : 2 ^ (Nat.clog 2 m - 1) < m := by
      have hnot : ¬ m ≤ 2 ^ (Nat.clog 2 m - 1) := by
        intro hle
        have : Nat.clog 2 m ≤ Nat.clog 2 m - 1 :=
          (Nat.clog_le_iff_le_pow (by norm_num)).2 hle
        omega
      omega
    have hpow : (2 : ℝ) ^ (Nat.clog 2 m - 1) < (m : ℝ) := by exact_mod_cast hlt
    have hpred : ((Nat.clog 2 m - 1 : ℕ) : ℝ) * log 2 < log (m : ℝ) := by
      have hposp : (0 : ℝ) < (2 : ℝ) ^ (Nat.clog 2 m - 1) := by positivity
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
      have hloglt := log_lt_log hposp hpow
      rw [log_pow (2 : ℝ) (Nat.clog 2 m - 1)] at hloglt
      exact hloglt
    have hcast : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub hpos
    have hclog : (Nat.clog 2 m : ℝ) < log (m : ℝ) / log 2 + 1 := by
      rw [hcast] at hpred
      have : (Nat.clog 2 m : ℝ) - 1 < log (m : ℝ) / log 2 := (lt_div_iff₀ hlog2pos).2 hpred
      linarith
    have hlogm : log (m : ℝ) ≤ log 2 + log n := by
      have hm' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
      calc log (m : ℝ) ≤ log (2 * n) := log_le_log hmpos hm'
        _ = log 2 + log n := by rw [log_mul (by norm_num) hn0.ne']
    have hdiv : log n / log 2 ≤ 2 * log n := by
      have hlogn : 0 ≤ log n := log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      rw [div_le_iff₀ hlog2pos]
      nlinarith [hlog2, hlogn]
    calc (Nat.clog 2 m : ℝ) ≤ log (m : ℝ) / log 2 + 1 := le_of_lt hclog
      _ ≤ (log 2 + log n) / log 2 + 1 := by gcongr
      _ = log 2 / log 2 + log n / log 2 + 1 := by rw [add_div]
      _ = 1 + log n / log 2 + 1 := by rw [div_self hlog2pos.ne']
      _ = log n / log 2 + 2 := by ring
      _ ≤ 2 * log n + 2 := by linarith

end Undecided.Plurality
