import Mathlib

/-! # Real estimates for the BIPS phases (EPI-4)

Scalar inequalities used by Lemmas 2 to 4: the logarithm bound on `[0, 1/2]`, the comparisons
that turn one round of relative growth into a uniform multiplicative factor, and the end-phase
tail at `⌈8 log n / c⌉₊`.
-/

namespace Epidemics

open Real Set

/-- Derivative of `t - t²/3 - log(1 + t)`. -/
lemma hasDerivAt_logGap (t : ℝ) (ht : -1 < t) :
    HasDerivAt (fun s => s - s ^ 2 / 3 - log (1 + s)) (1 - 2 * t / 3 - (1 + t)⁻¹) t := by
  have hsq := (hasDerivAt_pow 2 t).div_const 3
  have hlog := ((hasDerivAt_id t).const_add (1 : ℝ)).log (by linarith : (1 + t) ≠ 0)
  convert! (((hasDerivAt_id t).sub hsq).sub hlog) using 1
  simp [id]

/-- `log(1 + x) ≤ x - x²/3` for `0 ≤ x ≤ 1/2`. The paper uses the weaker
`log(1 + x) ≤ x - x²/2 + x³/3`; the quadratic gap is enough for the constant `13`. -/
lemma log_one_add_le_sub_sq_div_three {x : ℝ} (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) :
    log (1 + x) ≤ x - x ^ 2 / 3 := by
  let f : ℝ → ℝ := fun t => t - t ^ 2 / 3 - log (1 + t)
  have hmono : MonotoneOn f (Icc 0 (1 / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
      (f' := fun t => 1 - 2 * t / 3 - (1 + t)⁻¹) ?_ ?_ ?_
    · change ContinuousOn (fun t => t - t ^ 2 / 3 - log (1 + t)) (Icc 0 (1 / 2))
      refine ContinuousOn.sub (ContinuousOn.sub continuousOn_id
          ((continuousOn_id.pow 2).div_const 3)) ?_
      refine ContinuousOn.log (continuousOn_const.add continuousOn_id) ?_
      intro t ht
      have : (0 : ℝ) < 1 + t := by linarith [ht.1]
      exact this.ne'
    · intro t ht
      rw [interior_Icc] at ht
      change HasDerivWithinAt (fun s => s - s ^ 2 / 3 - log (1 + s)) _ _ t
      exact (hasDerivAt_logGap t (by linarith [ht.1])).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hpos : 0 ≤ t * (1 - 2 * t) / (3 * (1 + t)) := by
        apply div_nonneg
        · nlinarith [ht.1, ht.2]
        · nlinarith [ht.1]
      have heq : 1 - 2 * t / 3 - (1 + t)⁻¹ = t * (1 - 2 * t) / (3 * (1 + t)) := by
        have hne : (1 + t) ≠ 0 := by linarith [ht.1]
        field_simp
        ring
      linarith
  have hxI : x ∈ Icc 0 (1 / 2) := ⟨hx0, hx12⟩
  have h0 : f 0 ≤ f x := hmono (by simp) hxI hx0
  simpa [f, log_one] using h0

/-- The exponent of Lemma 2. With `x = c/2` and `φ = log(1 + x)`, the threshold
`T ≥ 13 m/c + 24 C log n/c²` gives `m φ + T (φ - x) ≤ -C log n` for `C ≥ 0`. -/
lemma small_phase_exponent {m T c x φ : ℝ} {n : ℕ} {C : ℝ} (hm : 0 ≤ m) (hT0 : 0 ≤ T)
    (hc : 0 < c) (hc1 : c ≤ 1) (hx : x = c / 2) (hφ : φ = log (1 + x)) (hC : 0 ≤ C)
    (hn : 1 ≤ n) (hbound : 13 * m / c + 24 * C * log (n : ℝ) / c ^ 2 ≤ T) :
    φ * m + T * (φ - x) ≤ -C * log (n : ℝ) := by
  have hx0 : 0 < x := by
    rw [hx]
    exact div_pos hc (by norm_num)
  have hx12 : x ≤ 1 / 2 := by
    rw [hx]
    linarith
  have hφle : φ ≤ x - x ^ 2 / 3 := by
    rw [hφ]
    exact log_one_add_le_sub_sq_div_three hx0.le hx12
  have hφx : φ ≤ x := by linarith [sq_nonneg x]
  have hdiff : φ - x ≤ -(x ^ 2 / 3) := by linarith
  have hmx : m * φ ≤ m * x := mul_le_mul_of_nonneg_left hφx hm
  have hTx : T * (φ - x) ≤ T * (-(x ^ 2 / 3)) := mul_le_mul_of_nonneg_left hdiff hT0
  have hsum : m * φ + T * (φ - x) ≤ m * x - T * (x ^ 2 / 3) := by
    have : T * (-(x ^ 2 / 3)) = -(T * (x ^ 2 / 3)) := by ring
    linarith
  have hnonneg : 0 ≤ x ^ 2 / 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbound hnonneg
  have hcdef : c = 2 * x := by
    rw [hx]
    ring
  have hL : (13 * m / c + 24 * C * log (n : ℝ) / c ^ 2) * (x ^ 2 / 3) =
      13 * m * x / 6 + 2 * C * log (n : ℝ) := by
    rw [hcdef]
    have hxne : x ≠ 0 := hx0.ne'
    field_simp
    ring
  have hdrop : m * x - T * (x ^ 2 / 3) ≤
      m * x - (13 * m * x / 6 + 2 * C * log (n : ℝ)) := by
    linarith [hL]
  have hring : m * x - (13 * m * x / 6 + 2 * C * log (n : ℝ)) =
      -(7 / 6) * m * x - 2 * C * log (n : ℝ) := by ring
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
  have hfinal : -(7 / 6) * m * x - 2 * C * log (n : ℝ) ≤ -C * log (n : ℝ) := by
    nlinarith
  have hcomm : φ * m + T * (φ - x) = m * φ + T * (φ - x) := by ring
  linarith [hcomm]

/-- `log(1 + z) ≥ z/(1 + z)` for `z ≥ 0`, from `log t ≤ t - 1` at `t = 1/(1 + z)`. -/
lemma log_one_add_ge_div {z : ℝ} (hz : 0 ≤ z) : z / (1 + z) ≤ log (1 + z) := by
  have hpos : 0 < 1 + z := by linarith
  have hlog := log_le_sub_one_of_pos (inv_pos.2 hpos)
  rw [log_inv] at hlog
  have hsub : 1 - (1 + z)⁻¹ ≤ log (1 + z) := by linarith
  have heq : 1 - (1 + z)⁻¹ = z / (1 + z) := by
    field_simp
    ring
  linarith

/-- `(1 - c/20)(1 + c/10) ≥ 1 + c/23` for `0 ≤ c ≤ 1`. -/
lemma one_step_factor_23 {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    1 + c / 23 ≤ (1 - c / 20) * (1 + c / 10) := by
  have hdiff : (1 - c / 20) * (1 + c / 10) - (1 + c / 23) = c * (3 / 460 - c / 200) := by
    ring
  have hnn : 0 ≤ 3 / 460 - c / 200 := by nlinarith
  have hprod : 0 ≤ c * (3 / 460 - c / 200) := mul_nonneg hc0 hnn
  linarith

/-! ## End phase (`9n/10` to the whole graph)

Scalar bounds for Lemma 4: the size gap `n ≥ 32769`, the one-round stay factor, and the
contracted tail at `⌈8 log n / c⌉₊`.
-/

lemma dyadic_end_gap (k : ℕ) (hk1 : 1 ≤ k) (hk14 : k ≤ 14) :
    (9 / 10) * (2 : ℝ) ^ (k + 1) < 4000 * (k : ℝ) * 0.6931471803 := by
  interval_cases k <;> norm_num

/-- On `2 ≤ n ≤ 32768`, `(9/10) n < 4000 log n`, so the end-phase hypothesis forces `n` larger. -/
lemma nine_tenth_lt_log {n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 32768) :
    (9 / 10) * (n : ℝ) < 4000 * log (n : ℝ) := by
  have hne : n ≠ 0 := by omega
  have hspec := (Nat.log2_eq_iff hne).1 rfl
  have hk1 : 1 ≤ n.log2 := (Nat.le_log2 hne).2 (by simpa using hn2)
  have hk15 : n.log2 ≤ 15 := by
    by_contra hlt
    have h16 : 16 ≤ n.log2 := by omega
    have hpow : 2 ^ 16 ≤ n := (Nat.le_log2 hne).1 h16
    omega
  by_cases hk14 : n.log2 ≤ 14
  · have hdy := dyadic_end_gap n.log2 hk1 hk14
    have hlt : (n : ℝ) < (2 : ℝ) ^ (n.log2 + 1) := by exact_mod_cast hspec.2
    have hstep1 : (9 / 10) * (n : ℝ) < (9 / 10) * (2 : ℝ) ^ (n.log2 + 1) :=
      mul_lt_mul_of_pos_left hlt (by norm_num)
    have hstep3 : 4000 * (n.log2 : ℝ) * 0.6931471803 < 4000 * (n.log2 : ℝ) * log 2 := by
      have hpos : (0 : ℝ) < 4000 * (n.log2 : ℝ) := by positivity
      exact mul_lt_mul_of_pos_left log_two_gt_d9 hpos
    have hpowle : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by exact_mod_cast (Nat.log2_self_le hne)
    have hlogle : (n.log2 : ℝ) * log 2 ≤ log (n : ℝ) := by
      have hpos2 : (0 : ℝ) < (2 : ℝ) ^ n.log2 := by positivity
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have := (log_le_log_iff hpos2 hn0).2 hpowle
      rwa [log_pow (2 : ℝ) n.log2] at this
    have hstep4 : 4000 * ((n.log2 : ℝ) * log 2) ≤ 4000 * log (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlogle (by norm_num : (0 : ℝ) ≤ 4000)
    linarith
  · have hk : n.log2 = 15 := by omega
    have hpow : 2 ^ 15 ≤ n := by simpa [hk] using hspec.1
    have hnEq : n = 32768 := by omega
    have hlog : log (32768 : ℝ) = 15 * log 2 := by
      have hpowR : (32768 : ℝ) = (2 : ℝ) ^ 15 := by norm_num
      rw [hpowR, log_pow (2 : ℝ) 15]
      norm_cast
    have hnum : (9 / 10) * (32768 : ℝ) < 4000 * 15 * 0.6931471803 := by norm_num
    have hlt : 4000 * 15 * 0.6931471803 < 4000 * 15 * log 2 := by
      have hpos : (0 : ℝ) < 4000 * (15 : ℝ) := by norm_num
      simpa [mul_assoc] using mul_lt_mul_of_pos_left log_two_gt_d9 hpos
    have : (9 / 10) * (n : ℝ) < 4000 * log (n : ℝ) := by
      simpa [hnEq, hlog, mul_assoc] using hnum.trans hlt
    exact this

/-- The hypothesis `4000 log n/c² ≤ (9/10) n` forces `n ≥ 32769` when `2 ≤ n` and `0 < c ≤ 1`. -/
lemma end_n_ge {c : ℝ} {n : ℕ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hn : 2 ≤ n)
    (h : 4000 * log (n : ℝ) / c ^ 2 ≤ (9 / 10) * (n : ℝ)) : 32769 ≤ n := by
  have hlog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc2pos : 0 < c ^ 2 := by positivity
  have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1
  have hsmall : 4000 * log (n : ℝ) ≤ (9 / 10) * (n : ℝ) := by
    have hdiv : 4000 * log (n : ℝ) ≤ 4000 * log (n : ℝ) / c ^ 2 := by
      rw [le_div_iff₀ hc2pos]
      nlinarith
    linarith
  by_contra hlt
  have hnle : n ≤ 32768 := by omega
  exact (not_le_of_gt (nine_tenth_lt_log hn hnle)) hsmall

/-- `(1 - (8/125) c) (1 + c (1/10 - 1/n)) ≥ 1` for `0 ≤ c ≤ 1` and `n ≥ 32769`. -/
lemma stay_factor {c n : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hn : (32769 : ℝ) ≤ n) :
    1 ≤ (1 - (8 / 125) * c) * (1 + c * (1 / 10 - 1 / n)) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hnum : 0 ≤ n * (45 - 8 * c) + 80 * c - 1250 := by
    have h37 : (37 : ℝ) * 32769 - 1250 ≤ n * (45 - 8 * c) + 80 * c - 1250 := by nlinarith
    have hpos : (0 : ℝ) ≤ 37 * 32769 - 1250 := by norm_num
    linarith
  have hdiff : (1 - (8 / 125) * c) * (10 * n + c * (n - 10)) - 10 * n =
      c * (n * (45 - 8 * c) + 80 * c - 1250) / 125 := by
    field_simp
    ring
  have hnonneg : 0 ≤ (1 - (8 / 125) * c) * (10 * n + c * (n - 10)) - 10 * n := by
    rw [hdiff]
    positivity
  have hclear : 10 * n ≤ (1 - (8 / 125) * c) * (10 * n + c * (n - 10)) := by linarith
  have hpos10 : (0 : ℝ) < 10 * n := by positivity
  have hrewrite : 10 * n + c * (n - 10) = 10 * n * (1 + c * (1 / 10 - 1 / n)) := by
    field_simp
  rw [hrewrite] at hclear
  have h10 : (10 : ℝ) * n * 1 ≤ 10 * n * ((1 - (8 / 125) * c) * (1 + c * (1 / 10 - 1 / n))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hclear
  exact le_of_mul_le_mul_left h10 hpos10

/-- `√(16 log n / s) ≤ (8/125) c` once `s ≥ 4000 log n / c²`. -/
lemma eps_le_eight {c s logn : ℝ} (hc0 : 0 < c) (hlog : 0 < logn)
    (hs : 4000 * logn / c ^ 2 ≤ s) :
    sqrt (16 * logn / s) ≤ (8 / 125) * c := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hs0 : 0 < s := by
    have : 0 < 4000 * logn / c ^ 2 := div_pos (mul_pos (by norm_num) hlog) hc2
    linarith
  have hbase : 4000 * logn ≤ s * c ^ 2 := by
    rw [div_le_iff₀ hc2] at hs
    exact hs
  have hsq : 16 * logn / s ≤ c ^ 2 / 250 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  have hsqrt := sqrt_le_sqrt hsq
  have hdiv : sqrt (c ^ 2 / 250) = c / sqrt 250 := by
    rw [sqrt_div (sq_nonneg c) 250, sqrt_sq hc0.le]
  have h125 : (125 : ℝ) / 8 ≤ sqrt 250 := by
    refine (le_sqrt (by norm_num) (by norm_num)).2 ?_
    norm_num
  have hinv : 1 / sqrt 250 ≤ 8 / 125 := by
    rw [div_le_div_iff₀ (sqrt_pos.2 (by norm_num)) (by norm_num)]
    have : (125 : ℝ) ≤ 8 * sqrt 250 := by linarith
    nlinarith
  have hmul : c / sqrt 250 ≤ (8 / 125) * c := by
    rw [div_eq_mul_inv]
    have : c * (sqrt 250)⁻¹ ≤ c * (8 / 125) :=
      mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) hc0.le
    simpa [mul_comm] using this
  calc sqrt (16 * logn / s) ≤ sqrt (c ^ 2 / 250) := hsqrt
    _ = c / sqrt 250 := hdiv
    _ ≤ (8 / 125) * c := hmul

/-- `8 log n / c ≤ (3/25) n` under the end-phase size hypothesis. -/
lemma eight_log_le {c : ℝ} {n : ℕ} (hc0 : 0 < c) (hn : 2 ≤ n)
    (h : 4000 * log (n : ℝ) / c ^ 2 ≤ (9 / 10) * (n : ℝ)) :
    8 * log (n : ℝ) / c ≤ (3 / 25) * (n : ℝ) := by
  have hlog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogle : log (n : ℝ) ≤ (n : ℝ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have := log_le_sub_one_of_pos hn0
    linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hbase : 4000 * log (n : ℝ) ≤ (9 / 10) * (n : ℝ) * c ^ 2 := by
    rw [div_le_iff₀ hc2] at h
    simpa [mul_assoc] using h
  have hfrom : 4000 * log (n : ℝ) * (10 / 9) ≤ (n : ℝ) * c ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hbase (by positivity : (0 : ℝ) ≤ 10 / 9)
    have heq : (9 / 10) * (n : ℝ) * c ^ 2 * (10 / 9) = (n : ℝ) * c ^ 2 := by ring
    linarith
  have h64 : 64 * log (n : ℝ) ≤ (9 / 625) * (n : ℝ) * c ^ 2 := by
    calc 64 * log (n : ℝ) = 4000 * log (n : ℝ) * (10 / 9) * (9 / 625) := by ring
      _ ≤ (n : ℝ) * c ^ 2 * (9 / 625) :=
          mul_le_mul_of_nonneg_right hfrom (by positivity)
      _ = (9 / 625) * (n : ℝ) * c ^ 2 := by ring
  have hsqlog : 64 * log (n : ℝ) ^ 2 ≤ (9 / 625) * (n : ℝ) * c ^ 2 * log (n : ℝ) := by
    have := mul_le_mul_of_nonneg_right h64 hlog.le
    linarith
  have hdiv : 64 * log (n : ℝ) ^ 2 / c ^ 2 ≤ (9 / 625) * (n : ℝ) * log (n : ℝ) := by
    rw [div_le_iff₀ hc2]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsqlog
  have hlogn : (9 / 625) * (n : ℝ) * log (n : ℝ) ≤ (9 / 625) * (n : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hlogle (by positivity)
  have hpow : (8 * log (n : ℝ) / c) ^ 2 ≤ ((3 / 25) * (n : ℝ)) ^ 2 := by
    calc (8 * log (n : ℝ) / c) ^ 2 = 64 * log (n : ℝ) ^ 2 / c ^ 2 := by ring
      _ ≤ (9 / 625) * (n : ℝ) * log (n : ℝ) := hdiv
      _ ≤ (9 / 625) * (n : ℝ) ^ 2 := by simpa [pow_two, mul_assoc] using hlogn
      _ = ((3 / 25) * (n : ℝ)) ^ 2 := by ring
  exact (sq_le_sq₀ (by positivity) (by positivity)).1 hpow

/-- At `T = ⌈8 log n / c⌉₊`, the end-phase tail is at most `n^{-5}`. -/
lemma end_tail_small {c : ℝ} {n T : ℕ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hn : 2 ≤ n)
    (hgap : 4000 * log (n : ℝ) / c ^ 2 ≤ (9 / 10) * (n : ℝ))
    (hT : T = Nat.ceil (8 * log (n : ℝ) / c)) :
    (1 - (9 / 10) * c) ^ T * ((n : ℝ) / 10) + (T : ℝ) ^ 2 * (n : ℝ) ^ (-7 : ℝ) ≤
      1 / (n : ℝ) ^ 5 := by
  have hnbig : 32769 ≤ n := end_n_ge hc0 hc1 hn hgap
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  set θ : ℝ := 1 - (9 / 10) * c with hθdef
  have hθ0 : 0 < θ := by
    rw [hθdef]
    have hle : (9 / 10) * c ≤ (9 / 10) * 1 :=
      mul_le_mul_of_nonneg_left hc1 (by norm_num : (0 : ℝ) ≤ 9 / 10)
    linarith [show (9 : ℝ) / 10 * 1 < 1 by norm_num]
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    exact sub_le_self _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10) hc0.le)
  have hlogθ : log θ ≤ θ - 1 := log_le_sub_one_of_pos hθ0
  have hsub : θ - 1 = -((9 / 10) * c) := by ring
  have hpowθ : θ ^ T = exp (log θ * (T : ℝ)) := by
    rw [← rpow_natCast θ T, rpow_def_of_pos hθ0]
  have hTge : 8 * log (n : ℝ) / c ≤ (T : ℝ) := by
    rw [hT]
    exact Nat.le_ceil _
  have hprod : (36 / 5) * log (n : ℝ) ≤ (9 / 10) * c * (T : ℝ) := by
    have h8 : 8 * log (n : ℝ) ≤ c * (T : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hTge hc0.le
      have heq : c * (8 * log (n : ℝ) / c) = 8 * log (n : ℝ) := by field_simp
      linarith
    calc (36 / 5) * log (n : ℝ) = (9 / 10) * (8 * log (n : ℝ)) := by ring
      _ ≤ (9 / 10) * (c * (T : ℝ)) := mul_le_mul_of_nonneg_left h8 (by norm_num)
      _ = (9 / 10) * c * (T : ℝ) := by ring
  have hθexp : θ ^ T ≤ (n : ℝ) ^ (-(36 / 5) : ℝ) := by
    have hle1 : θ ^ T ≤ exp ((θ - 1) * (T : ℝ)) := by
      rw [hpowθ]
      exact (exp_le_exp).mpr (mul_le_mul_of_nonneg_right hlogθ (Nat.cast_nonneg T))
    have hle2 : exp ((θ - 1) * (T : ℝ)) ≤ exp (-((36 / 5) * log (n : ℝ))) := by
      apply (exp_le_exp).mpr
      rw [hsub]
      linarith
    have heq : exp (-((36 / 5) * log (n : ℝ))) = (n : ℝ) ^ (-(36 / 5) : ℝ) := by
      have : -((36 / 5) * log (n : ℝ)) = log (n : ℝ) * (-(36 / 5)) := by ring
      rw [this, ← rpow_def_of_pos hn0]
    exact hle1.trans (hle2.trans (le_of_eq heq))
  have hfirst : θ ^ T * ((n : ℝ) / 10) ≤ (n : ℝ) ^ (-(31 / 5) : ℝ) / 10 := by
    have hmul := mul_le_mul_of_nonneg_right hθexp
      (div_nonneg hn0.le (by norm_num : (0 : ℝ) ≤ 10))
    have hpow : (n : ℝ) ^ (-(36 / 5) : ℝ) * (n : ℝ) = (n : ℝ) ^ (-(31 / 5) : ℝ) := by
      have h := (rpow_add hn0 (-(36 / 5) : ℝ) (1 : ℝ)).symm
      have hexp : (-(36 / 5) : ℝ) + 1 = -(31 / 5) := by norm_num
      simpa [rpow_one, hexp] using h
    have hdiv : (n : ℝ) ^ (-(36 / 5) : ℝ) * ((n : ℝ) / 10) =
        (n : ℝ) ^ (-(31 / 5) : ℝ) / 10 := by
      have : (n : ℝ) ^ (-(36 / 5) : ℝ) * ((n : ℝ) / 10) =
          ((n : ℝ) ^ (-(36 / 5) : ℝ) * (n : ℝ)) / 10 := by ring
      rw [this, hpow]
    linarith
  have hTlt : (T : ℝ) < (4 / 25) * (n : ℝ) := by
    have hceil : (T : ℝ) < 8 * log (n : ℝ) / c + 1 := by
      rw [hT]
      exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hlog.le) hc0.le)
    have h8 := eight_log_le hc0 hn hgap
    have hone : (1 : ℝ) ≤ (1 / 25) * (n : ℝ) := by
      have hdiv : (1 : ℝ) ≤ (n : ℝ) / 25 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 25)]
        exact_mod_cast (show 25 ≤ n by omega)
      have heq : (n : ℝ) / 25 = (1 / 25) * (n : ℝ) := by ring
      linarith
    linarith
  have hsecond : (T : ℝ) ^ 2 * (n : ℝ) ^ (-7 : ℝ) ≤ (16 / 625) * (n : ℝ) ^ (-5 : ℝ) := by
    have hTle : (T : ℝ) ≤ (4 / 25) * (n : ℝ) := le_of_lt hTlt
    have hsq : (T : ℝ) ^ 2 ≤ ((4 / 25) * (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg T) hTle 2
    have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ (n : ℝ) ^ (-7 : ℝ))
    have hring : ((4 / 25) * (n : ℝ)) ^ 2 = (16 / 625) * (n : ℝ) ^ 2 := by ring
    have hpow : (n : ℝ) ^ 2 * (n : ℝ) ^ (-7 : ℝ) = (n : ℝ) ^ (-5 : ℝ) := by
      rw [← rpow_natCast (n : ℝ) 2, ← rpow_add hn0]
      norm_num
    calc (T : ℝ) ^ 2 * (n : ℝ) ^ (-7 : ℝ)
        ≤ ((4 / 25) * (n : ℝ)) ^ 2 * (n : ℝ) ^ (-7 : ℝ) := hmul
      _ = (16 / 625) * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-7 : ℝ)) := by rw [hring]; ring
      _ = (16 / 625) * (n : ℝ) ^ (-5 : ℝ) := by rw [hpow]
  have hsplit : (n : ℝ) ^ (-(31 / 5) : ℝ) =
      (n : ℝ) ^ (-5 : ℝ) * (n : ℝ) ^ (-(6 / 5) : ℝ) := by
    rw [← rpow_add hn0]
    norm_num
  have hsmall : (n : ℝ) ^ (-(6 / 5) : ℝ) ≤ 1 := by
    rw [rpow_neg (by exact_mod_cast Nat.zero_le n : (0 : ℝ) ≤ n)]
    refine inv_le_one_of_one_le₀ ?_
    exact one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hcoeff : (1 : ℝ) / 10 + 16 / 625 ≤ 1 := by norm_num
  have hneg5 : 0 ≤ (n : ℝ) ^ (-5 : ℝ) := by positivity
  have hbound : (n : ℝ) ^ (-(31 / 5) : ℝ) / 10 + (16 / 625) * (n : ℝ) ^ (-5 : ℝ) ≤
      (n : ℝ) ^ (-5 : ℝ) := by
    rw [hsplit]
    have hpart : (n : ℝ) ^ (-5 : ℝ) * (n : ℝ) ^ (-(6 / 5) : ℝ) ≤ (n : ℝ) ^ (-5 : ℝ) := by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hsmall hneg5
    have hdiv : (n : ℝ) ^ (-5 : ℝ) * (n : ℝ) ^ (-(6 / 5) : ℝ) / 10 ≤
        (1 / 10) * (n : ℝ) ^ (-5 : ℝ) := by
      rw [div_le_iff₀ (by norm_num), mul_assoc]
      have : (n : ℝ) ^ (-5 : ℝ) * (n : ℝ) ^ (-(6 / 5) : ℝ) ≤ (n : ℝ) ^ (-5 : ℝ) * 1 := by
        simpa [mul_one] using hpart
      linarith
    have hsum : (1 / 10) * (n : ℝ) ^ (-5 : ℝ) + (16 / 625) * (n : ℝ) ^ (-5 : ℝ) =
        (1 / 10 + 16 / 625) * (n : ℝ) ^ (-5 : ℝ) := by ring
    have hmul := mul_le_mul_of_nonneg_right hcoeff hneg5
    linarith
  have hfive : (n : ℝ) ^ (-5 : ℝ) = 1 / (n : ℝ) ^ 5 := by
    have hsign : (-5 : ℝ) = -((5 : ℕ) : ℝ) := by norm_num
    rw [hsign, rpow_neg (by exact_mod_cast Nat.zero_le n : (0 : ℝ) ≤ n), rpow_natCast]
    exact (one_div ((n : ℝ) ^ 5)).symm
  linarith

/-! ## Phase lengths for the infection time

`128 √(log n / n) ≤ 1` already forces `n ≥ 16385`, which is the room used to turn
`4000 log n / y² ≤ n/4` into the concrete thresholds of Lemmas 2 to 4.
-/

/-- For `1 ≤ k ≤ 14`, `2^{k+1} < 16384 k * 0.6931471803`. -/
lemma dyadic_gap_card (k : ℕ) (hk1 : 1 ≤ k) (hk14 : k ≤ 14) :
    (2 : ℝ) ^ (k + 1) < 16384 * (k : ℝ) * 0.6931471803 := by
  interval_cases k <;> norm_num

/-- `log n ≤ n/16384` and `n ≥ 2` force `n ≥ 16385`. -/
lemma gap_card_ge {n : ℕ} (hn : 2 ≤ n) (h : log (n : ℝ) ≤ (n : ℝ) / 16384) : 16385 ≤ n := by
  by_contra hlt
  have hnle : n ≤ 16384 := by omega
  have hne : n ≠ 0 := by omega
  have hspec := (Nat.log2_eq_iff hne).1 rfl
  have hk1 : 1 ≤ n.log2 := (Nat.le_log2 hne).2 (by simpa using hn)
  have hk14 : n.log2 ≤ 14 := by
    by_contra hgt
    have h15 : 15 ≤ n.log2 := by omega
    have hpow : 2 ^ 15 ≤ n := (Nat.le_log2 hne).1 h15
    omega
  have hdy := dyadic_gap_card n.log2 hk1 hk14
  have hltn : (n : ℝ) < (2 : ℝ) ^ (n.log2 + 1) := by exact_mod_cast hspec.2
  have hstep1 : (n : ℝ) < 16384 * (n.log2 : ℝ) * 0.6931471803 := hltn.trans hdy
  have hstep3 : 16384 * (n.log2 : ℝ) * 0.6931471803 < 16384 * (n.log2 : ℝ) * log 2 := by
    have hpos : (0 : ℝ) < 16384 * (n.log2 : ℝ) := by positivity
    exact mul_lt_mul_of_pos_left log_two_gt_d9 hpos
  have hpowle : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by exact_mod_cast (Nat.log2_self_le hne)
  have hlogle : (n.log2 : ℝ) * log 2 ≤ log (n : ℝ) := by
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ n.log2 := by positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have := (log_le_log_iff hpos2 hn0).2 hpowle
    rwa [log_pow (2 : ℝ) n.log2] at this
  have hstep4 : 16384 * ((n.log2 : ℝ) * log 2) ≤ 16384 * log (n : ℝ) :=
    mul_le_mul_of_nonneg_left hlogle (by norm_num : (0 : ℝ) ≤ 16384)
  have hbig : (n : ℝ) < 16384 * log (n : ℝ) := by linarith
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16384)] at h
  linarith

end Epidemics
