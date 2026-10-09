import Epidemics.Revisited.Protocols
import Epidemics.Revisited.LowerGeneric

/-! # One-round lower bounds (EPI-8, Lemmas 39 and 49)

Chebyshev on the lower tail of the number of uninformed nodes, the bound
`(1 - 1/n)^k ≥ e^{-1}` for `k + 1 ≤ n`, and the one-round lemmas for push, pull and push–pull.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

variable {n : ℕ}

/-- Lower tail of the deficit, the mirror of `prob_deficit_gt_cheb`. If `μ ≤ E[n - |T|]` and
`z < μ`, and distinct uninformed nodes have covariance at most `c₀ ≥ 0`, then
`P[n - |T| < z] ≤ (u + c₀ u²) / (μ - z)²` with `u = n - |S|`. -/
lemma prob_deficit_lt_cheb (P : RumorProcess n) (S : Finset (Fin n)) {c₀ μ z : ℝ}
    (hc₀ : 0 ≤ c₀) (hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c₀)
    (hμ : μ ≤ (P.K S).expect (fun T => (n : ℝ) - T.card)) (hz : z < μ) :
    (P.K S).prob (fun T => (n : ℝ) - T.card < z) ≤
      (((n : ℝ) - S.card) + c₀ * ((n : ℝ) - S.card) ^ 2) / (μ - z) ^ 2 := by
  set D := P.K S
  set X : Finset (Fin n) → ℝ := fun T => (T.card : ℝ)
  have hEX : D.expect (fun T => (n : ℝ) - T.card) = (n : ℝ) - D.expect X := by
    rw [Distribution.expect_sub, Distribution.expect_const]
  have hlam : 0 < μ - z := by linarith
  have hEXle : D.expect X ≤ (n : ℝ) - μ := by linarith
  have hsub : D.prob (fun T => (n : ℝ) - T.card < z) ≤
      D.prob (fun T => μ - z ≤ |X T - D.expect X|) := by
    refine prob_mono D (fun T hT => ?_)
    have hlow : μ - z < X T - D.expect X := by
      have hXT : (n : ℝ) - z < X T := by simp only [X]; linarith
      linarith
    exact le_trans (le_of_lt hlow) (le_abs_self _)
  have hcheb := chebyshev D X hlam
  have hvar := variance_card_le_proof P S hc₀ hcov
  have hinc : D.expect X - S.card ≤ (n : ℝ) - S.card := by
    have hle : D.expect X ≤ D.expect (fun _ => (n : ℝ)) := D.expect_mono fun T => card_le_n T
    rw [Distribution.expect_const] at hle
    linarith
  have hvar' : D.expect (fun T => (X T - D.expect X) ^ 2) ≤
      ((n : ℝ) - S.card) + c₀ * ((n : ℝ) - S.card) ^ 2 := by
    linarith [hvar, hinc]
  calc D.prob (fun T => (n : ℝ) - T.card < z)
      ≤ D.prob (fun T => μ - z ≤ |X T - D.expect X|) := hsub
    _ ≤ D.expect (fun T => (X T - D.expect X) ^ 2) / (μ - z) ^ 2 := hcheb
    _ ≤ (((n : ℝ) - S.card) + c₀ * ((n : ℝ) - S.card) ^ 2) / (μ - z) ^ 2 :=
        div_le_div_of_nonneg_right hvar' (sq_nonneg _)

/-- `(1 - 1/n)^k ≥ e^{-1}` whenever `k + 1 ≤ n` (Corollary 17, for `1 ≤ u` uninformed nodes,
so the exponent `n - u` is at most `n - 1`). -/
lemma one_sub_inv_pow_ge_exp_neg {k : ℕ} (hk : k + 1 ≤ n) :
    Real.exp (-1) ≤ (1 - 1 / (n : ℝ)) ^ k := by
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hbase0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn0r]
    exact_mod_cast (show 1 ≤ n by omega)
  have hbase1 : 1 - 1 / (n : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (n : ℝ) := div_nonneg zero_le_one hn0r.le
    linarith
  have hk' : k ≤ n - 1 := by omega
  have hmono : (1 - 1 / (n : ℝ)) ^ (n - 1) ≤ (1 - 1 / (n : ℝ)) ^ k :=
    pow_le_pow_of_le_one hbase0 hbase1 hk'
  suffices Real.exp (-1) ≤ (1 - 1 / (n : ℝ)) ^ (n - 1) from le_trans this hmono
  by_cases hn1 : n = 1
  · simp [hn1]
  · let m : ℕ := n - 1
    have hmn : m + 1 = n := by omega
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hpow_le : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
      have h1 : 1 + 1 / (m : ℝ) ≤ Real.exp (1 / (m : ℝ)) := by
        linarith [Real.add_one_le_exp (1 / (m : ℝ))]
      calc (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp (1 / (m : ℝ)) ^ m :=
            pow_le_pow_left₀ (by positivity) h1 m
        _ = Real.exp ((m : ℕ) * (1 / (m : ℝ))) := by rw [← Real.exp_nat_mul]
        _ = Real.exp 1 := by
            have hcast : ((m : ℕ) : ℝ) = (m : ℝ) := rfl
            rw [hcast, mul_one_div, div_self hm0]
    have hpos : (0 : ℝ) < (1 + 1 / (m : ℝ)) ^ m := by positivity
    have hinv : Real.exp (-1) ≤ ((1 + 1 / (m : ℝ)) ^ m)⁻¹ := by
      rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hpos]
      exact hpow_le
    have hid : (1 - 1 / (n : ℝ)) ^ m = ((1 + 1 / (m : ℝ)) ^ m)⁻¹ := by
      have hleft : (1 : ℝ) - 1 / n = (m : ℝ) / n := by
        have hncast : (n : ℝ) = (m : ℝ) + 1 := by
          rw [← hmn]
          norm_cast
        rw [hncast]
        field_simp
        ring
      have hright : (1 : ℝ) + 1 / m = (n : ℝ) / m := by
        have hncast : (n : ℝ) = (m : ℝ) + 1 := by
          rw [← hmn]
          norm_cast
        rw [hncast]
        field_simp
      calc (1 - 1 / (n : ℝ)) ^ m
          = ((m : ℝ) / n) ^ m := by rw [hleft]
        _ = (m : ℝ) ^ m / (n : ℝ) ^ m := div_pow _ _ _
        _ = (((n : ℝ) / m) ^ m)⁻¹ := by rw [div_pow, inv_div]
        _ = ((1 + 1 / (m : ℝ)) ^ m)⁻¹ := by rw [← hright]
    have hm_eq : n - 1 = m := rfl
    rw [hm_eq, hid]
    exact hinv

/-- `v ≥ 4` gives `v^{1/4} ≥ √2 ≥ e / 2`. -/
lemma exp_le_two_mul_fourth {v : ℝ} (hv : 4 ≤ v) :
    Real.exp 1 ≤ 2 * v ^ (1 / 4 : ℝ) := by
  have h4 : (4 : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt 2 := by
    have htwo : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [htwo, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_eq_rpow]
    norm_num
  have ha : Real.sqrt 2 ≤ v ^ (1 / 4 : ℝ) := by
    rw [← h4]
    exact Real.rpow_le_rpow (by norm_num) hv (by norm_num)
  have ha2 : 2 ≤ (v ^ (1 / 4 : ℝ)) ^ 2 := by
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) ha
    simpa [sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hsq
  have he : Real.exp 1 < (2.8 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he2 : Real.exp 1 * Real.exp 1 < (2.8 : ℝ) * 2.8 :=
    mul_lt_mul he he.le (Real.exp_pos _) (by norm_num)
  have h28 : (2.8 : ℝ) * 2.8 < 8 := by norm_num
  have hcmp : Real.exp 1 ^ 2 ≤ (2 * v ^ (1 / 4 : ℝ)) ^ 2 := by
    nlinarith [ha2, he2, h28]
  exact le_of_sq_le_sq hcmp (by positivity)

/-- With `a = v^{1/4}` and `w ≥ 0`, `(v + w) / (w/e + v^{3/4})² ≤ v^{-1/2}`. -/
lemma push_level_algebra {v w : ℝ} (hv : 4 ≤ v) (hw : 0 ≤ w) :
    (v + w) / (w / Real.exp 1 + v ^ (3 / 4 : ℝ)) ^ 2 ≤ v ^ (-(1 / 2 : ℝ)) := by
  have hv0 : (0 : ℝ) ≤ v := by linarith
  set a : ℝ := v ^ (1 / 4 : ℝ)
  have ha0 : 0 ≤ a := Real.rpow_nonneg hv0 _
  have ha4 : a ^ 4 = v := by
    unfold a
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv0]
    norm_num [Real.rpow_one]
  have ha3 : a ^ 3 = v ^ (3 / 4 : ℝ) := by
    unfold a
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv0]
    norm_num
  have ha2 : a ^ 2 = v ^ (1 / 2 : ℝ) := by
    unfold a
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv0]
    norm_num
  have hae : Real.exp 1 ≤ 2 * a := by
    simpa [a] using exp_le_two_mul_fourth hv
  have hden : 0 < w / Real.exp 1 + a ^ 3 := by
    have hpos : 0 < a ^ 3 := by
      have : 0 < a := by
        have h4 : (0 : ℝ) < (4 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
        exact lt_of_lt_of_le h4 (by simpa [a] using Real.rpow_le_rpow (by norm_num) hv (by norm_num))
      positivity
    have hnn : 0 ≤ w / Real.exp 1 := div_nonneg hw (Real.exp_pos _).le
    linarith
  have hclear : (w + Real.exp 1 * a ^ 3) ^ 2 ≥ Real.exp 1 ^ 2 * (v + w) * a ^ 2 := by
    have hdiff : (w + Real.exp 1 * a ^ 3) ^ 2 - Real.exp 1 ^ 2 * (a ^ 4 + w) * a ^ 2 =
        w ^ 2 + w * a ^ 2 * Real.exp 1 * (2 * a - Real.exp 1) := by ring
    have hnn : 0 ≤ w ^ 2 + w * a ^ 2 * Real.exp 1 * (2 * a - Real.exp 1) := by
      have h1 : 0 ≤ w ^ 2 := sq_nonneg w
      have hgap : 0 ≤ 2 * a - Real.exp 1 := by linarith
      have he : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
      have h2 : 0 ≤ w * a ^ 2 * Real.exp 1 * (2 * a - Real.exp 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg hw (sq_nonneg a)) he) hgap
      linarith [h1, h2]
    rw [ha4] at hdiff
    linarith
  have hsq : (v + w) * a ^ 2 ≤ (w / Real.exp 1 + a ^ 3) ^ 2 := by
    have he2 : 0 < Real.exp 1 ^ 2 := by positivity
    have hrew : (w / Real.exp 1 + a ^ 3) ^ 2 =
        (w + Real.exp 1 * a ^ 3) ^ 2 / Real.exp 1 ^ 2 := by
      field_simp
    rw [hrew, le_div_iff₀ he2]
    linarith
  have hneg : v ^ (-(1 / 2 : ℝ)) = (a ^ 2)⁻¹ := by
    rw [Real.rpow_neg hv0, ha2]
  rw [hneg, ← ha3]
  have ha2pos : 0 < a ^ 2 := by
    have : 0 < a := by
      have h4 : (0 : ℝ) < (4 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      exact lt_of_lt_of_le h4 (by
        simpa [a] using Real.rpow_le_rpow (by norm_num) hv (by norm_num))
    positivity
  rw [div_le_iff₀ (sq_pos_of_pos hden), inv_mul_eq_div, le_div_iff₀ ha2pos]
  exact hsq

/-- One round of push (Lemma 39): `P[u' < v/e - v^{3/4}] ≤ v^{-1/2}` for `4 ≤ v ≤ u`. -/
theorem push_round_lower_proof (S : Finset (Fin n)) {v : ℝ} (hv : 4 ≤ v)
    (hvu : v ≤ (n : ℝ) - S.card) :
    ((push n).K S).prob (fun T => (n : ℝ) - T.card < v / Real.exp 1 - v ^ (3 / 4 : ℝ)) ≤
      v ^ (-(1 / 2 : ℝ)) := by
  set u : ℝ := (n : ℝ) - S.card
  have hu : v ≤ u := hvu
  have hcard : S.card + 1 ≤ n := by
    have hlt : (S.card : ℝ) + 1 ≤ n := by linarith
    exact_mod_cast hlt
  have hstay := one_sub_inv_pow_ge_exp_neg (k := S.card) hcard
  have hE : ((push n).K S).expect (fun T => (n : ℝ) - T.card) =
      u * (1 - 1 / (n : ℝ)) ^ S.card := by
    rw [expect_deficit]
    have heq : ∀ x ∈ (univ : Finset (Fin n)) \ S,
        1 - (push n).informProb S x = (1 - 1 / (n : ℝ)) ^ S.card := by
      intro x hx
      rw [push_informProb (mem_sdiff.mp hx).2]
      ring
    rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, card_compl_cast]
  have hμ : u / Real.exp 1 ≤ ((push n).K S).expect (fun T => (n : ℝ) - T.card) := by
    rw [hE]
    have hu0 : 0 ≤ u := by linarith
    have hmul := mul_le_mul_of_nonneg_left hstay hu0
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Real.exp_neg] using hmul
  set z : ℝ := v / Real.exp 1 - v ^ (3 / 4 : ℝ)
  have hz : z < u / Real.exp 1 := by
    have hpos : 0 < v ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < v) _
    have hge : v / Real.exp 1 ≤ u / Real.exp 1 :=
      div_le_div_of_nonneg_right hu (Real.exp_pos _).le
    linarith
  have hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y → (push n).cov S x y ≤ 0 :=
    fun x hx y hy hxy => push_cov_nonpos hx hy hxy
  have hcheb := prob_deficit_lt_cheb (push n) S (c₀ := 0) le_rfl hcov hμ hz
  have hnum : ((n : ℝ) - S.card) + 0 * ((n : ℝ) - S.card) ^ 2 = u := by
    simp [u]
  rw [hnum] at hcheb
  have halg := push_level_algebra (v := v) (w := u - v) hv (by linarith)
  have hden : u / Real.exp 1 - z = (u - v) / Real.exp 1 + v ^ (3 / 4 : ℝ) := by
    unfold z
    ring
  have hbound : u / (u / Real.exp 1 - z) ^ 2 ≤ v ^ (-(1 / 2 : ℝ)) := by
    rw [hden]
    simpa [add_comm] using halg
  exact le_trans hcheb hbound

/-- The event `n - |T| < 0` is impossible. -/
lemma prob_deficit_neg_eq_zero (P : RumorProcess n) (S : Finset (Fin n)) :
    (P.K S).prob (fun T => (n : ℝ) - T.card < 0) = 0 := by
  have hne : ∀ T : Finset (Fin n), ¬ ((n : ℝ) - T.card < 0) := by
    intro T
    have := card_le_n T
    linarith
  rw [prob_indicator_eq (P.K S) _ (fun _ => (0 : ℝ)) (fun _ _ => rfl)
    (fun T h => (hne T h).elim)]
  simp [Distribution.expect_const]

/-- One round of pull (Lemma 49, `a = 1`): `P[u' < u²/(2n)] ≤ 4 n² / u³`. -/
theorem pull_round_lower_proof (S : Finset (Fin n)) :
    ((pull n).K S).prob (fun T => (n : ℝ) - T.card < ((n : ℝ) - S.card) ^ 2 / (2 * n)) ≤
      4 * (n : ℝ) ^ 2 / ((n : ℝ) - S.card) ^ 3 := by
  set u : ℝ := (n : ℝ) - S.card
  have hu0 : 0 ≤ u := by
    have := card_le_n S
    linarith
  rcases hu0.eq_or_lt with hu | hu
  · have htarget : u ^ 2 / (2 * (n : ℝ)) = 0 := by simp [← hu]
    have hprob : ((pull n).K S).prob (fun T => (n : ℝ) - T.card < u ^ 2 / (2 * n)) =
        ((pull n).K S).prob (fun T => (n : ℝ) - T.card < 0) := by
      simp [htarget]
    rw [hprob, prob_deficit_neg_eq_zero]
    simp [← hu]
  · have hn0 : (0 : ℝ) < n := by
      have := card_le_n S
      linarith
    have hE : ((pull n).K S).expect (fun T => (n : ℝ) - T.card) = u ^ 2 / n := by
      rw [expect_deficit]
      have heq : ∀ x ∈ (univ : Finset (Fin n)) \ S,
          1 - (pull n).informProb S x = u / n := by
        intro x hx
        rw [pull_informProb (mem_sdiff.mp hx).2]
        have : (1 : ℝ) - S.card / n = u / n := by
          field_simp
          ring
        exact this
      rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, card_compl_cast]
      field_simp
      ring
    set μ : ℝ := u ^ 2 / n
    set z : ℝ := u ^ 2 / (2 * n)
    have hz : z < μ := by
      unfold z μ
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      exact mul_lt_mul_of_pos_left (by linarith : (n : ℝ) < 2 * n) (by positivity : (0 : ℝ) < u ^ 2)
    have hμ : μ ≤ ((pull n).K S).expect (fun T => (n : ℝ) - T.card) := by
      rw [hE]
    have hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y → (pull n).cov S x y ≤ 0 :=
      fun x hx y hy hxy => (pull_cov_eq_zero hx hy hxy).le
    have hcheb := prob_deficit_lt_cheb (pull n) S (c₀ := 0) le_rfl hcov hμ hz
    have hnum : u + 0 * u ^ 2 = u := by ring
    rw [hnum] at hcheb
    have hgap : μ - z = u ^ 2 / (2 * n) := by
      unfold μ z
      field_simp
      ring
    have halg : u / (μ - z) ^ 2 = 4 * n ^ 2 / u ^ 3 := by
      rw [hgap]
      field_simp
      ring
    have hle : u / (μ - z) ^ 2 ≤ 4 * n ^ 2 / u ^ 3 := by
      rw [halg]
    exact le_trans hcheb hle

/-- One round of push–pull (Lemma 49, `a = 1/e`): `P[u' < u²/(2 e n)] ≤ 4 e² n² / u³`. -/
theorem pushPull_round_lower_proof (S : Finset (Fin n)) :
    ((pushPull n).K S).prob (fun T => (n : ℝ) - T.card <
        ((n : ℝ) - S.card) ^ 2 / (2 * Real.exp 1 * n)) ≤
      4 * Real.exp 1 ^ 2 * (n : ℝ) ^ 2 / ((n : ℝ) - S.card) ^ 3 := by
  set u : ℝ := (n : ℝ) - S.card
  have hu0 : 0 ≤ u := by
    have := card_le_n S
    linarith
  rcases hu0.eq_or_lt with hu | hu
  · have htarget : u ^ 2 / (2 * Real.exp 1 * (n : ℝ)) = 0 := by simp [← hu]
    have hprob : ((pushPull n).K S).prob
        (fun T => (n : ℝ) - T.card < u ^ 2 / (2 * Real.exp 1 * n)) =
        ((pushPull n).K S).prob (fun T => (n : ℝ) - T.card < 0) := by
      simp [htarget]
    rw [hprob, prob_deficit_neg_eq_zero]
    simp [← hu]
  · have hn0 : (0 : ℝ) < n := by
      have := card_le_n S
      linarith
    have hcard : S.card + 1 ≤ n := by
      have : S.card < n := by
        have : (S.card : ℝ) < n := by linarith
        exact_mod_cast this
      exact Nat.succ_le_of_lt this
    have hstay := one_sub_inv_pow_ge_exp_neg (k := S.card) hcard
    have hE : ((pushPull n).K S).expect (fun T => (n : ℝ) - T.card) =
        u * ((1 - 1 / (n : ℝ)) ^ S.card * (u / n)) := by
      rw [expect_deficit]
      have heq : ∀ x ∈ (univ : Finset (Fin n)) \ S,
          1 - (pushPull n).informProb S x =
            (1 - 1 / (n : ℝ)) ^ S.card * (u / n) := by
        intro x hx
        rw [pushPull_informProb (mem_sdiff.mp hx).2]
        have : (1 : ℝ) - S.card / n = u / n := by
          field_simp
          ring
        rw [this]
        ring
      rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, card_compl_cast]
    have hμ : u ^ 2 / (Real.exp 1 * n) ≤
        ((pushPull n).K S).expect (fun T => (n : ℝ) - T.card) := by
      rw [hE]
      have hu0' : 0 ≤ u := hu.le
      have hfrac : 0 ≤ u / n := div_nonneg hu0' hn0.le
      have hmul := mul_le_mul_of_nonneg_right hstay hfrac
      have hstep : u * (Real.exp (-1) * (u / n)) ≤
          u * ((1 - 1 / (n : ℝ)) ^ S.card * (u / n)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hmul hu0'
      have hid : u * (Real.exp (-1) * (u / n)) = u ^ 2 / (Real.exp 1 * n) := by
        rw [Real.exp_neg]
        field_simp
      linarith
    set μ : ℝ := u ^ 2 / (Real.exp 1 * n)
    set z : ℝ := u ^ 2 / (2 * Real.exp 1 * n)
    have hz : z < μ := by
      unfold z μ
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      exact mul_lt_mul_of_pos_left (by
        calc Real.exp 1 * (n : ℝ) < Real.exp 1 * (2 * n) :=
              mul_lt_mul_of_pos_left (by linarith : (n : ℝ) < 2 * n) (Real.exp_pos _)
          _ = 2 * Real.exp 1 * n := by ring) (by positivity : (0 : ℝ) < u ^ 2)
    have hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y → (pushPull n).cov S x y ≤ 0 :=
      fun x hx y hy hxy => pushPull_cov_nonpos hx hy hxy
    have hcheb := prob_deficit_lt_cheb (pushPull n) S (c₀ := 0) le_rfl hcov hμ hz
    have hnum : u + 0 * u ^ 2 = u := by ring
    rw [hnum] at hcheb
    have hgap : μ - z = u ^ 2 / (2 * Real.exp 1 * n) := by
      unfold μ z
      field_simp
      ring
    have halg : u / (μ - z) ^ 2 = 4 * Real.exp 1 ^ 2 * n ^ 2 / u ^ 3 := by
      rw [hgap]
      field_simp
      ring
    exact le_trans hcheb (by rw [halg])

end Epidemics.Revisited
