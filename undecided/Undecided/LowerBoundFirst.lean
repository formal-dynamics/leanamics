import Undecided.LowerBoundRound

/-! # The `Ω(md(c))` lower bound (UND-3): the first round (SODA 2015, Lemma 3)

[BCNPS15, Lemma 3] ("Rise of the undecided"): let `k = o(√(n / log n))`. From any initial
configuration `c̄` (without undecided nodes), after the first round, w.h.p.,
`n / (2R(c̄)²) ≤ C_m' ≤ 2n / R(c̄)²` and `n (1 - 2/Λ(c̄)) ≤ Q' ≤ n (1 - 1/(2Λ(c̄)))`, where `m` is
the plurality colour.

Here the upper bound is stated for **every** colour (`maxCount`), as needed for the lower bound
(no colour, not only the initial plurality, may grow fast); the expected size of colour `i`
after the first round is `c̄ᵢ² / n ≤ c̄_m² / n = n / R(c̄)²`.
"W.h.p." and `o(·)` are made explicit as everywhere in `undecided/`: one constant `C` with
`log n ≥ C`, `C k ≤ (n / log n)^{1/2}` and failure probability at most `C / n`. The probability
of missing a set `S` after `T` rounds from `x` is `miss S T x` (`PluralityStages.lean`).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- **Lemma 3 of [BCNPS15]** (first round, "rise of the undecided"). There is `C > 0` such
that, for every `n` with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/2}`, every
configuration `x` without undecided nodes and every plurality colour `m` of `x`, after one
round, with probability at least `1 - C / n`: the colour `m` has at least `n / (2R(x)²)` nodes,
**every** colour has at most `2n / R(x)²` nodes, and the number of undecided nodes lies in
`[n (1 - 2/Λ(x)), n (1 - 1/(2Λ(x)))]`. -/
theorem first_round : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 2) →
    ∀ (x : Config n k) (m : Fin k), count x none = 0 →
      (∀ i, count x (some i) ≤ count x (some m)) →
      miss {y | (n : ℝ) / (2 * ratioR x ^ 2) ≤ cnt y m ∧
          (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 ∧
          n * (1 - 2 / ratioLam x) ≤ und y ∧ und y ≤ n * (1 - 1 / (2 * ratioLam x))} 1 x
        ≤ C / n := by
  refine ⟨100, by norm_num, ?_⟩
  intro n hL k hk x m hq hplur
  have hlog1 : (1 : ℝ) ≤ log n := by linarith
  have hlogpos : 0 < log n := by linarith
  have hn1 : 1 < n := one_lt_n_of_log (by norm_num : (0 : ℝ) < 100) hL
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hk_le : k ≤ n :=
    k_le_n_of_range (by norm_num : (1 : ℝ) ≤ 100) (by norm_num : (1 : ℝ) / 2 ≤ 1) hlog1 hk
  have hkpos : 0 < k := m.pos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hpoly : (100 * (k : ℝ)) ^ 2 * log n ≤ n :=
    pow_of_rpow (by norm_num : 0 < 2) (by positivity) hlogpos (Nat.cast_nonneg n) hk
  have hpoly' : (10000 : ℝ) * (k : ℝ) ^ 2 * log n ≤ n := by
    have heq : (100 * (k : ℝ)) ^ 2 = (10000 : ℝ) * (k : ℝ) ^ 2 := by ring
    rwa [heq] at hpoly
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have h18 : (18 : ℝ) * log n ≤ n := by
    have hlog0 : 0 ≤ log n := hlogpos.le
    have hcoe : (18 : ℝ) ≤ 10000 * (k : ℝ) ^ 2 := by
      have : (18 : ℝ) ≤ 10000 := by norm_num
      exact le_trans this (le_mul_of_one_le_right (by norm_num) hk2)
    have : (18 : ℝ) * log n ≤ 10000 * (k : ℝ) ^ 2 * log n :=
      mul_le_mul_of_nonneg_right hcoe hlog0
    linarith
  have h6 : 6 * (3 * log n) ≤ n := by
    have : 6 * (3 * log n) = 18 * log n := by ring
    linarith
  have hund0 : und x = 0 := by
    unfold und
    exact_mod_cast hq
  have hcnt : ∀ i, cnt x i ≤ cnt x m := by
    intro i
    unfold cnt
    exact_mod_cast hplur i
  have hdiv : (n : ℝ) ≤ (k : ℝ) * cnt x m := n_div_le_cnt x m hund0 hcnt
  have hcm : n / (k : ℝ) ≤ cnt x m := by
    rw [div_le_iff₀ (by exact_mod_cast hkpos : (0 : ℝ) < k), mul_comm]
    exact hdiv
  have hμeq : mu x m = cnt x m ^ 2 / n := mu_of_und_zero x m hund0 hnR.ne'
  have hμge : n / (k : ℝ) ^ 2 ≤ mu x m := by
    rw [hμeq]
    have hsq : (n / (k : ℝ)) ^ 2 ≤ cnt x m ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcm 2
    have hdivμ : (n / (k : ℝ)) ^ 2 / n ≤ cnt x m ^ 2 / n :=
      div_le_div_of_nonneg_right hsq hnR.le
    have heq : (n / (k : ℝ)) ^ 2 / n = n / (k : ℝ) ^ 2 := by field_simp
    linarith
  have h14 : 14 * (3 * log n) ≤ mu x m := by
    have h42 : (42 : ℝ) * log n ≤ n / (k : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
      have hlog0 : 0 ≤ log n := hlogpos.le
      have hk2' : 0 ≤ (k : ℝ) ^ 2 := by positivity
      have hcoe : (42 : ℝ) * (k : ℝ) ^ 2 ≤ 10000 * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num) hk2'
      have : (42 : ℝ) * (k : ℝ) ^ 2 * log n ≤ 10000 * (k : ℝ) ^ 2 * log n :=
        mul_le_mul_of_nonneg_right hcoe hlog0
      have heq : 14 * (3 * log n) * (k : ℝ) ^ 2 = 42 * (k : ℝ) ^ 2 * log n := by ring
      linarith
    have : 14 * (3 * log n) = 42 * log n := by ring
    linarith
  have hhalf : dev (3 * log n) (mu x m) ≤ mu x m / 2 :=
    dev_le_half (by linarith : 0 ≤ 3 * log n) h14
  have hΛpos : 0 < ratioLam x := by
    have hM : 0 < (count x (some m) : ℝ) := by
      have hmax := maxCount_eq_of_plurality x hplur
      have hpos := maxCount_pos_of_und_zero x hq hn
      exact_mod_cast (hmax ▸ hpos)
    have hsq : 0 < (count x (some m) : ℝ) ^ 2 := by positivity
    have hsum : 0 < ∑ i, (count x (some i) : ℝ) ^ 2 :=
      lt_of_lt_of_le hsq
        (single_le_sum (f := fun i => (count x (some i) : ℝ) ^ 2)
          (fun i _ => sq_nonneg _) (mem_univ m))
    rw [ratioLam_of_und_zero x hq hn]
    exact div_pos (pow_pos hnR 2) hsum
  have hΛle : ratioLam x ≤ (k : ℝ) := ratioLam_le_card x
  have hΛ0 : 0 ≤ ratioLam x := hΛpos.le
  have hΛsq : ratioLam x ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hΛ0 hΛle 2
  have h48 : (48 : ℝ) * ratioLam x ^ 2 * log n ≤ n := by
    have hlog0 : 0 ≤ log n := hlogpos.le
    have h1 : (48 : ℝ) * ratioLam x ^ 2 ≤ 48 * (k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hΛsq (by norm_num)
    have h1' : (48 : ℝ) * ratioLam x ^ 2 * log n ≤ 48 * (k : ℝ) ^ 2 * log n :=
      mul_le_mul_of_nonneg_right h1 hlog0
    have h2 : (48 : ℝ) * (k : ℝ) ^ 2 ≤ 10000 * (k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have h2' : (48 : ℝ) * (k : ℝ) ^ 2 * log n ≤ 10000 * (k : ℝ) ^ 2 * log n :=
      mul_le_mul_of_nonneg_right h2 hlog0
    linarith
  have hs : (4 * ratioLam x) ^ 2 * (3 * log n) ≤ n := by
    have heq : (4 * ratioLam x) ^ 2 * (3 * log n) = 48 * ratioLam x ^ 2 * log n := by ring
    linarith
  have hsqrt : √((3 * log n) * n) ≤ n / (4 * ratioLam x) :=
    sqrt_ln_le (by linarith) (by positivity) hs
  have hdevU : dev (3 * log n) (muU x) ≤ n / (2 * ratioLam x) := by
    have hdev := dev_le (by linarith : 0 ≤ 3 * log n) (muU_le_n x hnR) h6
    have htwo : 2 * √((3 * log n) * n) ≤ n / (2 * ratioLam x) := by
      have heq : 2 * (n / (4 * ratioLam x)) = n / (2 * ratioLam x) := by
        field_simp
        norm_num
      linarith
    linarith
  have hS : ∀ y, Good (3 * log n) m x y → y ∈
      {y | (n : ℝ) / (2 * ratioR x ^ 2) ≤ cnt y m ∧
        (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 ∧
        n * (1 - 2 / ratioLam x) ≤ und y ∧ und y ≤ n * (1 - 1 / (2 * ratioLam x))} := by
    intro y hG
    exact first_of_good hnR (by linarith) hq hplur hhalf hdevU hG
  have hmiss := miss_round_le (by linarith : 0 < 3 * log n) m x _ hS
  calc
      miss {y | (n : ℝ) / (2 * ratioR x ^ 2) ≤ cnt y m ∧
          (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 ∧
          n * (1 - 2 / ratioLam x) ≤ und y ∧ und y ≤ n * (1 - 1 / (2 * ratioLam x))} 1 x
        ≤ ((k : ℝ) + 4) * exp (-(3 * log n)) := hmiss
    _ = ((k : ℝ) + 4) / (n : ℝ) ^ 3 := by
        rw [exp_neg_three_log hnR]
        ring
    _ ≤ 5 / (n : ℝ) ^ 2 := bad_prob_le (by omega) hk_le
    _ ≤ 5 / (n : ℝ) := five_div_sq_le (by omega)
    _ ≤ 100 / (n : ℝ) := by
        rw [div_le_div_iff₀ hnR hnR]
        have : (5 : ℝ) ≤ 100 := by norm_num
        exact mul_le_mul_of_nonneg_right this hnR.le

end Undecided.Plurality
