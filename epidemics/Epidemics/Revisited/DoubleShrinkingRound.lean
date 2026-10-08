import Epidemics.Revisited.DoubleShrinkingAux

/-! # One round in the double exponential shrinking regime (EPI-8)

`round_fail_le`: one round fails to bring the number of uninformed nodes below a target `z`
with probability at most `(1 + c) n / (z - u s)² + n^{1-α} n^{-τ} / z`, where `s` bounds the
probability of staying uninformed under Definition 13. Above `n^{1-α}` uninformed nodes this is
Chebyshev's inequality with the variance bound of Lemma 9 (Lemmas 44 and 45 of the paper);
below, it is Markov's inequality with fast finishing.

Also small facts on real powers of `n` used throughout.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

lemma npow_mono {n : ℕ} (hn : 1 ≤ n) {x y : ℝ} (h : x ≤ y) : (n : ℝ) ^ x ≤ (n : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

lemma npow_pos {n : ℕ} (hn : 1 ≤ n) (x : ℝ) : 0 < (n : ℝ) ^ x :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) x

lemma npow_add {n : ℕ} (hn : 1 ≤ n) (x y : ℝ) :
    (n : ℝ) ^ (x + y) = (n : ℝ) ^ x * (n : ℝ) ^ y :=
  Real.rpow_add (by exact_mod_cast hn) x y

lemma npow_pow {n : ℕ} (x : ℝ) (k : ℕ) : ((n : ℝ) ^ x) ^ k = (n : ℝ) ^ (x * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]

lemma npow_one' {n : ℕ} : (n : ℝ) ^ (1 : ℝ) = n := Real.rpow_one _

/-- Every constant is eventually below `n^ε`. -/
lemma exists_le_npow (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B ≤ (n : ℝ) ^ ε := by
  refine ⟨⌈(max B 1) ^ (1 / ε)⌉₊, fun n hn => ?_⟩
  have hB1 : 1 ≤ max B 1 := le_max_right _ _
  have hle : (max B 1) ^ (1 / ε) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have h0 : 0 ≤ (max B 1) ^ (1 / ε) := Real.rpow_nonneg (by linarith) _
  have := Real.rpow_le_rpow h0 hle hε.le
  rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hε.ne', Real.rpow_one] at this
  linarith [le_max_left B 1]

/-- `ln n` is eventually above every constant. -/
lemma exists_le_log (X : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → X ≤ Real.log n := by
  refine ⟨⌈Real.exp X⌉₊, fun n hn => ?_⟩
  have h1 : Real.exp X ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have := Real.log_le_log (Real.exp_pos X) h1
  rwa [Real.log_exp] at this

/-- One round of Definition 13 or of fast finishing (Lemmas 44 and 45, and Markov). -/
lemma round_fail_le (P : RumorProcess n) {ℓ a c g α τ s z : ℝ} (hc : 0 ≤ c)
    (hDES : P.UpperDoubleShrinking ℓ a c g α) (hFF : P.FastFinishing α τ)
    (hn : 1 ≤ n) (S : Finset (Fin n)) (hSg : (n : ℝ) - S.card ≤ g * n)
    (hs : (n : ℝ) ^ (1 - α) ≤ (n : ℝ) - S.card →
      a * (((n : ℝ) - S.card) / n) ^ (ℓ - 1) ≤ s)
    (hz : ((n : ℝ) - S.card) * s < z) (hz0 : 0 < z) :
    (P.K S).prob (fun T => z < (n : ℝ) - T.card) ≤
      (1 + c) * n / (z - ((n : ℝ) - S.card) * s) ^ 2 +
        (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / z := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hu0 : 0 ≤ (n : ℝ) - S.card := by have := card_cast_le S; linarith
  have hun : (n : ℝ) - S.card ≤ n := by have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _; linarith
  have hA : 0 ≤ (1 + c) * n / (z - ((n : ℝ) - S.card) * s) ^ 2 := by positivity
  have hB : 0 ≤ (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / z :=
    div_nonneg (mul_nonneg (npow_pos hn _).le (npow_pos hn _).le) hz0.le
  by_cases h : (n : ℝ) ^ (1 - α) ≤ (n : ℝ) - S.card
  · obtain ⟨h1, h2⟩ := hDES S h hSg
    have hupos : 0 < (n : ℝ) - S.card := lt_of_lt_of_le (npow_pos hn _) h
    have hstay : ∀ x ∉ S, 1 - P.informProb S x ≤ s := fun x hx => le_trans (h1 x hx) (hs h)
    have hE := expect_deficit_le_of_stay P S hstay
    have hc₀ : 0 ≤ c * n / ((n : ℝ) - S.card) ^ 2 := by positivity
    have hcheb := prob_deficit_gt_cheb P S hc₀ h2 hE hz
    have hnum : ((n : ℝ) - S.card) + c * n / ((n : ℝ) - S.card) ^ 2 * ((n : ℝ) - S.card) ^ 2
        ≤ (1 + c) * n := by
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 hupos.ne')]
      linarith
    have := div_le_div_of_nonneg_right hnum (sq_nonneg (z - ((n : ℝ) - S.card) * s))
    linarith
  · rw [not_le] at h
    have hstay : ∀ x ∉ S, 1 - P.informProb S x ≤ (n : ℝ) ^ (-τ) := hFF S h.le
    have hE := expect_deficit_le_of_stay P S hstay
    have hE' : (P.K S).expect (fun T => (n : ℝ) - T.card) ≤
        (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) :=
      le_trans hE (mul_le_mul_of_nonneg_right h.le (npow_pos hn _).le)
    have := prob_deficit_gt_markov P S hE' hz0
    linarith

/-- The phase calculus with `q = n^{-2δ}` and `λ = n^δ`: after `K + s` rounds,
`P[more than y K uninformed] ≤ 2^K n^{-δ s / 2}` (when `2 ≤ n^{δ/2}`). -/
lemma notYet_phase_npow (P : RumorProcess n) (y : ℕ → ℝ) (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hn : 1 ≤ n) (h2 : 2 ≤ (n : ℝ) ^ (δ / 2))
    (hstep : ∀ j, j < K → ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ y j →
      (P.K S).prob (fun T => y (j + 1) < (n : ℝ) - T.card) ≤ (n : ℝ) ^ (-(2 * δ)))
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ y 0) (s : ℕ) :
    P.notYet ((n : ℝ) - y K) (K + s) S ≤ 2 ^ K * (n : ℝ) ^ (-(δ / 2) * s) := by
  have hlam : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hn) hδ.le
  have hph := notYet_phase_le P y K (npow_pos hn _).le hlam hstep S hS (K + s)
  have hq : (n : ℝ) ^ (-(2 * δ)) + 1 / (n : ℝ) ^ δ ≤ 2 * (n : ℝ) ^ (-δ) := by
    have h1 : (n : ℝ) ^ (-(2 * δ)) ≤ (n : ℝ) ^ (-δ) := npow_mono hn (by linarith)
    have h2' : 1 / (n : ℝ) ^ δ = (n : ℝ) ^ (-δ) := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
    linarith
  have hθ0 : 0 ≤ (n : ℝ) ^ (-(2 * δ)) + 1 / (n : ℝ) ^ δ := by
    have := npow_pos hn (-(2 * δ)); have := npow_pos hn δ; positivity
  have hpow := pow_le_pow_left₀ hθ0 hq (K + s)
  have hlamK : 0 ≤ ((n : ℝ) ^ δ) ^ K := pow_nonneg (npow_pos hn _).le _
  have hstep2 := mul_le_mul_of_nonneg_right hpow hlamK
  have hcalc : (2 * (n : ℝ) ^ (-δ)) ^ (K + s) * ((n : ℝ) ^ δ) ^ K =
      2 ^ K * (2 ^ s * (n : ℝ) ^ (-δ * s)) := by
    rw [mul_pow, npow_pow, npow_pow]
    have : (n : ℝ) ^ (-δ * ((K + s : ℕ) : ℝ)) * (n : ℝ) ^ (δ * (K : ℝ)) =
        (n : ℝ) ^ (-δ * (s : ℝ)) := by
      rw [← npow_add hn]
      congr 1
      push_cast
      ring
    rw [mul_assoc, this, pow_add]
    ring
  have h2s : (2 : ℝ) ^ s * (n : ℝ) ^ (-δ * s) ≤ (n : ℝ) ^ (-(δ / 2) * s) := by
    have hp := pow_le_pow_left₀ (by norm_num) h2 s
    rw [npow_pow] at hp
    have := mul_le_mul_of_nonneg_right hp (npow_pos hn (-δ * s)).le
    rw [← npow_add hn] at this
    have he : δ / 2 * (s : ℝ) + -δ * s = -(δ / 2) * s := by ring
    rw [he] at this
    exact this
  calc P.notYet ((n : ℝ) - y K) (K + s) S
      ≤ ((n : ℝ) ^ (-(2 * δ)) + 1 / (n : ℝ) ^ δ) ^ (K + s) * ((n : ℝ) ^ δ) ^ K := hph
    _ ≤ (2 * (n : ℝ) ^ (-δ)) ^ (K + s) * ((n : ℝ) ^ δ) ^ K := hstep2
    _ = 2 ^ K * (2 ^ s * (n : ℝ) ^ (-δ * s)) := hcalc
    _ ≤ 2 ^ K * (n : ℝ) ^ (-(δ / 2) * s) :=
        mul_le_mul_of_nonneg_left h2s (pow_nonneg (by norm_num) _)

end Epidemics.Revisited
