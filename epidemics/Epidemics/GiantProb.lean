import Epidemics.GiantCoins

/-! # Counting positive answers among i.i.d. trials (EPI-3)

The probabilistic half of the proofs of Krivelevich–Sudakov (*The phase transition in random
graphs: a simple proof*, Random Structures & Algorithms 43 (2013), arXiv:1201.6529): Lemma 1,
part 2, with the Chernoff bounds of FND-3 (`Dynamics.Chernoff`) in place of Chebyshev's inequality,
as suggested in the paper's Discussion, item 1.

The trials are `x : Fin m → Bool` under `independent (fun _ => bernoulli p)`, listed as
`List.ofFn x`, so that `((List.ofFn x).take t).count true` is the number of successes among the
first `t` trials (`count_take_ofFn`).

* `prob_count_take_le`, `prob_count_take_ge`: lower and upper tails for the first `t` trials.
* `prob_count_take_far`: Lemma 1, part 2.
* `Good`, `prob_not_good_le`: the typical properties used in the proof of Theorem 2 (the counts at
  times `t₁` and `N₀`, and at every time between them, are close to their means).
* `pow_three_mul_exp_neg_le`: `x³ e^{-κx} ≤ 6 / κ³`, to turn exponential bounds into `C / n`.
-/

namespace Epidemics
open Finset Dynamics

/-- The number of successes among the first `t` trials. -/
lemma count_take_ofFn {m : ℕ} (x : Fin m → Bool) (t : ℕ) :
    ((List.ofFn x).take t).count true =
      ((univ.filter fun j : Fin m => j.val < t).filter fun j => x j = true).card := by
  rw [filter_filter, card_filter]
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    cases t with
    | zero => simp
    | succ t =>
      rw [List.take_succ_cons, List.count_cons, ih (fun i => x i.succ) t]
      simp only [Fin.val_zero, Nat.zero_lt_succ, true_and, Fin.val_succ, Nat.add_lt_add_iff_right,
        beq_iff_eq]
      split_ifs <;> simp_all
      omega

lemma sum_filter_lt {m t : ℕ} (ht : t ≤ m) (p : ℝ) :
    ∑ _i ∈ univ.filter (fun j : Fin m => j.val < t), p = t * p := by
  rw [sum_const, Fin.card_filter_val_lt, min_eq_right ht, nsmul_eq_mul]

variable (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)

/-- **Lower tail** for the first `t ≤ m` trials (Chernoff, FND-3):
`P(∑_{i<t} Xᵢ ≤ (1 - δ) t p) ≤ exp (-δ² t p / 2)`. -/
lemma prob_count_take_le {m t : ℕ} (ht : t ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
        (fun x => (((List.ofFn x).take t).count true : ℝ) ≤ (1 - δ) * (t * p)) ≤
      Real.exp (-(δ ^ 2 * (t * p) / 2)) := by
  have h := Distribution.bernoulli_chernoff_lower (fun _ : Fin m => p) (fun _ => h0) (fun _ => h1)
    (univ.filter fun j : Fin m => j.val < t) hδ0 hδ1 (sum_filter_lt ht p).ge
  refine (Distribution.prob_mono _ fun x hx => ?_).trans h
  rwa [count_take_ofFn] at hx

/-- **Upper tail** for the first `t ≤ m` trials (Chernoff, FND-3):
`P(∑_{i<t} Xᵢ ≥ (1 + δ) t p) ≤ exp (-δ² t p / 3)` for `δ < 1`. -/
lemma prob_count_take_ge {m t : ℕ} (ht : t ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
        (fun x => (1 + δ) * (t * p) ≤ (((List.ofFn x).take t).count true : ℝ)) ≤
      Real.exp (-(δ ^ 2 * (t * p) / 3)) := by
  have h := Distribution.bernoulli_chernoff_upper (fun _ : Fin m => p) (fun _ => h0) (fun _ => h1)
    (univ.filter fun j : Fin m => j.val < t) hδ0 (sum_filter_lt ht p).le
  refine (Distribution.prob_mono _ fun x hx => ?_).trans (h.trans ?_)
  · rwa [count_take_ofFn] at hx
  · rw [Real.exp_le_exp, neg_le_neg_iff]
    have : 0 ≤ δ ^ 2 * (t * p) := by positivity
    exact div_le_div_of_nonneg_left this (by linarith) (by linarith)

/-- **Krivelevich–Sudakov, Lemma 1, part 2**, with the Chernoff bounds (FND-3) instead of
Chebyshev's inequality, as in their Discussion, item 1: among the first `N₀` of `m` i.i.d.
Bernoulli(`p`) trials, the number of successes deviates from its mean `N₀ p` by at least `δ N₀ p`
with probability at most `2 exp (-δ² N₀ p / 3)`. -/
theorem prob_count_take_far {m N₀ : ℕ} (hN₀ : N₀ ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
        (fun x => δ * (N₀ * p) ≤ |(((List.ofFn x).take N₀).count true : ℝ) - N₀ * p|) ≤
      2 * Real.exp (-(δ ^ 2 * (N₀ * p) / 3)) := by
  have hexp : Real.exp (-(δ ^ 2 * (N₀ * p) / 2)) ≤ Real.exp (-(δ ^ 2 * (N₀ * p) / 3)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have : 0 ≤ δ ^ 2 * (N₀ * p) := by positivity
    linarith
  calc _ ≤ (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
          (fun x => (((List.ofFn x).take N₀).count true : ℝ) ≤ (1 - δ) * (N₀ * p) ∨
            (1 + δ) * (N₀ * p) ≤ (((List.ofFn x).take N₀).count true : ℝ)) := by
        refine Distribution.prob_mono _ fun x hx => ?_
        rcases le_abs'.mp hx with h | h
        · left; linarith
        · right; linarith
    _ ≤ _ := (prob_or_le _ _ _).trans
        (add_le_add (prob_count_take_le p h0 h1 hN₀ hδ0 hδ1)
          (prob_count_take_ge p h0 h1 hN₀ hδ0 hδ1))
    _ ≤ _ := by linarith

/-- The typical behaviour of the answers used in the proof of Theorem 2: the numbers of positive
answers among the first `N₀` and the first `t₁` are at most `(1 + δ)` times their means, and
among the first `t` at least `(1 - δ)` times the mean for every `t₁ ≤ t ≤ N₀`. -/
def Good (N₀ t₁ : ℕ) (δ : ℝ) (L : List Bool) : Prop :=
  ((L.take N₀).count true : ℝ) ≤ (1 + δ) * (N₀ * p) ∧
    ((L.take t₁).count true : ℝ) ≤ (1 + δ) * (t₁ * p) ∧
    ∀ t ∈ Icc t₁ N₀, (1 - δ) * (t * p) ≤ ((L.take t).count true : ℝ)

/-- The answers are typical except with probability `(N₀ + 3) exp (-δ² t₁ p / 3)`. -/
theorem prob_not_good_le {N₀ t₁ : ℕ} (ht₁ : t₁ ≤ N₀) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Distribution.independent fun _ : Fin N₀ => Distribution.bernoulli p h0 h1).prob
        (fun x => ¬Good p N₀ t₁ δ (List.ofFn x)) ≤
      (N₀ + 3) * Real.exp (-(δ ^ 2 * (t₁ * p) / 3)) := by
  set P := Distribution.independent fun _ : Fin N₀ => Distribution.bernoulli p h0 h1
  set E := Real.exp (-(δ ^ 2 * (t₁ * p) / 3))
  have hmono {t : ℕ} (ht : t₁ ≤ t) : Real.exp (-(δ ^ 2 * (t * p) / 3)) ≤ E := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have : (t₁ : ℝ) * p ≤ t * p := mul_le_mul_of_nonneg_right (by exact_mod_cast ht) h0
    have : δ ^ 2 * (t₁ * p) ≤ δ ^ 2 * (t * p) := mul_le_mul_of_nonneg_left this (sq_nonneg δ)
    linarith
  have hlow {t : ℕ} (ht : t₁ ≤ t) (htN : t ≤ N₀) :
      P.prob (fun x => ¬(1 - δ) * (t * p) ≤ (((List.ofFn x).take t).count true : ℝ)) ≤ E := by
    refine (Distribution.prob_mono _ fun x hx => (not_le.mp hx).le).trans
      ((prob_count_take_le p h0 h1 htN hδ0 hδ1).trans ?_)
    refine le_trans ?_ (hmono ht)
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have : 0 ≤ δ ^ 2 * (t * p) := by positivity
    linarith
  have hhigh {t : ℕ} (ht : t₁ ≤ t) (htN : t ≤ N₀) :
      P.prob (fun x => ¬(((List.ofFn x).take t).count true : ℝ) ≤ (1 + δ) * (t * p)) ≤ E :=
    (Distribution.prob_mono _ fun x hx => (not_le.mp hx).le).trans
      ((prob_count_take_ge p h0 h1 htN hδ0 hδ1).trans (hmono ht))
  calc P.prob (fun x => ¬Good p N₀ t₁ δ (List.ofFn x))
      ≤ P.prob (fun x => ¬(((List.ofFn x).take N₀).count true : ℝ) ≤ (1 + δ) * (N₀ * p) ∨
          (¬(((List.ofFn x).take t₁).count true : ℝ) ≤ (1 + δ) * (t₁ * p) ∨
            ∃ t ∈ Icc t₁ N₀,
              ¬(1 - δ) * (t * p) ≤ (((List.ofFn x).take t).count true : ℝ))) := by
        refine Distribution.prob_mono _ fun x hx => ?_
        simp only [Good, not_and_or, not_forall, exists_prop] at hx
        exact hx
    _ ≤ E + (E + ∑ t ∈ Icc t₁ N₀, E) := by
        refine (prob_or_le _ _ _).trans (add_le_add (hhigh ht₁ le_rfl)
          ((prob_or_le _ _ _).trans (add_le_add (hhigh le_rfl ht₁) ?_)))
        refine (prob_exists_le_sum _ _ _).trans (sum_le_sum fun t ht => ?_)
        obtain ⟨h₁, h₂⟩ := mem_Icc.mp ht
        exact hlow h₁ h₂
    _ ≤ (N₀ + 3) * E := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hE : 0 ≤ E := (Real.exp_pos _).le
        have : ((N₀ + 1 - t₁ : ℕ) : ℝ) ≤ N₀ + 1 := by
          have := Nat.sub_le (N₀ + 1) t₁
          exact_mod_cast this
        nlinarith

/-- `x³ e^{-κx} ≤ 6 / κ³` for `κ > 0`, `x ≥ 0`. -/
lemma pow_three_mul_exp_neg_le {κ : ℝ} (hκ : 0 < κ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ 3 * Real.exp (-(κ * x)) ≤ 6 / κ ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (κ * x) (by positivity) 3
  rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num [Nat.factorial]] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith [Real.exp_pos (κ * x)]

end Epidemics
