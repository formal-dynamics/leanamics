import Epidemics.SubcriticalProb

/-! # Binomial tails and the Chernoff bound of Theorem E.1 (EPI-2)

The tail `binTail p m k` of the number of successes in `m` independent Bernoulli(`p`) trials (the
coin `Distribution.bernoulli` of the Chernoff bounds of `dynamics/`), its one-step recursion
(condition on the first trial), and the Chernoff bound used in the proof of Theorem E.1 of
Becchetti, Clementi, Denni, Pasquale, Trevisan, Ziccardi, *Percolation and epidemic processes in
one-dimensional small-world networks* (arXiv:2103.16398).

The paper tilts by `ε` rather than by the optimal `log (1 + δ)`, which gives its closed form
`exp (ε - ε² t / 2)`. Markov's inequality on `exp (ε X)` and the bound on the moment-generating
function are the core's `Distribution.prob_ge_le_exp` (`Dynamics.ChernoffAux`, FND-3); only the
scalar inequality `(1 - ε) e^ε ≤ 1 - ε² / 2` and the arithmetic of the paper's constants are local.
-/

namespace Epidemics
open Finset Dynamics

/-- The tail of a binomial distribution: the probability of at least `k` successes in `m`
independent Bernoulli(`p`) trials. -/
noncomputable def binTail (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (m k : ℕ) : ℝ :=
  (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
    (fun ξ => k ≤ (univ.filter fun i => ξ i = true).card)

section BinTail
variable {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)

lemma binTail_zero_right (m : ℕ) : binTail p h0 h1 m 0 = 1 :=
  prob_eq_one _ fun _ => Nat.zero_le _

lemma binTail_nonneg (m k : ℕ) : 0 ≤ binTail p h0 h1 m k :=
  Distribution.prob_nonneg _ _

/-- Successes among `b` followed by `r`. -/
lemma card_filter_cons {m : ℕ} (b : Bool) (r : Fin m → Bool) :
    (univ.filter fun i => (Fin.cons b r : Fin (m + 1) → Bool) i = true).card =
      (if b = true then 1 else 0) + (univ.filter fun i => r i = true).card := by
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  simp

/-- Probabilities under an i.i.d. product over `Fin (m + 1)`, conditioned on the first trial. -/
lemma independent_prob_fin_succ {β : Type*} [Fintype β] {m : ℕ} (q : Distribution β)
    (s : (Fin (m + 1) → β) → Prop) :
    (Distribution.independent fun _ : Fin (m + 1) => q).prob s =
      ∑ b, q.weight b *
        (Distribution.independent fun _ : Fin m => q).prob (fun r => s (Fin.cons b r)) := by
  unfold Distribution.prob
  exact independent_expect_fin_succ q _

/-- **One-step recursion of the binomial tail**: condition on the first trial. -/
lemma binTail_succ_succ (m k : ℕ) :
    binTail p h0 h1 (m + 1) (k + 1) =
      p * binTail p h0 h1 m k + (1 - p) * binTail p h0 h1 m (k + 1) := by
  unfold binTail
  rw [independent_prob_fin_succ, Fintype.sum_bool]
  simp only [card_filter_cons, if_true, Bool.false_eq_true, if_false, zero_add]
  have ht : ∀ c : ℕ, k + 1 ≤ 1 + c ↔ k ≤ c := fun c => by omega
  simp only [ht]
  simp [Distribution.bernoulli]

end BinTail

/-- The key scalar inequality `(1 - ε) e^ε ≤ 1 - ε² / 2` for `0 ≤ ε < 1`. -/
lemma one_sub_mul_exp_le {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    (1 - ε) * Real.exp ε ≤ 1 - ε ^ 2 / 2 := by
  have hexp := exp_le_one_add_add_sq_div (x := ε) (by linarith)
  have hden : 0 < 2 * (1 - ε / 3) := by linarith
  have hq : ε ^ 2 / (2 * (1 - ε / 3)) * (1 - ε) ≤ ε ^ 2 / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]
    nlinarith [sq_nonneg ε]
  calc (1 - ε) * Real.exp ε
      ≤ (1 - ε) * (1 + ε + ε ^ 2 / (2 * (1 - ε / 3))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = 1 - ε ^ 2 + ε ^ 2 / (2 * (1 - ε / 3)) * (1 - ε) := by ring
    _ ≤ 1 - ε ^ 2 / 2 := by linarith

/-- **Chernoff bound** for the proof of Theorem E.1: if `p (d - 1) ≤ 1 - ε` with `0 < ε < 1`, then
at least `t` successes among `t (d - 1) + 1` independent Bernoulli(`p`) trials occur with
probability at most `exp (ε - ε² t / 2)`. -/
theorem binomial_tail_le {d : ℕ} {p ε : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hp : p * ((d : ℝ) - 1) ≤ 1 - ε) (t : ℕ) :
    (Distribution.independent fun _ : Fin (t * (d - 1) + 1) =>
        Distribution.bernoulli p h0 h1).prob
        (fun ξ => t ≤ (univ.filter fun i => ξ i = true).card) ≤
      Real.exp (ε - ε ^ 2 * t / 2) := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · -- `d ≤ 1`: a single trial
    have hm : t * (d - 1) + 1 = 1 := by
      rw [Nat.sub_eq_zero_of_le (by omega), mul_zero]
    rcases Nat.lt_or_ge t 2 with ht | ht
    · calc _ ≤ (1 : ℝ) := Distribution.prob_le_one _ _
        _ ≤ _ := by
          apply Real.one_le_exp
          have ht' : (t : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp ht
          nlinarith [sq_nonneg ε]
    · rw [prob_eq_zero]
      · exact (Real.exp_pos _).le
      · intro ξ hξ
        have hle := card_filter_le (univ : Finset (Fin (t * (d - 1) + 1))) fun i => ξ i = true
        rw [card_univ, Fintype.card_fin] at hle
        have h1' : (univ.filter fun i => ξ i = true).card ≤ 1 := hle.trans hm.le
        omega
  · -- `d ≥ 2`: Markov's inequality on `exp (ε X)` (core `prob_ge_le_exp`, tilt `ε`)
    have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hp' : p ≤ 1 - ε := le_trans (le_mul_of_one_le_right h0 hd1) hp
    set m := t * (d - 1) + 1 with hm
    have hmR : (m : ℝ) = t * ((d : ℝ) - 1) + 1 := by
      rw [hm]
      push_cast [Nat.cast_sub (by omega : 1 ≤ d)]
      ring
    have ht0 : (0 : ℝ) ≤ t := t.cast_nonneg
    -- the mean `m p` is at most `(1 - ε) (t + 1)`
    have hmean : ∑ _i : Fin m, (Distribution.bernoulli p h0 h1).expect
        (fun b => if b = true then (1 : ℝ) else 0) ≤ (1 - ε) * (t + 1) := by
      simp only [Distribution.bernoulli_expect, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      norm_num
      rw [hmR]
      nlinarith
    have hcore := Distribution.prob_ge_le_exp (fun _ : Fin m => Distribution.bernoulli p h0 h1)
      (fun _ b => if b = true then (1 : ℝ) else 0) (fun _ b => by cases b <;> simp) hε.le
      hmean (t : ℝ)
    simp only [sum_boole] at hcore
    have ha : 0 ≤ Real.exp ε - 1 := by linarith [Real.add_one_le_exp ε]
    -- `(1 - ε) (e^ε - 1) ≤ ε - ε² / 2`
    have hb : (1 - ε) * (Real.exp ε - 1) ≤ ε - ε ^ 2 / 2 := by
      linarith [one_sub_mul_exp_le hε.le hε1]
    calc (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
            (fun ξ => t ≤ (univ.filter fun i => ξ i = true).card)
        = (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
            (fun ξ => (t : ℝ) ≤ ((univ.filter fun i => ξ i = true).card : ℝ)) :=
          prob_congr _ fun ξ => Nat.cast_le.symm
      _ ≤ Real.exp ((1 - ε) * (t + 1) * (Real.exp ε - 1) - ε * t) := hcore
      _ ≤ Real.exp (ε - ε ^ 2 * t / 2) := by
          apply Real.exp_le_exp.mpr
          calc (1 - ε) * (t + 1) * (Real.exp ε - 1) - ε * t
              = (t + 1) * ((1 - ε) * (Real.exp ε - 1)) - ε * t := by ring
            _ ≤ (t + 1) * (ε - ε ^ 2 / 2) - ε * t := by gcongr
            _ ≤ ε - ε ^ 2 * t / 2 := by nlinarith [sq_nonneg ε]

end Epidemics
