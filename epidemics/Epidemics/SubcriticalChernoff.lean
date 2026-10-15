import Dynamics.Chernoff

/-! # The Chernoff bound of Theorem E.1 (EPI-2)

The Chernoff bound used in the proof of Theorem E.1 of Becchetti, Clementi, Denni, Pasquale,
Trevisan, Ziccardi, *Percolation and epidemic processes in one-dimensional small-world networks*
(arXiv:2103.16398), for the number of successes in independent Bernoulli(`p`) trials (the coin
`Distribution.bernoulli` of the Chernoff bounds of `dynamics/`). The binomial tail
`Distribution.binTail` and its one-step recursion `Distribution.binTail_succ_succ`, used by the
exploration of `SubcriticalExploration.lean`, are the core's (`Dynamics.Chernoff`).

The paper tilts by `ε` rather than by the optimal `log (1 + δ)`, which gives its closed form
`exp (ε - ε² t / 2)`. Markov's inequality on `exp (ε X)`, the bound on the moment-generating
function and the scalar inequality `(1 - ε) e^ε ≤ 1 - ε² / 2`
(`one_sub_mul_exp_le_one_sub_sq_div_two`) are the core's fixed-tilt tail
`Distribution.prob_ge_le_exp_tilt` (`Dynamics.ChernoffAux`, FND-3); only the arithmetic of the
paper's constants is local.
-/

namespace Epidemics
open Finset Dynamics

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
    · rw [Distribution.prob_eq_zero]
      · exact (Real.exp_pos _).le
      · intro ξ hξ
        have hle := card_filter_le (univ : Finset (Fin (t * (d - 1) + 1))) fun i => ξ i = true
        rw [card_univ, Fintype.card_fin] at hle
        have h1' : (univ.filter fun i => ξ i = true).card ≤ 1 := hle.trans hm.le
        omega
  · -- `d ≥ 2`: Markov's inequality on `exp (ε X)` (core `prob_ge_le_exp_tilt`, tilt `ε`)
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
    have hcore := Distribution.prob_ge_le_exp_tilt
      (fun _ : Fin m => Distribution.bernoulli p h0 h1)
      (fun _ b => if b = true then (1 : ℝ) else 0) (fun _ b => by cases b <;> simp) hε.le hε1
      (by positivity) hmean (t : ℝ)
    simp only [sum_boole] at hcore
    calc (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
            (fun ξ => t ≤ (univ.filter fun i => ξ i = true).card)
        = (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
            (fun ξ => (t : ℝ) ≤ ((univ.filter fun i => ξ i = true).card : ℝ)) :=
          Distribution.prob_congr _ fun ξ => Nat.cast_le.symm
      _ ≤ Real.exp ((t + 1) * (ε - ε ^ 2 / 2) - ε * t) := hcore
      _ ≤ Real.exp (ε - ε ^ 2 * t / 2) := by
          apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg ε]

end Epidemics
