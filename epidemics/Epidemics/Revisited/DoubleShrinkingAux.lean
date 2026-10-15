import Epidemics.Revisited.DoubleShrinkingDefs
import Epidemics.Revisited.ShrinkingPotential
import Dynamics.Phases

/-! # Phase calculus with potentials (EPI-8, double exponential shrinking)

Generic finite-time tools for Theorem 43:

* `closed_of_superset`: a region closed under informing more nodes is closed under the rounds,
  so the core's contraction on a closed region (`Dynamics.Kernel.iterate_le_pow_of_closed`)
  applies: a potential that contracts by `θ` in one round on the region contracts by `θ^t` in
  `t` rounds.
* `notYet_phase_le`: a phase calculus (the core's `Dynamics.Kernel.iterate_outside_le_of_phases`).
  Given thresholds `y 0, …, y J` on the number of uninformed nodes, if from at most `y j`
  uninformed nodes one round fails to reach at most `y (j + 1)` with probability at most `q`,
  then from at most `y 0` uninformed nodes, more than `y J` remain after `t` rounds with
  probability at most `(q + 1/λ)^t λ^J`, for every `λ ≥ 1`. The potential is `λ^{J - j}` in
  phase `j` (the last phase reached), and `0` from phase `J` on; it replaces the stochastic
  domination by sums of geometric variables (Lemma 47).
* `notYet_finish_le`: if every uninformed node stays uninformed with probability at most `θ`,
  then the expected number of uninformed nodes contracts by `θ` per round, and by Markov's
  inequality some node is still uninformed after `t` rounds with probability at most
  `θ^t (n - |S|)`.
* `prob_deficit_gt_cheb` and `prob_deficit_gt_markov`: the one-round failure probabilities, by
  Chebyshev's inequality with the variance bound of Lemma 9, or by Markov's inequality.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-- A region of states closed under informing more nodes is closed under the rounds. -/
lemma closed_of_superset (P : RumorProcess n) (R : Finset (Fin n) → Prop)
    (hR : ∀ S T, R S → S ⊆ T → R T) :
    ∀ S T, R S → (P.K S).weight T ≠ 0 → R T :=
  fun S T hS hw => hR S T hS (not_not.mp fun h => hw (weight_zero_of_not_subset P h))

lemma card_le_of_subset_real {S T : Finset (Fin n)} (h : S ⊆ T) : (S.card : ℝ) ≤ T.card :=
  Nat.cast_le.mpr (card_le_card h)

/-- Phase calculus: from at most `y 0` uninformed nodes, more than `y J` remain after `t` rounds
with probability at most `(q + 1/λ)^t λ^J`. The core's `Kernel.iterate_outside_le_of_phases`
with the phases `A j` = "at most `y j` uninformed nodes", closed under the rounds since the
informed set only grows. -/
lemma notYet_phase_le (P : RumorProcess n) (y : ℕ → ℝ) (J : ℕ) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 1 ≤ lam)
    (hstep : ∀ j, j < J → ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ y j →
      (P.K S).prob (fun T => y (j + 1) < (n : ℝ) - T.card) ≤ q)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ y 0) (t : ℕ) :
    P.notYet ((n : ℝ) - y J) t S ≤ (q + 1 / lam) ^ t * lam ^ J := by
  set A : ℕ → Set (Finset (Fin n)) := fun j => {T | (n : ℝ) - T.card ≤ y j}
  have hclosed : ∀ j ≤ J, ∀ S T, S ∈ A j → (P.K S).weight T ≠ 0 → T ∈ A j :=
    fun j _ => closed_of_superset P (· ∈ A j) fun S T (hS : (n : ℝ) - S.card ≤ y j) hST => by
      change (n : ℝ) - T.card ≤ y j
      linarith [card_le_of_subset_real hST]
  have hmove : ∀ j < J, ∀ S ∈ A j, 1 - q ≤ (P.K S).prob (· ∈ A (j + 1)) := by
    intro j hj S hS
    have h := (P.K S).one_sub_prob_le_prob (s := fun T => y (j + 1) < (n : ℝ) - T.card)
      (t := (· ∈ A (j + 1))) fun T hT => by
        change (n : ℝ) - T.card ≤ y (j + 1)
        exact not_lt.mp hT
    linarith [hstep j hj S hS]
  have hout : below ((n : ℝ) - y J) = Kernel.outside (A J) := by
    funext T
    by_cases h : (n : ℝ) - T.card ≤ y J
    · rw [Kernel.outside_of_mem (show T ∈ A J from h)]
      have : ¬ (T.card : ℝ) < (n : ℝ) - y J := by linarith
      simp [below, this]
    · rw [Kernel.outside_of_not_mem (show T ∉ A J from h)]
      have : (T.card : ℝ) < (n : ℝ) - y J := by linarith [not_le.mp h]
      simp [below, this]
  rw [notYet_below, hout]
  exact Kernel.iterate_outside_le_of_phases P.K A J hq hlam hclosed hmove S hS t

/-- Finishing: if every uninformed node stays uninformed with probability at most `θ` in every
round started with at most `U` uninformed nodes, then from such a state some node is still
uninformed after `t` rounds with probability at most `θ^t (n - |S|)`. -/
lemma notYet_finish_le (P : RumorProcess n) {U θ : ℝ} (hθ : 0 ≤ θ)
    (hstep : ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ U → ∀ x ∉ S, 1 - P.informProb S x ≤ θ)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ U) (t : ℕ) :
    P.notYet n t S ≤ θ ^ t * ((n : ℝ) - S.card) := by
  have hR : ∀ S T : Finset (Fin n), (n : ℝ) - S.card ≤ U → S ⊆ T → (n : ℝ) - T.card ≤ U := by
    intro S T hS hST
    have := card_le_of_subset_real hST
    linarith
  have happ : ∀ T : Finset (Fin n), (n : ℝ) - T.card ≤ U →
      P.K.apply (fun T => (n : ℝ) - T.card) T ≤ θ * ((n : ℝ) - T.card) := by
    intro T hT
    rw [Kernel.apply, expect_deficit]
    calc ∑ x ∈ (univ : Finset (Fin n)) \ T, (1 - P.informProb T x)
        ≤ ∑ x ∈ (univ : Finset (Fin n)) \ T, θ :=
          sum_le_sum fun x hx => hstep T hT x (mem_sdiff.mp hx).2
      _ = θ * ((n : ℝ) - T.card) := by rw [sum_const, nsmul_eq_mul, card_compl_cast, mul_comm]
  have hit := Kernel.iterate_le_pow_of_closed P.K (fun T => (n : ℝ) - T.card ≤ U)
    (closed_of_superset P _ hR) _ hθ happ t S hS
  have hind : ∀ T : Finset (Fin n), below (n : ℝ) T ≤ (n : ℝ) - T.card := by
    intro T
    unfold below
    split_ifs with h
    · have h' : T.card < n := by exact_mod_cast h
      have : (T.card : ℝ) + 1 ≤ n := by exact_mod_cast h'
      linarith
    · have := card_cast_le T
      linarith
  rw [notYet_below]
  exact le_trans (P.K.iterate_mono t hind S) hit

/-- Chebyshev for one round: if the expected number of uninformed nodes after the round is at
most `μ < z` and distinct uninformed nodes have covariance at most `c₀ ≥ 0`, then more than `z`
nodes stay uninformed with probability at most `(u + c₀ u²) / (z - μ)²`, `u = n - |S|`. -/
lemma prob_deficit_gt_cheb (P : RumorProcess n) (S : Finset (Fin n)) {c₀ μ z : ℝ}
    (hc₀ : 0 ≤ c₀) (hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c₀)
    (hμ : (P.K S).expect (fun T => (n : ℝ) - T.card) ≤ μ) (hz : μ < z) :
    (P.K S).prob (fun T => z < (n : ℝ) - T.card) ≤
      (((n : ℝ) - S.card) + c₀ * ((n : ℝ) - S.card) ^ 2) / (z - μ) ^ 2 := by
  set D := P.K S
  set X : Finset (Fin n) → ℝ := fun T => (T.card : ℝ)
  have hEX : D.expect (fun T => (n : ℝ) - T.card) = (n : ℝ) - D.expect X := by
    rw [Distribution.expect_sub, Distribution.expect_const]
  have hlam : 0 < z - μ := by linarith
  have hsub : D.prob (fun T => z < (n : ℝ) - T.card) ≤
      D.prob (fun T => z - μ ≤ |X T - D.expect X|) := by
    refine Distribution.prob_mono D (fun T hT => ?_)
    have : z - μ ≤ D.expect X - X T := by simp only [X]; linarith
    exact le_trans this (by rw [abs_sub_comm]; exact le_abs_self _)
  have hcheb := chebyshev D X hlam
  have hvar := variance_card_le_proof P S hc₀ hcov
  have hinc : D.expect X - S.card ≤ (n : ℝ) - S.card := by
    have hle : D.expect X ≤ D.expect (fun _ => (n : ℝ)) := D.expect_mono fun T => card_cast_le T
    rw [Distribution.expect_const] at hle
    linarith
  have hvar' : D.expect (fun T => (X T - D.expect X) ^ 2) ≤
      ((n : ℝ) - S.card) + c₀ * ((n : ℝ) - S.card) ^ 2 := by
    have := hvar
    simp only [X, D] at this ⊢
    linarith
  calc D.prob (fun T => z < (n : ℝ) - T.card)
      ≤ D.prob (fun T => z - μ ≤ |X T - D.expect X|) := hsub
    _ ≤ D.expect (fun T => (X T - D.expect X) ^ 2) / (z - μ) ^ 2 := hcheb
    _ ≤ (((n : ℝ) - S.card) + c₀ * ((n : ℝ) - S.card) ^ 2) / (z - μ) ^ 2 :=
        div_le_div_of_nonneg_right hvar' (by positivity)

/-- Markov for one round: more than `z > 0` nodes stay uninformed with probability at most
`μ / z` when their expected number is at most `μ`. -/
lemma prob_deficit_gt_markov (P : RumorProcess n) (S : Finset (Fin n)) {μ z : ℝ}
    (hμ : (P.K S).expect (fun T => (n : ℝ) - T.card) ≤ μ) (hz : 0 < z) :
    (P.K S).prob (fun T => z < (n : ℝ) - T.card) ≤ μ / z := by
  classical
  set D := P.K S
  have hpt : ∀ T : Finset (Fin n), (if z < (n : ℝ) - T.card then (1 : ℝ) else 0) ≤
      ((n : ℝ) - T.card) / z := by
    intro T
    split_ifs with h
    · rw [le_div_iff₀ hz]; linarith
    · exact div_nonneg (by have := card_cast_le T; linarith) hz.le
  have hE := D.expect_mono hpt
  rw [expect_div] at hE
  rw [prob_indicator_eq D _ (fun T => if z < (n : ℝ) - T.card then (1 : ℝ) else 0)
    (fun T h => by simp [h]) (fun T h => by simp [h])]
  exact le_trans hE (div_le_div_of_nonneg_right hμ hz.le)

/-- The expected number of uninformed nodes after a round where each uninformed node stays
uninformed with probability at most `s`. -/
lemma expect_deficit_le_of_stay (P : RumorProcess n) (S : Finset (Fin n)) {s : ℝ}
    (h : ∀ x ∉ S, 1 - P.informProb S x ≤ s) :
    (P.K S).expect (fun T => (n : ℝ) - T.card) ≤ ((n : ℝ) - S.card) * s := by
  rw [expect_deficit]
  calc ∑ x ∈ (univ : Finset (Fin n)) \ S, (1 - P.informProb S x)
      ≤ ∑ x ∈ (univ : Finset (Fin n)) \ S, s :=
        sum_le_sum fun x hx => h x (mem_sdiff.mp hx).2
    _ = ((n : ℝ) - S.card) * s := by rw [sum_const, nsmul_eq_mul, card_compl_cast]

end Epidemics.Revisited
