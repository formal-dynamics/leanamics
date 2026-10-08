import Epidemics.Revisited.DoubleShrinkingDefs
import Epidemics.Revisited.ShrinkingPotential

/-! # Phase calculus with potentials (EPI-8, double exponential shrinking)

Generic finite-time tools for Theorem 43:

* `iterate_le_pow_of_region`: a potential that contracts by `θ` in one round, from every state of
  a region closed under informing more nodes, contracts by `θ^t` in `t` rounds.
* `notYet_phase_le`: a phase calculus. Given thresholds `y 0, …, y J` on the number of
  uninformed nodes, if from at most `y j` uninformed nodes one round fails to reach at most
  `y (j + 1)` with probability at most `q`, then from at most `y 0` uninformed nodes, more than
  `y J` remain after `t` rounds with probability at most `(q + 1/λ)^t λ^J`, for every `λ ≥ 1`.
  The potential is `λ^{J - j}` in phase `j` (the last phase reached), and `0` from phase `J` on;
  it replaces the stochastic domination by sums of geometric variables (Lemma 47).
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

/-- Contraction of a potential on a region closed under informing more nodes. -/
lemma iterate_le_pow_of_region (P : RumorProcess n) (R : Finset (Fin n) → Prop)
    (hR : ∀ S T, R S → S ⊆ T → R T) (Ψ : Finset (Fin n) → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hstep : ∀ S, R S → P.K.apply Ψ S ≤ θ * Ψ S) :
    ∀ t S, R S → P.K.iterate t Ψ S ≤ θ ^ t * Ψ S := by
  intro t
  induction t with
  | zero => intro S _; simp
  | succ t ih =>
    intro S hS
    rw [Kernel.iterate_succ, Kernel.apply]
    have h1 : (P.K S).expect (P.K.iterate t Ψ) ≤ (P.K S).expect (fun T => θ ^ t * Ψ T) :=
      expect_le_of_weight P S (fun T hST => ih T (hR S T hS hST))
    rw [Distribution.expect_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hstep S hS) (pow_nonneg hθ t)
    rw [Kernel.apply] at h2
    calc (P.K S).expect (P.K.iterate t Ψ) ≤ θ ^ t * (P.K S).expect Ψ := h1
      _ ≤ θ ^ t * (θ * Ψ S) := h2
      _ = θ ^ (t + 1) * Ψ S := by ring

/-- The phase reached by a state: the largest `j ≤ J` with at most `y j` uninformed nodes. -/
noncomputable def phaseOf (y : ℕ → ℝ) (J : ℕ) (T : Finset (Fin n)) : ℕ := by
  classical
  exact Nat.findGreatest (fun j => (n : ℝ) - T.card ≤ y j) J

lemma phaseOf_le (y : ℕ → ℝ) (J : ℕ) (T : Finset (Fin n)) : phaseOf y J T ≤ J := by
  classical
  unfold phaseOf
  convert Nat.findGreatest_le J

lemma phaseOf_spec {y : ℕ → ℝ} {J : ℕ} {T : Finset (Fin n)} (h0 : (n : ℝ) - T.card ≤ y 0) :
    (n : ℝ) - T.card ≤ y (phaseOf y J T) := by
  classical
  unfold phaseOf
  convert Nat.findGreatest_spec (P := fun j => (n : ℝ) - T.card ≤ y j) (Nat.zero_le J) h0

lemma le_phaseOf {y : ℕ → ℝ} {J j : ℕ} {T : Finset (Fin n)} (hj : j ≤ J)
    (h : (n : ℝ) - T.card ≤ y j) : j ≤ phaseOf y J T := by
  classical
  unfold phaseOf
  convert Nat.le_findGreatest (P := fun j => (n : ℝ) - T.card ≤ y j) hj h

/-- The phase potential: `0` once at most `y J` nodes are uninformed, `λ^{J - j}` in phase `j`
otherwise. -/
noncomputable def phasePot (y : ℕ → ℝ) (J : ℕ) (lam : ℝ) (T : Finset (Fin n)) : ℝ := by
  classical
  exact if (n : ℝ) - T.card ≤ y J then 0 else lam ^ (J - phaseOf y J T)

lemma phasePot_nonneg (y : ℕ → ℝ) (J : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (T : Finset (Fin n)) :
    0 ≤ phasePot y J lam T := by
  unfold phasePot
  split_ifs
  · exact le_rfl
  · exact pow_nonneg hlam _

lemma phasePot_le (y : ℕ → ℝ) (J : ℕ) {lam : ℝ} (hlam : 1 ≤ lam) (T : Finset (Fin n)) :
    phasePot y J lam T ≤ lam ^ J := by
  unfold phasePot
  split_ifs
  · exact pow_nonneg (by linarith) _
  · exact pow_le_pow_right₀ hlam (Nat.sub_le _ _)

lemma below_le_phasePot (y : ℕ → ℝ) (J : ℕ) {lam : ℝ} (hlam : 1 ≤ lam) (T : Finset (Fin n)) :
    below ((n : ℝ) - y J) T ≤ phasePot y J lam T := by
  unfold below phasePot
  by_cases h : (n : ℝ) - T.card ≤ y J
  · have : ¬ (T.card : ℝ) < (n : ℝ) - y J := by linarith
    simp [this, h]
  · have : (T.card : ℝ) < (n : ℝ) - y J := by linarith
    simp only [this, h, if_true, if_false]
    exact one_le_pow₀ hlam

lemma card_le_of_subset_real {S T : Finset (Fin n)} (h : S ⊆ T) : (S.card : ℝ) ≤ T.card :=
  Nat.cast_le.mpr (card_le_card h)

/-- One round of the phase potential. -/
lemma apply_phasePot_le (P : RumorProcess n) (y : ℕ → ℝ) (J : ℕ) {q lam : ℝ} (hlam : 1 ≤ lam)
    (hstep : ∀ j, j < J → ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ y j →
      (P.K S).prob (fun T => y (j + 1) < (n : ℝ) - T.card) ≤ q)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ y 0) :
    P.K.apply (phasePot y J lam) S ≤ (q + 1 / lam) * phasePot y J lam S := by
  classical
  have hlam0 : 0 < lam := by linarith
  by_cases hJ : (n : ℝ) - S.card ≤ y J
  · have hzero : ∀ T, S ⊆ T → phasePot y J lam T = 0 := by
      intro T hST
      have := card_le_of_subset_real hST
      have hT : (n : ℝ) - T.card ≤ y J := by linarith
      simp [phasePot, hT]
    rw [Kernel.apply, expect_eq_of_agree_on_superset P S (g := fun _ => 0) hzero,
      Distribution.expect_const]
    simp [phasePot, hJ]
  · set m := phaseOf y J S with hm
    have hmJ : m < J := by
      rcases lt_or_eq_of_le (phaseOf_le y J S) with h | h
      · exact h
      · exact absurd (h ▸ phaseOf_spec (J := J) hS) hJ
    have hSm : (n : ℝ) - S.card ≤ y m := phaseOf_spec hS
    have hpot : phasePot y J lam S = lam ^ (J - m) := by simp [phasePot, hJ, hm]
    have hsplit : J - m = (J - (m + 1)) + 1 := by omega
    -- pointwise bound on the next state
    have hpt : ∀ T, S ⊆ T → phasePot y J lam T ≤
        lam ^ (J - (m + 1)) + lam ^ (J - m) *
          (if y (m + 1) < (n : ℝ) - T.card then 1 else 0) := by
      intro T hST
      have hc := card_le_of_subset_real hST
      have hpow0 : 0 ≤ lam ^ (J - (m + 1)) := pow_nonneg hlam0.le _
      by_cases hTJ : (n : ℝ) - T.card ≤ y J
      · simp only [phasePot, hTJ, if_true]
        have : 0 ≤ lam ^ (J - m) * (if y (m + 1) < (n : ℝ) - T.card then (1 : ℝ) else 0) :=
          mul_nonneg (pow_nonneg hlam0.le _) (by split_ifs <;> norm_num)
        linarith
      · simp only [phasePot, hTJ, if_false]
        have hTm : m ≤ phaseOf y J T := le_phaseOf hmJ.le (by linarith)
        by_cases hfail : y (m + 1) < (n : ℝ) - T.card
        · rw [if_pos hfail, mul_one]
          have := pow_le_pow_right₀ hlam (Nat.sub_le_sub_left hTm J)
          linarith
        · rw [if_neg hfail, mul_zero, add_zero]
          have hTm1 : m + 1 ≤ phaseOf y J T := le_phaseOf hmJ (by linarith)
          exact pow_le_pow_right₀ hlam (Nat.sub_le_sub_left hTm1 J)
    have hE := expect_le_of_weight P S hpt
    rw [Distribution.expect_add, Distribution.expect_const, Distribution.expect_mul] at hE
    have hprob := hstep m hmJ S hSm
    rw [prob_indicator_eq (P.K S) (fun T => y (m + 1) < (n : ℝ) - T.card)
      (fun T => if y (m + 1) < (n : ℝ) - T.card then (1 : ℝ) else 0)
      (fun T h => by simp [h]) (fun T h => by simp [h])] at hprob
    rw [Kernel.apply, hpot]
    have hmul := mul_le_mul_of_nonneg_left hprob (pow_nonneg hlam0.le (J - m))
    have hid : lam ^ (J - (m + 1)) = 1 / lam * lam ^ (J - m) := by
      rw [hsplit, pow_succ]
      field_simp
    calc (P.K S).expect (phasePot y J lam)
        ≤ lam ^ (J - (m + 1)) + lam ^ (J - m) *
            (P.K S).expect (fun T => if y (m + 1) < (n : ℝ) - T.card then 1 else 0) := hE
      _ ≤ 1 / lam * lam ^ (J - m) + lam ^ (J - m) * q := by rw [hid]; linarith
      _ = (q + 1 / lam) * lam ^ (J - m) := by ring

/-- Phase calculus: from at most `y 0` uninformed nodes, more than `y J` remain after `t` rounds
with probability at most `(q + 1/λ)^t λ^J`. -/
lemma notYet_phase_le (P : RumorProcess n) (y : ℕ → ℝ) (J : ℕ) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 1 ≤ lam)
    (hstep : ∀ j, j < J → ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ y j →
      (P.K S).prob (fun T => y (j + 1) < (n : ℝ) - T.card) ≤ q)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ y 0) (t : ℕ) :
    P.notYet ((n : ℝ) - y J) t S ≤ (q + 1 / lam) ^ t * lam ^ J := by
  have hlam0 : 0 < lam := by linarith
  have hθ : 0 ≤ q + 1 / lam := by positivity
  have hR : ∀ S T : Finset (Fin n), (n : ℝ) - S.card ≤ y 0 → S ⊆ T →
      (n : ℝ) - T.card ≤ y 0 := by
    intro S T hS hST
    have := card_le_of_subset_real hST
    linarith
  have hit := iterate_le_pow_of_region P (fun T => (n : ℝ) - T.card ≤ y 0) hR
    (phasePot y J lam) hθ (fun T hT => apply_phasePot_le P y J hlam hstep T hT) t S hS
  rw [notYet_below]
  calc P.K.iterate t (below ((n : ℝ) - y J)) S ≤ P.K.iterate t (phasePot y J lam) S :=
        P.K.iterate_mono t (below_le_phasePot y J hlam) S
    _ ≤ (q + 1 / lam) ^ t * phasePot y J lam S := hit
    _ ≤ (q + 1 / lam) ^ t * lam ^ J :=
        mul_le_mul_of_nonneg_left (phasePot_le y J hlam S) (pow_nonneg hθ t)

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
  have hit := iterate_le_pow_of_region P (fun T => (n : ℝ) - T.card ≤ U) hR _ hθ happ t S hS
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
    refine prob_mono D (fun T hT => ?_)
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
