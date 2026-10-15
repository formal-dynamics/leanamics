import Epidemics.CobraDuality
import Dynamics.Spectral

/-! # Spectral quantities for the COBRA cover time (EPI-4)

Cooper, Radzik, Rivera, *The coalescing-branching random walk on expanders and the dual epidemic
process*, PODC 2016 (arXiv:1602.05768), Section 1 and the proof of Lemma 1 (Section 3).

For a connected `r`-regular graph `G` the random walk has transition matrix `P = A(G) / r`, with
eigenvalues `1 = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ ≥ -1`, and the paper's `λ = λ_max = max_{i ≥ 2} |λᵢ|`. Since
`λₙ ≤ λ₂`, this is `max {λ₂, |λₙ|}`: the core's `Dynamics.lambdaG`, built on
`Dynamics.transitionMatrix` and `Dynamics.walkEigenvalues` (`Dynamics/Spectral.lean`, shared with
the median package).

The spectral core of Lemma 1 is `‖P 1_A‖² ≤ λ² |A| + (1 - λ²) |A|² / n`, where
`(P 1_A)(x) = d_A(x) / r` and `d_A(x) = |N(x) ∩ A|` (`sum_sq_neighbor_le`).
-/

namespace Epidemics
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A positive-degree regular simple graph has at least two vertices. -/
lemma two_le_card_of_pos_regular {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    [Nonempty V] : 2 ≤ Fintype.card V := by
  obtain ⟨v⟩ : Nonempty V := inferInstance
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro u hu
    exact Finset.mem_erase.2
      ⟨(G.ne_of_adj ((G.mem_neighborFinset v u).mp hu)).symm, Finset.mem_univ u⟩
  have hle : (G.neighborFinset v).card ≤ Fintype.card V - 1 := by
    calc (G.neighborFinset v).card
        ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
      _ = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  rw [G.card_neighborFinset_eq_degree, hreg v] at hle
  omega

/-- Double counting: `∑_x d_A(x) = r |A|` on an `r`-regular graph. -/
lemma sum_neighborCard_eq {r : ℕ} (hreg : G.IsRegularOfDegree r) (A : Finset V) :
    ∑ x, (G.neighborFinset x ∩ A).card = r * A.card := by
  classical
  have hcard (x : V) :
      (G.neighborFinset x ∩ A).card = ∑ w ∈ A, if G.Adj x w then 1 else 0 := by
    rw [Finset.card_eq_sum_ite
      (Finset.inter_subset_right (s₁ := G.neighborFinset x) (s₂ := A))]
    refine Finset.sum_congr rfl fun w hw => ?_
    simp [Finset.mem_inter, hw, G.mem_neighborFinset]
  calc ∑ x, (G.neighborFinset x ∩ A).card
      = ∑ x, ∑ w ∈ A, if G.Adj x w then 1 else 0 := by
        exact Finset.sum_congr rfl fun x _ => hcard x
    _ = ∑ w ∈ A, ∑ x, if G.Adj w x then 1 else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
        simp [G.adj_comm]
    _ = ∑ w ∈ A, G.degree w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_boole, ← G.card_neighborFinset_eq_degree]
        apply congrArg Finset.card
        ext x
        simp [G.mem_neighborFinset]
    _ = ∑ _w ∈ A, r := by
        refine Finset.sum_congr rfl fun w _ => hreg w
    _ = r * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- `(P 1_A)(x) = d_A(x) / r`. -/
lemma transition_indVec_apply {r : ℕ} (A : Finset V) (x : V) :
    (transitionMatrix G r *ᵥ indVec A) x =
      ((G.neighborFinset x ∩ A).card : ℝ) / r := by
  rw [transitionMatrix, smul_mulVec, Pi.smul_apply, smul_eq_mul,
    SimpleGraph.adjMatrix_mulVec_apply, div_eq_inv_mul]
  congr 1
  classical
  simp only [indVec, Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- `‖P 1_A‖² = ∑_x (d_A(x) / r)²`. -/
lemma sum_sq_neighbor_eq_dotProduct {r : ℕ} (A : Finset V) :
    ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 =
      (transitionMatrix G r *ᵥ indVec A) ⬝ᵥ (transitionMatrix G r *ᵥ indVec A) := by
  simp only [dotProduct, sq, transition_indVec_apply A]

/-- If `λ < 1`, expand `1_A` in the eigenbasis of `P`: the top eigenvalue is `1` with squared
coefficient `|A|² / n`, and every other eigenvalue has square at most `λ²`. -/
lemma norm_sq_indVec_le_of_lambda_lt {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    (hL : lambdaG G r < 1) (A : Finset V) :
    (transitionMatrix G r *ᵥ indVec A) ⬝ᵥ (transitionMatrix G r *ᵥ indVec A) ≤
      lambdaG G r ^ 2 * A.card +
        (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
  rcases isEmpty_or_nonempty V with hV | hV
  · haveI := hV
    have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
    simp [hA, dotProduct, lambdaG, Fintype.card_eq_zero]
  obtain ⟨k₀, hμ0, hsmall, htop⟩ := exists_top_eigenvectorBasis G hr hreg hL
  have hP := transitionMatrix_isHermitian G r
  set P := transitionMatrix G r
  set b : V → V → ℝ := fun k => ⇑(hP.eigenvectorBasis k)
  set μ : V → ℝ := hP.eigenvalues
  set s : V → ℝ := fun k => b k ⬝ᵥ indVec A
  have hS2 : ∑ k, s k ^ 2 = A.card := by
    have h := dotProduct_eq_sum_eigenvectorBasis hP (indVec A) (indVec A)
    rw [indVec_dotProduct_self] at h
    rw [h]
    simp only [s, sq]
    rfl
  have hs0 : s k₀ ^ 2 = (A.card : ℝ) ^ 2 / Fintype.card V := by
    have h := htop (indVec A) (indVec A)
    rw [sum_indVec, ← sq, ← sq] at h
    exact h
  have hnorm : (P *ᵥ indVec A) ⬝ᵥ (P *ᵥ indVec A) = ∑ k, μ k ^ 2 * s k ^ 2 := by
    rw [dotProduct_eq_sum_eigenvectorBasis hP]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eigenvectorBasis_dotProduct_mulVec hP]
    ring
  have hrest : ∑ k ∈ Finset.univ.erase k₀, μ k ^ 2 * s k ^ 2 ≤
      lambdaG G r ^ 2 * (A.card - s k₀ ^ 2) := by
    have hsum : ∑ k ∈ Finset.univ.erase k₀, s k ^ 2 = A.card - s k₀ ^ 2 := by
      have h := Finset.sum_erase_add Finset.univ (fun k => s k ^ 2) (Finset.mem_univ k₀)
      rw [hS2] at h
      linarith
    calc ∑ k ∈ Finset.univ.erase k₀, μ k ^ 2 * s k ^ 2
        ≤ ∑ k ∈ Finset.univ.erase k₀, lambdaG G r ^ 2 * s k ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact mul_le_mul_of_nonneg_right (by
            have habs := hsmall k (Finset.ne_of_mem_erase hk)
            have : |μ k| ^ 2 ≤ lambdaG G r ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) habs 2
            simpa [sq_abs] using this) (sq_nonneg _)
      _ = lambdaG G r ^ 2 * ∑ k ∈ Finset.univ.erase k₀, s k ^ 2 := by
          rw [Finset.mul_sum]
      _ = lambdaG G r ^ 2 * (A.card - s k₀ ^ 2) := by rw [hsum]
  have hsplit :=
    Finset.sum_erase_add Finset.univ (fun k => μ k ^ 2 * s k ^ 2) (Finset.mem_univ k₀)
  have hμ0' : μ k₀ = 1 := hμ0
  rw [hnorm, ← hsplit, hμ0']
  have htop : (1 : ℝ) ^ 2 * s k₀ ^ 2 = (A.card : ℝ) ^ 2 / Fintype.card V := by
    simp [hs0]
  calc ∑ k ∈ Finset.univ.erase k₀, μ k ^ 2 * s k ^ 2 + (1 : ℝ) ^ 2 * s k₀ ^ 2
      ≤ lambdaG G r ^ 2 * (A.card - s k₀ ^ 2) + (A.card : ℝ) ^ 2 / Fintype.card V := by
        linarith [hrest, htop]
    _ = lambdaG G r ^ 2 * A.card + (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
        rw [hs0]
        field_simp
        ring

/-- **Spectral core of Lemma 1** (Section 3, inequality (7)): on an `r`-regular graph with
`r > 0`, for every set `A`,
`∑ₓ P(x, A)² = ‖P 1_A‖² ≤ λ² |A| + (1 - λ²) |A|² / n`, where `P(x, A) = d_A(x) / r`.
Proof idea: expand `1_A` in an orthonormal eigenbasis of `P`; the top eigenvector is the constant
vector `1/√n` (coefficient `|A| / √n`) and every other eigenvalue has square `≤ λ²`. If `λ ≥ 1`
the bound follows from `P(x, A) ≤ 1` and `∑ₓ P(x, A) = |A|`. -/
theorem sum_sq_neighbor_le {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    (A : Finset V) :
    ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 ≤
      lambdaG G r ^ 2 * A.card + (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
  rw [sum_sq_neighbor_eq_dotProduct]
  by_cases hL : lambdaG G r < 1
  · exact norm_sq_indVec_le_of_lambda_lt hreg hr hL A
  · push Not at hL
    rcases isEmpty_or_nonempty V with hV | hV
    · haveI := hV
      have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
      simp [hA, dotProduct, lambdaG, Fintype.card_eq_zero]
    · have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
      have hfrac (x : V) :
          0 ≤ ((G.neighborFinset x ∩ A).card : ℝ) / r ∧
            ((G.neighborFinset x ∩ A).card : ℝ) / r ≤ 1 := by
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
        have hle : (G.neighborFinset x ∩ A).card ≤ r := by
          rw [← hreg x, ← G.card_neighborFinset_eq_degree]
          exact Finset.card_le_card Finset.inter_subset_left
        constructor
        · positivity
        · rw [div_le_one hr0]
          exact_mod_cast hle
      have hsq : ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 ≤
          ∑ x, ((G.neighborFinset x ∩ A).card : ℝ) / r := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h0 := (hfrac x).1
        have h1 := (hfrac x).2
        rw [sq]
        exact mul_le_of_le_one_left h0 h1
      have hsum : ∑ x, ((G.neighborFinset x ∩ A).card : ℝ) / r = A.card := by
        rw [← Finset.sum_div, ← Nat.cast_sum, sum_neighborCard_eq hreg, Nat.cast_mul,
          mul_div_cancel_left₀]
        exact_mod_cast hr.ne'
      have hcard : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ A
      have hgap : 0 ≤ (A.card : ℝ) - A.card ^ 2 / Fintype.card V := by
        rw [sub_nonneg, div_le_iff₀ hn]
        nlinarith [sq_nonneg ((A.card : ℝ) - Fintype.card V)]
      have hlam2 : 1 ≤ lambdaG G r ^ 2 := by nlinarith [sq_nonneg (lambdaG G r)]
      have hRHS : (A.card : ℝ) ≤ lambdaG G r ^ 2 * A.card +
          (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
        have hkey : lambdaG G r ^ 2 * (A.card : ℝ) +
            (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V - A.card =
            (lambdaG G r ^ 2 - 1) * (A.card - A.card ^ 2 / Fintype.card V) := by
          field_simp
          ring
        have hnn : 0 ≤ (lambdaG G r ^ 2 - 1) * (A.card - A.card ^ 2 / Fintype.card V) :=
          mul_nonneg (by linarith) hgap
        linarith
      calc (transitionMatrix G r *ᵥ indVec A) ⬝ᵥ (transitionMatrix G r *ᵥ indVec A)
          = ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 :=
            (sum_sq_neighbor_eq_dotProduct A).symm
        _ ≤ ∑ x, ((G.neighborFinset x ∩ A).card : ℝ) / r := hsq
        _ = A.card := hsum
        _ ≤ _ := hRHS

end Epidemics
