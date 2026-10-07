import Averaging.ReconstructionDefs

/-! # Clustered regular graphs: partition and transition-matrix facts

Elementary facts behind Section 3 of Becchetti et al. (arXiv:1511.03927): the partition identities
`⟨𝟙, 𝟙⟩ = ⟨χ, χ⟩ = 2n`, `⟨𝟙, χ⟩ = 0`, the matrix form `x⁽ᵗ⁾ = Pᵗ x` of the averaging dynamics,
`P 𝟙 = 𝟙`, Observation A.3 (`P χ = (1 - 2b/d) χ`) and its powers, and basic properties of `λ`.
-/

namespace Averaging
open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The balanced partition -/

namespace IsBalancedPartition

variable {V₁ V₂ : Finset V} {n : ℕ} (h : IsBalancedPartition V₁ V₂ n)
include h

lemma card_eq : Fintype.card V = 2 * n := by
  rw [← card_univ, ← h.union_eq_univ, card_union_of_disjoint h.disjoint, h.card_left,
    h.card_right]
  ring

lemma mem_or (v : V) : v ∈ V₁ ∨ v ∈ V₂ :=
  mem_union.mp (h.union_eq_univ ▸ mem_univ v)

lemma clusterIndicator_of_mem_left {v : V} (hv : v ∈ V₁) : clusterIndicator V₁ V₂ v = 1 := by
  simp [clusterIndicator, hv, disjoint_left.mp h.disjoint hv]

lemma clusterIndicator_of_mem_right {v : V} (hv : v ∈ V₂) : clusterIndicator V₁ V₂ v = -1 := by
  simp [clusterIndicator, hv, disjoint_right.mp h.disjoint hv]

lemma clusterIndicator_eq_one_or (v : V) :
    clusterIndicator V₁ V₂ v = 1 ∨ clusterIndicator V₁ V₂ v = -1 := by
  rcases h.mem_or v with hv | hv
  · exact Or.inl (h.clusterIndicator_of_mem_left hv)
  · exact Or.inr (h.clusterIndicator_of_mem_right hv)

lemma card_inter_add (s : Finset V) : (s ∩ V₁).card + (s ∩ V₂).card = s.card := by
  rw [← card_union_of_disjoint (h.disjoint.mono inter_subset_right inter_subset_right),
    ← inter_union_distrib_left, h.union_eq_univ, inter_univ]

omit h [Fintype V] in
lemma sum_clusterIndicator (s : Finset V) :
    ∑ u ∈ s, clusterIndicator V₁ V₂ u = ((s ∩ V₁).card : ℝ) - (s ∩ V₂).card := by
  simp [clusterIndicator, sum_sub_distrib]

lemma one_dotProduct_one : (1 : V → ℝ) ⬝ᵥ 1 = 2 * n := by
  simp [dotProduct, h.card_eq]

lemma one_dotProduct_clusterIndicator : (1 : V → ℝ) ⬝ᵥ clusterIndicator V₁ V₂ = 0 := by
  rw [one_dotProduct, sum_clusterIndicator, univ_inter, univ_inter, h.card_left, h.card_right,
    sub_self]

lemma clusterIndicator_dotProduct_self :
    clusterIndicator V₁ V₂ ⬝ᵥ clusterIndicator V₁ V₂ = 2 * n := by
  have hsq (v : V) : clusterIndicator V₁ V₂ v * clusterIndicator V₁ V₂ v = 1 := by
    rcases h.clusterIndicator_eq_one_or v with hv | hv <;> rw [hv] <;> norm_num
  simp [dotProduct, hsq, h.card_eq]

/-- A vector of signs has squared norm `2n`. -/
lemma dotProduct_self_of_sign {x : V → ℝ} (hx : ∀ v, x v = 1 ∨ x v = -1) : x ⬝ᵥ x = 2 * n := by
  have hsq (v : V) : x v * x v = 1 := by
    rcases hx v with hv | hv <;> rw [hv] <;> norm_num
  simp [dotProduct, hsq, h.card_eq]

end IsBalancedPartition

/-! ### The transition matrix -/

variable {G : SimpleGraph V} [DecidableRel G.Adj] {V₁ V₂ : Finset V} {n d b : ℕ}

omit [DecidableEq V] in
lemma avgStep_eq_transitionMatrix_mulVec (hreg : G.IsRegularOfDegree d) (x : V → ℝ) :
    avgStep G x = transitionMatrix G d *ᵥ x := by
  ext v
  rw [avgStep, transitionMatrix, smul_mulVec, Pi.smul_apply, adjMatrix_mulVec_apply, hreg v,
    smul_eq_mul, div_eq_inv_mul]

/-- `x⁽ᵗ⁾ = Pᵗ x` (Section 2). -/
lemma avgIter_eq_pow_mulVec (hreg : G.IsRegularOfDegree d) (t : ℕ) (x : V → ℝ) :
    avgIter G t x = (transitionMatrix G d ^ t) *ᵥ x := by
  induction t with
  | zero => simp [avgIter]
  | succ t ih =>
    rw [show avgIter G (t + 1) x = avgStep G (avgIter G t x) from rfl, ih,
      avgStep_eq_transitionMatrix_mulVec hreg, mulVec_mulVec, ← pow_succ']

omit [DecidableEq V] in
/-- `P 𝟙 = 𝟙`: the transition matrix is stochastic. -/
lemma transitionMatrix_mulVec_one (hreg : G.IsRegularOfDegree d) (hd : 0 < d) :
    transitionMatrix G d *ᵥ 1 = 1 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  ext v
  rw [transitionMatrix, smul_mulVec, Pi.smul_apply, adjMatrix_mulVec_apply]
  simp only [Pi.one_apply, sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  rw [hreg v]
  exact inv_mul_cancel₀ hdR

/-- **Observation A.3**: `P χ = (1 - 2b/d) χ`. -/
lemma transitionMatrix_mulVec_clusterIndicator_aux (hG : IsClusteredRegular G V₁ V₂ n d b)
    (hd : 0 < d) :
    transitionMatrix G d *ᵥ clusterIndicator V₁ V₂ =
      (1 - 2 * (b : ℝ) / d) • clusterIndicator V₁ V₂ := by
  have hP := hG.toIsBalancedPartition
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  ext v
  rw [transitionMatrix, smul_mulVec, Pi.smul_apply, adjMatrix_mulVec_apply,
    IsBalancedPartition.sum_clusterIndicator, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  have hsum := hP.card_inter_add (G.neighborFinset v)
  rw [card_neighborFinset_eq_degree, hG.regular v] at hsum
  have hsumR : ((G.neighborFinset v ∩ V₁).card : ℝ) + (G.neighborFinset v ∩ V₂).card = d := by
    exact_mod_cast hsum
  rcases hP.mem_or v with hv | hv
  · rw [hP.clusterIndicator_of_mem_left hv]
    have hb : ((G.neighborFinset v ∩ V₂).card : ℝ) = b := by exact_mod_cast hG.cross_left v hv
    field_simp
    linarith
  · rw [hP.clusterIndicator_of_mem_right hv]
    have hb : ((G.neighborFinset v ∩ V₁).card : ℝ) = b := by exact_mod_cast hG.cross_right v hv
    field_simp
    linarith

lemma pow_mulVec_of_mulVec_eq_smul {M : Matrix V V ℝ} {u : V → ℝ} {c : ℝ}
    (hu : M *ᵥ u = c • u) (t : ℕ) : (M ^ t) *ᵥ u = c ^ t • u := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hu, smul_smul, pow_succ]

/-! ### The parameter `λ` -/

lemma maxAbsOtherEigenvalue_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    0 ≤ maxAbsOtherEigenvalue G d :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- `λ` bounds `|λᵢ|` for every `i ≥ 3` (0-based index `≥ 2`) of the sorted spectrum. -/
lemma abs_eigenvalues₀_le_maxAbsOtherEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (i : Fin (Fintype.card V)) (hi : 2 ≤ i.val) :
    |(transitionMatrix_isHermitian G d).eigenvalues₀ i| ≤ maxAbsOtherEigenvalue G d :=
  le_ciSup (f := fun j : {j : Fin (Fintype.card V) // 2 ≤ j.val} =>
    |(transitionMatrix_isHermitian G d).eigenvalues₀ j.1|) (Set.finite_range _).bddAbove ⟨i, hi⟩

end Averaging
