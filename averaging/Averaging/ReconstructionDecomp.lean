import Averaging.ReconstructionSpectral
import Averaging.ReconstructionMatrix

/-! # Lemma C.1: `x⁽ᵗ⁾ = α₁ 𝟙 + α₂ λ₂ᵗ χ + e⁽ᵗ⁾` with `‖e⁽ᵗ⁾‖_∞ ≤ λᵗ √(2n)`

Lemma C.1 of Becchetti et al. (arXiv:1511.03927). The vectors `𝟙` and `χ` are orthogonal
eigenvectors of `P` with eigenvalues `1` and `λ₂ = 1 - 2b/d`, both larger than `λ`; since at most
two eigenvalues of `P` exceed `λ` in absolute value, `P` contracts the orthogonal complement of
`span {𝟙, χ}` by `λ` (`pow_mulVec_dotProduct_self_le_of_orthogonal`). The error
`e⁽ᵗ⁾ = Pᵗ (x - α₁ 𝟙 - α₂ χ)` then has `‖e⁽ᵗ⁾‖_∞ ≤ ‖e⁽ᵗ⁾‖₂ ≤ λᵗ ‖x‖₂ = λᵗ √(2n)`.
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {V₁ V₂ : Finset V} {n d b : ℕ}

/-- `P` contracts vectors orthogonal to `𝟙` and `χ` by `λ`: `‖Pᵗ y‖² ≤ λ²ᵗ ‖y‖²`. -/
lemma transitionMatrix_pow_mulVec_dotProduct_self_le (hG : IsClusteredRegular G V₁ V₂ n d b)
    (hd : 0 < d) (hn : 0 < n) (hlam : maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d)
    {y : V → ℝ} (hy₁ : (1 : V → ℝ) ⬝ᵥ y = 0) (hy₂ : clusterIndicator V₁ V₂ ⬝ᵥ y = 0) (t : ℕ) :
    ((transitionMatrix G d ^ t) *ᵥ y) ⬝ᵥ ((transitionMatrix G d ^ t) *ᵥ y) ≤
      (maxAbsOtherEigenvalue G d ^ t) ^ 2 * (y ⬝ᵥ y) := by
  have hP := hG.toIsBalancedPartition
  have hμ1 : 1 - 2 * (b : ℝ) / d ≤ 1 := by
    have : 0 ≤ 2 * (b : ℝ) / d := by positivity
    linarith
  exact pow_mulVec_dotProduct_self_le_of_orthogonal (transitionMatrix_isHermitian G d)
    (hK := card_filter_lt_abs_eigenvalues_le_two _
      (abs_eigenvalues₀_le_maxAbsOtherEigenvalue G d))
    (c₁ := 1) (c₂ := 1 - 2 * (b : ℝ) / d)
    (hc₁ := by rw [abs_one]; linarith) (hc₂ := lt_of_lt_of_le hlam (le_abs_self _))
    (hu₁ := by rw [one_smul]; exact transitionMatrix_mulVec_one hG.regular hd)
    (hu₂ := transitionMatrix_mulVec_clusterIndicator_aux hG hd)
    (m := 2 * n) (hm := by positivity) (h₁ := hP.one_dotProduct_one)
    (h₂ := hP.clusterIndicator_dotProduct_self) (h₁₂ := hP.one_dotProduct_clusterIndicator)
    (hy₁ := hy₁) (hy₂ := hy₂) t

/-- **Lemma C.1** (with explicit `α₁ = ⟨x, 𝟙⟩ / 2n`, `α₂ = ⟨x, χ⟩ / 2n`). -/
theorem abs_avgIter_sub_le_aux (hG : IsClusteredRegular G V₁ V₂ n d b) (hd : 0 < d)
    (hlam : maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (t : ℕ) (v : V) :
    |avgIter G t x v - ((∑ u, x u) / (2 * n) +
        (x ⬝ᵥ clusterIndicator V₁ V₂) / (2 * n) * (1 - 2 * (b : ℝ) / d) ^ t *
          clusterIndicator V₁ V₂ v)| ≤
      maxAbsOtherEigenvalue G d ^ t * √(2 * n) := by
  have hP := hG.toIsBalancedPartition
  have hn : 0 < n := by
    have h1 := hP.card_eq
    have h2 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  have hm : (2 * n : ℝ) ≠ 0 := by positivity
  have hlam0 := maxAbsOtherEigenvalue_nonneg G d
  set χ := clusterIndicator V₁ V₂ with hχ
  set P := transitionMatrix G d with hPdef
  set μ := 1 - 2 * (b : ℝ) / d with hμ
  set lam := maxAbsOtherEigenvalue G d with hlamdef
  set α₁ := (x ⬝ᵥ 1) / (2 * n) with hα₁
  set α₂ := (x ⬝ᵥ χ) / (2 * n) with hα₂
  set y := x - α₁ • (1 : V → ℝ) - α₂ • χ with hy
  have hy₁ : (1 : V → ℝ) ⬝ᵥ y = 0 := by
    rw [dotProduct_comm]
    exact residual_dotProduct_left hm hP.one_dotProduct_one hP.one_dotProduct_clusterIndicator x
  have hy₂ : χ ⬝ᵥ y = 0 := by
    rw [dotProduct_comm]
    exact residual_dotProduct_right hm hP.clusterIndicator_dotProduct_self
      hP.one_dotProduct_clusterIndicator x
  have hyy : y ⬝ᵥ y ≤ 2 * n := by
    rw [hy, residual_dotProduct_self hm hP.one_dotProduct_one hP.clusterIndicator_dotProduct_self
      hP.one_dotProduct_clusterIndicator x, hP.dotProduct_self_of_sign hx]
    have : 0 ≤ ((x ⬝ᵥ 1) ^ 2 + (x ⬝ᵥ χ) ^ 2) / (2 * n) := by positivity
    linarith
  have hP1 : P *ᵥ (1 : V → ℝ) = (1 : ℝ) • (1 : V → ℝ) := by
    rw [one_smul]; exact transitionMatrix_mulVec_one hG.regular hd
  have hPt : (P ^ t) *ᵥ x = (P ^ t) *ᵥ y + α₁ • (1 : V → ℝ) + (α₂ * μ ^ t) • χ := by
    have hx_eq : x = y + α₁ • (1 : V → ℝ) + α₂ • χ := by
      rw [hy]; abel
    conv_lhs => rw [hx_eq]
    rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, pow_mulVec_of_mulVec_eq_smul hP1 t,
      pow_mulVec_of_mulVec_eq_smul (transitionMatrix_mulVec_clusterIndicator_aux hG hd) t,
      one_pow, one_smul, smul_smul, mul_comm α₂]
  have key : avgIter G t x v - ((∑ u, x u) / (2 * n) + α₂ * μ ^ t * χ v) =
      ((P ^ t) *ᵥ y) v := by
    rw [avgIter_eq_pow_mulVec hG.regular, ← hPdef, hPt, ← dotProduct_one, ← hα₁]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
    ring
  rw [key]
  set z := (P ^ t) *ᵥ y with hz
  have hzz : z ⬝ᵥ z ≤ (lam ^ t) ^ 2 * (2 * n) :=
    (transitionMatrix_pow_mulVec_dotProduct_self_le hG hd hn hlam hy₁ hy₂ t).trans
      (mul_le_mul_of_nonneg_left hyy (by positivity))
  have hzv : z v ^ 2 ≤ z ⬝ᵥ z := by
    rw [dotProduct, sq]
    exact single_le_sum (fun u _ => mul_self_nonneg (z u)) (mem_univ v)
  calc |z v| ≤ √((lam ^ t) ^ 2 * (2 * n)) := Real.abs_le_sqrt (hzv.trans hzz)
    _ = lam ^ t * √(2 * n) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (pow_nonneg hlam0 t)]

end Averaging
