import Averaging.ReconstructionDefs

/-! # Contraction off two eigenvectors of a real symmetric matrix

The linear-algebra inputs of Lemma C.1 of Becchetti et al. (arXiv:1511.03927), on top of the
plain-vector eigenbasis API of `Dynamics/Spectral.lean` (orthonormality, Parseval, the spectral
bound `‖Aᵗ y‖² ≤ λ²ᵗ ‖y‖²` for vectors `y` without components along eigenvectors whose eigenvalue
exceeds `λ` in absolute value): at most two eigenvalues exceed a bound on the rest of the sorted
spectrum, Bessel's inequality for the projection on the span of two orthogonal vectors of equal
norm, and the resulting contraction off two eigenvectors.
-/

namespace Averaging
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian)

/-- At most two eigenvalues exceed in absolute value a bound on all but the two largest ones of
the decreasingly sorted spectrum `eigenvalues₀`. -/
lemma card_filter_lt_abs_eigenvalues_le_two {lam : ℝ}
    (hlam : ∀ i : Fin (Fintype.card V), 2 ≤ i.val → |hA.eigenvalues₀ i| ≤ lam) :
    (univ.filter fun j => lam < |hA.eigenvalues j|).card ≤ 2 := by
  let e : V → Fin (Fintype.card V) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have he : Function.Injective e := Equiv.injective _
  have hmaps : ∀ j ∈ univ.filter (fun j => lam < |hA.eigenvalues j|),
      (e j).val ∈ range 2 := by
    intro j hj
    rw [mem_filter] at hj
    rw [mem_range]
    by_contra h
    exact absurd (hlam (e j) (not_lt.mp h)) (not_le.mpr hj.2)
  calc (univ.filter fun j => lam < |hA.eigenvalues j|).card ≤ (range 2).card :=
        card_le_card_of_injOn (fun j => (e j).val) hmaps
          (fun a _ b _ hab => he (Fin.ext hab))
    _ = 2 := card_range 2

/-! ### Projection on the span of two orthogonal vectors of equal norm -/

section Projection

omit [DecidableEq V]

variable {u₁ u₂ : V → ℝ} {m : ℝ}

lemma residual_dotProduct_left (hm : m ≠ 0) (h₁ : u₁ ⬝ᵥ u₁ = m) (h₁₂ : u₁ ⬝ᵥ u₂ = 0)
    (w : V → ℝ) : (w - ((w ⬝ᵥ u₁) / m) • u₁ - ((w ⬝ᵥ u₂) / m) • u₂) ⬝ᵥ u₁ = 0 := by
  rw [sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, h₁, dotProduct_comm u₂,
    h₁₂, smul_eq_mul, smul_eq_mul, div_mul_cancel₀ _ hm]
  ring

lemma residual_dotProduct_right (hm : m ≠ 0) (h₂ : u₂ ⬝ᵥ u₂ = m) (h₁₂ : u₁ ⬝ᵥ u₂ = 0)
    (w : V → ℝ) : (w - ((w ⬝ᵥ u₁) / m) • u₁ - ((w ⬝ᵥ u₂) / m) • u₂) ⬝ᵥ u₂ = 0 := by
  rw [sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, h₂, h₁₂, smul_eq_mul,
    smul_eq_mul, div_mul_cancel₀ _ hm]
  ring

lemma residual_dotProduct_self (hm : m ≠ 0) (h₁ : u₁ ⬝ᵥ u₁ = m) (h₂ : u₂ ⬝ᵥ u₂ = m)
    (h₁₂ : u₁ ⬝ᵥ u₂ = 0) (w : V → ℝ) :
    (w - ((w ⬝ᵥ u₁) / m) • u₁ - ((w ⬝ᵥ u₂) / m) • u₂) ⬝ᵥ
        (w - ((w ⬝ᵥ u₁) / m) • u₁ - ((w ⬝ᵥ u₂) / m) • u₂) =
      w ⬝ᵥ w - ((w ⬝ᵥ u₁) ^ 2 + (w ⬝ᵥ u₂) ^ 2) / m := by
  conv_lhs => rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
    residual_dotProduct_left hm h₁ h₁₂, residual_dotProduct_right hm h₂ h₁₂]
  rw [sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm u₁,
    dotProduct_comm u₂]
  simp only [smul_eq_mul]
  ring

/-- A unit vector has squared projection on `span {u₁, u₂}` at most `1` (Bessel). -/
lemma sq_add_sq_le (hm : 0 < m) (h₁ : u₁ ⬝ᵥ u₁ = m) (h₂ : u₂ ⬝ᵥ u₂ = m) (h₁₂ : u₁ ⬝ᵥ u₂ = 0)
    {w : V → ℝ} (hw : w ⬝ᵥ w = 1) : (w ⬝ᵥ u₁) ^ 2 + (w ⬝ᵥ u₂) ^ 2 ≤ m := by
  have h := residual_dotProduct_self hm.ne' h₁ h₂ h₁₂ w
  have h0 := dotProduct_self_star_nonneg
    (w - ((w ⬝ᵥ u₁) / m) • u₁ - ((w ⬝ᵥ u₂) / m) • u₂)
  simp only [star_trivial] at h0
  rw [h, hw, sub_nonneg, div_le_one hm] at h0
  exact h0

/-- Equality in Bessel's inequality: then `w ∈ span {u₁, u₂}`, so `w ⊥ y` whenever
`y ⊥ u₁, u₂`. -/
lemma dotProduct_eq_zero_of_sq_add_sq_eq (hm : 0 < m) (h₁ : u₁ ⬝ᵥ u₁ = m)
    (h₂ : u₂ ⬝ᵥ u₂ = m) (h₁₂ : u₁ ⬝ᵥ u₂ = 0) {w : V → ℝ} (hw : w ⬝ᵥ w = 1)
    (heq : (w ⬝ᵥ u₁) ^ 2 + (w ⬝ᵥ u₂) ^ 2 = m) {y : V → ℝ} (hy₁ : u₁ ⬝ᵥ y = 0)
    (hy₂ : u₂ ⬝ᵥ y = 0) : w ⬝ᵥ y = 0 := by
  have h := residual_dotProduct_self hm.ne' h₁ h₂ h₁₂ w
  rw [hw, heq, div_self hm.ne', sub_self] at h
  have hr := dotProduct_self_eq_zero.mp h
  have hy := congrArg (· ⬝ᵥ y) hr
  simp only [sub_dotProduct, smul_dotProduct, hy₁, hy₂, smul_eq_mul, mul_zero, sub_zero,
    zero_dotProduct] at hy
  exact hy

end Projection

/-- Contraction off two eigenvectors. Let `u₁, u₂` be orthogonal eigenvectors of `A` of equal
squared norm `m > 0`, with eigenvalues `c₁, c₂` exceeding `λ` in absolute value, and assume that at
most two eigenvalues of `A` exceed `λ` in absolute value. Then `‖Aᵗ y‖² ≤ λ²ᵗ ‖y‖²` for every `y`
orthogonal to `u₁` and `u₂`. -/
theorem pow_mulVec_dotProduct_self_le_of_orthogonal {lam c₁ c₂ m : ℝ} {u₁ u₂ : V → ℝ}
    (hK : (univ.filter fun j => lam < |hA.eigenvalues j|).card ≤ 2)
    (hc₁ : lam < |c₁|) (hc₂ : lam < |c₂|) (hu₁ : A *ᵥ u₁ = c₁ • u₁) (hu₂ : A *ᵥ u₂ = c₂ • u₂)
    (hm : 0 < m) (h₁ : u₁ ⬝ᵥ u₁ = m) (h₂ : u₂ ⬝ᵥ u₂ = m) (h₁₂ : u₁ ⬝ᵥ u₂ = 0)
    {y : V → ℝ} (hy₁ : u₁ ⬝ᵥ y = 0) (hy₂ : u₂ ⬝ᵥ y = 0) (t : ℕ) :
    ((A ^ t) *ᵥ y) ⬝ᵥ ((A ^ t) *ᵥ y) ≤ (lam ^ t) ^ 2 * (y ⬝ᵥ y) := by
  set K := univ.filter fun j => lam < |hA.eigenvalues j| with hKdef
  set a : V → ℝ := fun j => ⇑(hA.eigenvectorBasis j) ⬝ᵥ u₁
  set c : V → ℝ := fun j => ⇑(hA.eigenvectorBasis j) ⬝ᵥ u₂
  have hw (j : V) : ⇑(hA.eigenvectorBasis j) ⬝ᵥ ⇑(hA.eigenvectorBasis j) = 1 := by
    simp [eigenvectorBasis_dotProduct]
  -- outside `K`, the eigenvalue differs from `c₁` and `c₂`
  have hoff (j : V) (hj : j ∉ K) : a j = 0 ∧ c j = 0 := by
    have hj' : |hA.eigenvalues j| ≤ lam := by simpa [hKdef] using hj
    refine ⟨eigenvectorBasis_dotProduct_eq_zero_of_mulVec_eq_smul hA hu₁ fun h => ?_,
      eigenvectorBasis_dotProduct_eq_zero_of_mulVec_eq_smul hA hu₂ fun h => ?_⟩
    · rw [h] at hj'; linarith
    · rw [h] at hj'; linarith
  have hbessel (j : V) : a j ^ 2 + c j ^ 2 ≤ m := sq_add_sq_le hm h₁ h₂ h₁₂ (hw j)
  have hsum : ∑ j ∈ K, (a j ^ 2 + c j ^ 2) = 2 * m := by
    rw [sum_filter_of_ne fun j _ hne => ?_]
    · rw [sum_add_distrib]
      have e₁ := (dotProduct_eq_sum_eigenvectorBasis hA u₁ u₁).symm
      have e₂ := (dotProduct_eq_sum_eigenvectorBasis hA u₂ u₂).symm
      simp only [← sq] at e₁ e₂
      simp only [a, c, e₁, e₂, h₁, h₂]
      ring
    · by_contra hjK
      have hjK' : j ∉ K := by simpa [hKdef] using hjK
      obtain ⟨ha, hc⟩ := hoff j hjK'
      exact hne (by rw [ha, hc]; ring)
  have hzero : ∀ j ∈ K, m - (a j ^ 2 + c j ^ 2) = 0 := by
    refine (sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.mpr (hbessel j)).mp ?_
    refine le_antisymm ?_ (sum_nonneg fun j _ => sub_nonneg.mpr (hbessel j))
    rw [sum_sub_distrib, hsum, sum_const, nsmul_eq_mul]
    have hK' : (K.card : ℝ) ≤ 2 := by exact_mod_cast hK
    nlinarith
  refine pow_mulVec_dotProduct_self_le hA (fun j hj => ?_) t
  have hjK : j ∈ K := by simpa [hKdef] using hj
  exact dotProduct_eq_zero_of_sq_add_sq_eq hm h₁ h₂ h₁₂ (hw j)
    (by linarith [hzero j hjK]) hy₁ hy₂

end Averaging
