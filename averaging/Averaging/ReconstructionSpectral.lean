import Averaging.ReconstructionDefs

/-! # Spectral facts for real symmetric matrices, on plain vectors

For a real symmetric matrix `A` on `V`, Mathlib's orthonormal eigenbasis
`Matrix.IsHermitian.eigenvectorBasis` lives in `EuclideanSpace ℝ V`. Here its vectors are read as
plain functions `V → ℝ` with the dot product `⬝ᵥ`: orthonormality, the expansion of a vector in
the basis, Parseval's identity, and the contraction bound `‖Aᵗ y‖² ≤ λ²ᵗ ‖y‖²` for vectors `y`
without components along eigenvectors whose eigenvalue exceeds `λ` in absolute value. These are
the linear-algebra inputs of Lemma C.1 of Becchetti et al. (arXiv:1511.03927).
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian)

/-- The `j`-th vector of the orthonormal eigenbasis of `A`, as a plain function. -/
noncomputable def eigvec (j : V) : V → ℝ := ⇑(hA.eigenvectorBasis j)

lemma eigvec_dotProduct_eigvec (i j : V) :
    eigvec hA i ⬝ᵥ eigvec hA j = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  rw [← h]
  simp [eigvec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma mulVec_eigvec (j : V) : A *ᵥ eigvec hA j = hA.eigenvalues j • eigvec hA j :=
  hA.mulVec_eigenvectorBasis j

/-- Expansion of a vector in the orthonormal eigenbasis. -/
lemma sum_dotProduct_smul_eigvec (u : V → ℝ) :
    ∑ j, (eigvec hA j ⬝ᵥ u) • eigvec hA j = u := by
  have h := congrArg WithLp.ofLp (hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 u))
  simpa [eigvec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h

/-- Parseval's identity in the eigenbasis. -/
lemma sum_dotProduct_mul_dotProduct (u v : V → ℝ) :
    ∑ j, (eigvec hA j ⬝ᵥ u) * (eigvec hA j ⬝ᵥ v) = u ⬝ᵥ v := by
  conv_rhs => rw [← sum_dotProduct_smul_eigvec hA u]
  rw [sum_dotProduct]
  simp [smul_dotProduct]

lemma pow_mulVec_eigvec (t : ℕ) (j : V) :
    (A ^ t) *ᵥ eigvec hA j = hA.eigenvalues j ^ t • eigvec hA j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, mulVec_eigvec, smul_smul, pow_succ]

/-- The coefficient of `Aᵗ y` along an eigenvector is `νᵗ` times that of `y` (symmetry of `A`). -/
lemma eigvec_dotProduct_pow_mulVec (t : ℕ) (j : V) (y : V → ℝ) :
    eigvec hA j ⬝ᵥ ((A ^ t) *ᵥ y) = hA.eigenvalues j ^ t * (eigvec hA j ⬝ᵥ y) := by
  have hs : Aᵀ = A := IsSymm.eq hA
  have hT : (A ^ t)ᵀ = A ^ t := by rw [transpose_pow, hs]
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, pow_mulVec_eigvec, smul_dotProduct,
    smul_eq_mul]

/-- Contraction: if `y` has no component along eigenvectors with `|ν| > λ`, then
`‖Aᵗ y‖² ≤ λ²ᵗ ‖y‖²`. -/
lemma pow_mulVec_dotProduct_self_le {lam : ℝ} {y : V → ℝ}
    (hy : ∀ j, lam < |hA.eigenvalues j| → eigvec hA j ⬝ᵥ y = 0) (t : ℕ) :
    ((A ^ t) *ᵥ y) ⬝ᵥ ((A ^ t) *ᵥ y) ≤ (lam ^ t) ^ 2 * (y ⬝ᵥ y) := by
  rw [← sum_dotProduct_mul_dotProduct hA, ← sum_dotProduct_mul_dotProduct hA, mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [eigvec_dotProduct_pow_mulVec]
  by_cases hj : lam < |hA.eigenvalues j|
  · simp [hy j hj]
  · have hle : |hA.eigenvalues j ^ t| ≤ lam ^ t := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (not_lt.mp hj) t
    have hsq : (hA.eigenvalues j ^ t) ^ 2 ≤ (lam ^ t) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    nlinarith [sq_nonneg (eigvec hA j ⬝ᵥ y)]

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

/-- Eigenvectors for distinct eigenvalues of a symmetric matrix are orthogonal. -/
lemma eigvec_dotProduct_eq_zero_of_mulVec_eq_smul {u : V → ℝ} {c : ℝ} (hu : A *ᵥ u = c • u)
    {j : V} (hj : hA.eigenvalues j ≠ c) : eigvec hA j ⬝ᵥ u = 0 := by
  have h := eigvec_dotProduct_pow_mulVec hA 1 j u
  rw [pow_one, pow_one, hu, dotProduct_smul, smul_eq_mul] at h
  have h' : (c - hA.eigenvalues j) * (eigvec hA j ⬝ᵥ u) = 0 := by linarith
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1).symm hj
  · exact h1

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
  set a : V → ℝ := fun j => eigvec hA j ⬝ᵥ u₁
  set c : V → ℝ := fun j => eigvec hA j ⬝ᵥ u₂
  have hw (j : V) : eigvec hA j ⬝ᵥ eigvec hA j = 1 := by simp [eigvec_dotProduct_eigvec]
  -- outside `K`, the eigenvalue differs from `c₁` and `c₂`
  have hoff (j : V) (hj : j ∉ K) : a j = 0 ∧ c j = 0 := by
    have hj' : |hA.eigenvalues j| ≤ lam := by simpa [hKdef] using hj
    refine ⟨eigvec_dotProduct_eq_zero_of_mulVec_eq_smul hA hu₁ fun h => ?_,
      eigvec_dotProduct_eq_zero_of_mulVec_eq_smul hA hu₂ fun h => ?_⟩
    · rw [h] at hj'; linarith
    · rw [h] at hj'; linarith
  have hbessel (j : V) : a j ^ 2 + c j ^ 2 ≤ m := sq_add_sq_le hm h₁ h₂ h₁₂ (hw j)
  have hsum : ∑ j ∈ K, (a j ^ 2 + c j ^ 2) = 2 * m := by
    rw [sum_filter_of_ne fun j _ hne => ?_]
    · rw [sum_add_distrib]
      have e₁ := sum_dotProduct_mul_dotProduct hA u₁ u₁
      have e₂ := sum_dotProduct_mul_dotProduct hA u₂ u₂
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
