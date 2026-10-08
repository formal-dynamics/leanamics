import Mathlib

/-! # Spectral lemmas for a real symmetric matrix

Generic facts behind Theorem 33 of the Survey (Lovász 1993, Theorem 5.1), for a real symmetric
matrix `A` with Mathlib's orthonormal eigenbasis `bₖ = hA.eigenvectorBasis k` and eigenvalues
`μₖ = hA.eigenvalues k`, written with plain dot products:

* completeness `∑ₖ bₖ(u) bₖ(v) = δᵤᵥ`, orthonormality, and Parseval
  `y ⬝ z = ∑ₖ (bₖ ⬝ y)(bₖ ⬝ z)`;
* `bₖ ⬝ (A z) = μₖ (bₖ ⬝ z)`;
* `|μₖ| ≤ 1` when the quadratic form satisfies `|w ⬝ A w| ≤ w ⬝ w`;
* contraction on the complement of a unit eigenvector `s` for the eigenvalue `1`: if all
  eigenvalues satisfy `|μ| ≤ 1` and at most one satisfies `|μ| > λ`, then
  `‖A y‖ ≤ λ ‖y‖` for `y ⊥ s`;
* the entry bound `|Aᵗ(u, v) - s(u) s(v)| ≤ λᵗ`.
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian)

/-- Completeness of the eigenbasis: `∑ₖ bₖ(u) bₖ(v) = δᵤᵥ`. -/
lemma sum_eigenvectorBasis_mul_eigenvectorBasis (u v : V) :
    ∑ k, hA.eigenvectorBasis k u * hA.eigenvectorBasis k v = if u = v then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2) u) v
  simpa [Matrix.mul_apply, one_apply] using h

/-- Orthonormality of the eigenbasis: `bₖ ⬝ bₗ = δₖₗ`. -/
lemma eigenvectorBasis_dotProduct (k l : V) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ ⇑(hA.eigenvectorBasis l) = if k = l then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2) k) l
  simpa [Matrix.mul_apply, one_apply, dotProduct] using h

/-- Parseval: `y ⬝ z = ∑ₖ (bₖ ⬝ y)(bₖ ⬝ z)`. -/
lemma dotProduct_eq_sum_eigenvectorBasis (y z : V → ℝ) :
    y ⬝ᵥ z = ∑ k, (⇑(hA.eigenvectorBasis k) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  calc y ⬝ᵥ z = ∑ u, ∑ v, y u * z v * (if u = v then 1 else 0) := by
        simp [dotProduct]
    _ = ∑ u, ∑ v, y u * z v *
          ∑ k, hA.eigenvectorBasis k u * hA.eigenvectorBasis k v := by
        simp_rw [sum_eigenvectorBasis_mul_eigenvectorBasis]
    _ = ∑ u, ∑ v, ∑ k, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ u, ∑ k, ∑ v, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ k, ∑ u, ∑ v, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) := Finset.sum_comm
    _ = _ := by
        simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- The coefficients of `A z`: `bₖ ⬝ (A z) = μₖ (bₖ ⬝ z)`. -/
lemma eigenvectorBasis_dotProduct_mulVec (k : V) (z : V → ℝ) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ (A *ᵥ z) =
      hA.eigenvalues k * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial, hA.eq,
    hA.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul]

omit [DecidableEq V] in
include hA in
/-- A symmetric matrix moves between the two sides of a dot product. -/
lemma dotProduct_mulVec_comm (y z : V → ℝ) : y ⬝ᵥ (A *ᵥ z) = (A *ᵥ y) ⬝ᵥ z := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial, hA.eq]

/-- If the quadratic form satisfies `|w ⬝ A w| ≤ w ⬝ w`, every eigenvalue has `|μ| ≤ 1`. -/
lemma abs_eigenvalues_le_one (hq : ∀ w : V → ℝ, |w ⬝ᵥ (A *ᵥ w)| ≤ w ⬝ᵥ w) (k : V) :
    |hA.eigenvalues k| ≤ 1 := by
  have h := hq ⇑(hA.eigenvectorBasis k)
  rw [hA.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul,
    eigenvectorBasis_dotProduct hA k k, if_pos rfl, mul_one] at h
  exact h

/-- Contraction on the complement of `s`: if `s` is a unit eigenvector for the eigenvalue `1`,
every eigenvalue has `|μ| ≤ 1` and at most one has `|μ| > λ`, then `‖A y‖² ≤ λ² ‖y‖²` for every
`y ⊥ s`. -/
lemma mulVec_dotProduct_mulVec_le (s : V → ℝ) (hs : A *ᵥ s = s) (hs1 : s ⬝ᵥ s = 1) {lam : ℝ}
    (hle : ∀ k, |hA.eigenvalues k| ≤ 1)
    (huniq : ∀ k l, lam < |hA.eigenvalues k| → lam < |hA.eigenvalues l| → k = l)
    (y : V → ℝ) (hy : s ⬝ᵥ y = 0) :
    (A *ᵥ y) ⬝ᵥ (A *ᵥ y) ≤ lam ^ 2 * (y ⬝ᵥ y) := by
  rw [dotProduct_eq_sum_eigenvectorBasis hA (A *ᵥ y) (A *ᵥ y),
    dotProduct_eq_sum_eigenvectorBasis hA y y, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [eigenvectorBasis_dotProduct_mulVec]
  by_cases hk : |hA.eigenvalues k| ≤ lam
  · have hsq : hA.eigenvalues k ^ 2 ≤ lam ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hk 2
    nlinarith [sq_nonneg (⇑(hA.eigenvectorBasis k) ⬝ᵥ y)]
  · replace hk : lam < |hA.eigenvalues k| := not_le.mp hk
    have hother : ∀ l ≠ k, ⇑(hA.eigenvectorBasis l) ⬝ᵥ s = 0 := by
      intro l hl
      have hμl : |hA.eigenvalues l| ≤ lam := by
        by_contra h
        exact hl (huniq l k (not_le.mp h) hk)
      have hμ1 : hA.eigenvalues l ≠ 1 := by
        intro h
        rw [h, abs_one] at hμl
        linarith [hk.trans_le (hle k)]
      have h := eigenvectorBasis_dotProduct_mulVec hA l s
      rw [hs] at h
      have h' : (1 - hA.eigenvalues l) * (⇑(hA.eigenvectorBasis l) ⬝ᵥ s) = 0 := by linarith
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hμ1))
    have hsing (z : V → ℝ) : z ⬝ᵥ s =
        (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ s) := by
      rw [dotProduct_eq_sum_eigenvectorBasis hA z s,
        Finset.sum_eq_single k (fun l _ hl => by rw [hother l hl, mul_zero]) (by simp)]
    have hss := hsing s
    rw [hs1] at hss
    have hne : ⇑(hA.eigenvectorBasis k) ⬝ᵥ s ≠ 0 := by
      intro h
      rw [h, mul_zero] at hss
      exact one_ne_zero hss
    have hsy := hsing y
    rw [dotProduct_comm, hy] at hsy
    have hck : ⇑(hA.eigenvectorBasis k) ⬝ᵥ y = 0 :=
      (mul_eq_zero.mp hsy.symm).resolve_right hne
    rw [hck]
    simp

/-- The powers of `A` fix `s` and keep the complement of `s`. -/
lemma pow_mulVec_of_mulVec_eq (s : V → ℝ) (hs : A *ᵥ s = s) (t : ℕ) : A ^ t *ᵥ s = s := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ', ← mulVec_mulVec, ih, hs]

include hA in
/-- Contraction by `λᵗ` of `Aᵗ` on the complement of `s`. -/
lemma pow_mulVec_dotProduct_le (s : V → ℝ) (hs : A *ᵥ s = s) {lam : ℝ}
    (hcontr : ∀ y, s ⬝ᵥ y = 0 → (A *ᵥ y) ⬝ᵥ (A *ᵥ y) ≤ lam ^ 2 * (y ⬝ᵥ y))
    (y : V → ℝ) (hy : s ⬝ᵥ y = 0) (t : ℕ) :
    s ⬝ᵥ (A ^ t *ᵥ y) = 0 ∧ (A ^ t *ᵥ y) ⬝ᵥ (A ^ t *ᵥ y) ≤ lam ^ (2 * t) * (y ⬝ᵥ y) := by
  induction t with
  | zero => simp [hy]
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    refine ⟨?_, ?_⟩
    · rw [dotProduct_mulVec_comm hA, hs, ih.1]
    · calc (A *ᵥ (A ^ t *ᵥ y)) ⬝ᵥ (A *ᵥ (A ^ t *ᵥ y))
          ≤ lam ^ 2 * ((A ^ t *ᵥ y) ⬝ᵥ (A ^ t *ᵥ y)) := hcontr _ ih.1
        _ ≤ lam ^ 2 * (lam ^ (2 * t) * (y ⬝ᵥ y)) :=
          mul_le_mul_of_nonneg_left ih.2 (sq_nonneg lam)
        _ = lam ^ (2 * (t + 1)) * (y ⬝ᵥ y) := by ring

include hA in
/-- The entry bound `|Aᵗ(u, v) - s(u) s(v)| ≤ λᵗ`, from the contraction on the complement of a
unit eigenvector `s` for the eigenvalue `1`. -/
lemma abs_pow_apply_sub_le (s : V → ℝ) (hs : A *ᵥ s = s) (hs1 : s ⬝ᵥ s = 1) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hcontr : ∀ y, s ⬝ᵥ y = 0 → (A *ᵥ y) ⬝ᵥ (A *ᵥ y) ≤ lam ^ 2 * (y ⬝ᵥ y))
    (t : ℕ) (u v : V) : |(A ^ t) u v - s u * s v| ≤ lam ^ t := by
  set y : V → ℝ := Pi.single v 1 - s v • s with hydef
  have hsy : s ⬝ᵥ y = 0 := by
    rw [hydef, dotProduct_sub, dotProduct_single_one, dotProduct_smul, hs1, smul_eq_mul,
      mul_one, sub_self]
  have hyy : y ⬝ᵥ y ≤ 1 := by
    have : y ⬝ᵥ y = 1 - s v ^ 2 := by
      simp only [hydef, sub_dotProduct, dotProduct_sub, single_one_dotProduct,
        dotProduct_single_one, smul_dotProduct, dotProduct_smul, hs1, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
      ring
    rw [this]
    linarith [sq_nonneg (s v)]
  have hAy : (A ^ t *ᵥ y) u = (A ^ t) u v - s u * s v := by
    rw [hydef, mulVec_sub, mulVec_smul, pow_mulVec_of_mulVec_eq s hs, mulVec_single_one]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, col_apply]
    ring
  obtain ⟨-, hb⟩ := pow_mulVec_dotProduct_le hA s hs hcontr y hsy t
  rw [← hAy]
  refine abs_le_of_sq_le_sq ?_ (pow_nonneg hlam t)
  calc (A ^ t *ᵥ y) u ^ 2 ≤ ∑ w, (A ^ t *ᵥ y) w ^ 2 :=
        Finset.single_le_sum (f := fun w => (A ^ t *ᵥ y) w ^ 2) (fun w _ => sq_nonneg _)
          (mem_univ u)
    _ = (A ^ t *ᵥ y) ⬝ᵥ (A ^ t *ᵥ y) := by simp [dotProduct, sq]
    _ ≤ lam ^ (2 * t) * (y ⬝ᵥ y) := hb
    _ ≤ lam ^ (2 * t) * 1 := mul_le_mul_of_nonneg_left hyy (pow_nonneg hlam _)
    _ = (lam ^ t) ^ 2 := by ring

end Averaging
