import Dynamics.Spectral

/-! # Spectral lemmas for a real symmetric matrix

Facts behind Theorem 33 of the Survey (Lovász 1993, Theorem 5.1), for a real symmetric matrix `A`
with Mathlib's orthonormal eigenbasis `bₖ = hA.eigenvectorBasis k` and eigenvalues
`μₖ = hA.eigenvalues k`, on top of the plain-vector eigenbasis API of `Dynamics/Spectral.lean`
(Parseval, `bₖ ⬝ (Aᵗ z) = μₖᵗ (bₖ ⬝ z)`, the spectral bound for powers):

* `|μₖ| ≤ 1` when the quadratic form satisfies `|w ⬝ A w| ≤ w ⬝ w`;
* orthogonality on the complement of a unit eigenvector `s` for the eigenvalue `1`: if all
  eigenvalues satisfy `|μ| ≤ 1` and at most one satisfies `|μ| > λ`, then every `y ⊥ s` has no
  component along the eigenvectors with `|μ| > λ`, so `‖Aᵗ y‖ ≤ λᵗ ‖y‖`;
* the entry bound `|Aᵗ(u, v) - s(u) s(v)| ≤ λᵗ`.
-/

namespace Averaging
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian)

/-- If the quadratic form satisfies `|w ⬝ A w| ≤ w ⬝ w`, every eigenvalue has `|μ| ≤ 1`. -/
lemma abs_eigenvalues_le_one (hq : ∀ w : V → ℝ, |w ⬝ᵥ (A *ᵥ w)| ≤ w ⬝ᵥ w) (k : V) :
    |hA.eigenvalues k| ≤ 1 := by
  have h := hq ⇑(hA.eigenvectorBasis k)
  rw [hA.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul,
    eigenvectorBasis_dotProduct hA k k, if_pos rfl, mul_one] at h
  exact h

/-- Orthogonality on the complement of `s`: if `s` is a unit eigenvector for the eigenvalue `1`,
every eigenvalue has `|μ| ≤ 1` and at most one has `|μ| > λ`, then every `y ⊥ s` has no
component along the eigenvectors with `|μ| > λ`. -/
lemma eigenvectorBasis_dotProduct_eq_zero_of_orthogonal (s : V → ℝ) (hs : A *ᵥ s = s)
    (hs1 : s ⬝ᵥ s = 1) {lam : ℝ} (hle : ∀ k, |hA.eigenvalues k| ≤ 1)
    (huniq : ∀ k l, lam < |hA.eigenvalues k| → lam < |hA.eigenvalues l| → k = l)
    (y : V → ℝ) (hy : s ⬝ᵥ y = 0) (k : V) (hk : lam < |hA.eigenvalues k|) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ y = 0 := by
  have hother : ∀ l ≠ k, ⇑(hA.eigenvectorBasis l) ⬝ᵥ s = 0 := by
    intro l hl
    have hμl : |hA.eigenvalues l| ≤ lam := by
      by_contra h
      exact hl (huniq l k (not_le.mp h) hk)
    refine eigenvectorBasis_dotProduct_eq_zero_of_mulVec_eq_smul hA (c := 1)
      (by rw [one_smul]; exact hs) fun h => ?_
    rw [h, abs_one] at hμl
    linarith [hk.trans_le (hle k)]
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
  exact (mul_eq_zero.mp hsy.symm).resolve_right hne

/-- The entry bound `|Aᵗ(u, v) - s(u) s(v)| ≤ λᵗ`, for a unit eigenvector `s` for the eigenvalue
`1` whose complement has no component along the eigenvectors with `|μ| > λ`
(`eigenvectorBasis_dotProduct_eq_zero_of_orthogonal`), by the spectral bound for powers
`Dynamics.pow_mulVec_dotProduct_self_le`. -/
lemma abs_pow_apply_sub_le (s : V → ℝ) (hs : A *ᵥ s = s) (hs1 : s ⬝ᵥ s = 1) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hcomp : ∀ y, s ⬝ᵥ y = 0 → ∀ k, lam < |hA.eigenvalues k| →
      ⇑(hA.eigenvectorBasis k) ⬝ᵥ y = 0)
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
  have hst : A ^ t *ᵥ s = s := by
    rw [pow_mulVec_of_mulVec_eq_smul (c := 1) (by rw [one_smul]; exact hs) t, one_pow, one_smul]
  have hAy : (A ^ t *ᵥ y) u = (A ^ t) u v - s u * s v := by
    rw [hydef, mulVec_sub, mulVec_smul, hst, mulVec_single_one]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, col_apply]
    ring
  have hb := pow_mulVec_dotProduct_self_le hA (hcomp y hsy) t
  rw [← hAy]
  refine abs_le_of_sq_le_sq ?_ (pow_nonneg hlam t)
  calc (A ^ t *ᵥ y) u ^ 2 ≤ ∑ w, (A ^ t *ᵥ y) w ^ 2 :=
        Finset.single_le_sum (f := fun w => (A ^ t *ᵥ y) w ^ 2) (fun w _ => sq_nonneg _)
          (mem_univ u)
    _ = (A ^ t *ᵥ y) ⬝ᵥ (A ^ t *ᵥ y) := by simp [dotProduct, sq]
    _ ≤ (lam ^ t) ^ 2 * (y ⬝ᵥ y) := hb
    _ ≤ (lam ^ t) ^ 2 * 1 := mul_le_mul_of_nonneg_left hyy (sq_nonneg _)
    _ = (lam ^ t) ^ 2 := mul_one _

end Averaging
