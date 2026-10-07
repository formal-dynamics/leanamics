import Averaging.RateDefs

/-! # The random-walk matrix and its symmetrization: entries and similarity

Helpers for the rate bound (Survey, Section 7.2, Theorem 33): the entries of `P = D⁻¹A`, the
identification of `Pᵗ` with the `t`-step transition probabilities `transW` and of the averaging
dynamics with `Pᵗ x`, and the similarity `P = D^{-1/2} N D^{1/2}` with
`N = D^{-1/2} A D^{-1/2}` when every degree is positive.
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The entries of `P = D⁻¹A`: `P u v = 1 / d(u)` if `u ~ v`, `0` otherwise. -/
lemma walkMatrix_apply (u v : V) :
    walkMatrix G u v = if G.Adj u v then (G.degree u : ℝ)⁻¹ else 0 := by
  rw [walkMatrix, diagonal_mul, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

/-- `Pᵗ(u, v)` is the `t`-step transition probability `transW G t u v`. -/
lemma walkMatrix_pow_apply_eq_transW (t : ℕ) (u v : V) :
    (walkMatrix G ^ t) u v = transW G t u v := by
  induction t generalizing u with
  | zero => simp [transW, one_apply]
  | succ t ih =>
    rw [pow_succ', mul_apply]
    simp_rw [ih]
    simp only [transW, walkMatrix, diagonal_mul, SimpleGraph.adjMatrix_apply, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul]
    rw [← sum_filter, div_eq_inv_mul, mul_sum, SimpleGraph.neighborFinset_eq_filter]

/-- The averaging dynamics is `x⁽ᵗ⁾ = Pᵗ x⁽⁰⁾`. -/
lemma avgIter_eq_walkMatrix_pow_mulVec' (t : ℕ) (x : V → ℝ) :
    avgIter G t x = walkMatrix G ^ t *ᵥ x := by
  funext u
  rw [avgIter_eq_sum_transW]
  simp only [mulVec, dotProduct, walkMatrix_pow_apply_eq_transW]

/-- The entries of `N = D^{-1/2} A D^{-1/2}`. -/
lemma normAdjMatrix_apply (u v : V) :
    normAdjMatrix G u v =
      if G.Adj u v then (√(G.degree u : ℝ))⁻¹ * (√(G.degree v : ℝ))⁻¹ else 0 := by
  rw [normAdjMatrix, mul_diagonal, diagonal_mul, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

/-- `D^{1/2} D^{-1/2} = I` when every degree is positive. -/
lemma diagonal_sqrt_mul_inv (hdeg : ∀ v, 0 < G.degree v) :
    diagonal (fun v => √(G.degree v : ℝ)) * diagonal (fun v => (√(G.degree v : ℝ))⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext v
  exact mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (by exact_mod_cast hdeg v))

/-- `P = D^{-1/2} N D^{1/2}` when every degree is positive. -/
lemma walkMatrix_eq_conj (hdeg : ∀ v, 0 < G.degree v) :
    walkMatrix G = diagonal (fun v => (√(G.degree v : ℝ))⁻¹) * normAdjMatrix G *
      diagonal (fun v => √(G.degree v : ℝ)) := by
  ext u v
  rw [mul_diagonal, diagonal_mul, walkMatrix_apply, normAdjMatrix_apply]
  split_ifs with h
  · have hu : (0 : ℝ) < G.degree u := by exact_mod_cast hdeg u
    have hv : (0 : ℝ) < G.degree v := by exact_mod_cast hdeg v
    have hsv : √(G.degree v : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hv
    field_simp
    exact Real.sq_sqrt hu.le
  · simp

/-- `Pᵗ = D^{-1/2} Nᵗ D^{1/2}` when every degree is positive. -/
lemma walkMatrix_pow_eq (hdeg : ∀ v, 0 < G.degree v) (t : ℕ) :
    walkMatrix G ^ t = diagonal (fun v => (√(G.degree v : ℝ))⁻¹) * normAdjMatrix G ^ t *
      diagonal (fun v => √(G.degree v : ℝ)) := by
  have hone := diagonal_sqrt_mul_inv G hdeg
  have hone' : diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *
      diagonal (fun v => √(G.degree v : ℝ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext v
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by exact_mod_cast hdeg v))
  induction t with
  | zero => simp [hone']
  | succ t ih =>
    rw [pow_succ, ih, walkMatrix_eq_conj G hdeg, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal fun v => √(G.degree v : ℝ)), hone, Matrix.one_mul]

/-- The entries of `Pᵗ` through `Nᵗ`: `Pᵗ(u, v) = d(u)^{-1/2} Nᵗ(u, v) d(v)^{1/2}`. -/
lemma walkMatrix_pow_apply_eq (hdeg : ∀ v, 0 < G.degree v) (t : ℕ) (u v : V) :
    (walkMatrix G ^ t) u v =
      (√(G.degree u : ℝ))⁻¹ * (normAdjMatrix G ^ t) u v * √(G.degree v : ℝ) := by
  rw [walkMatrix_pow_eq G hdeg, mul_diagonal, diagonal_mul]

/-- `P` and `N` have the same characteristic polynomial when every degree is positive. -/
lemma charpoly_walkMatrix_eq (hdeg : ∀ v, 0 < G.degree v) :
    (walkMatrix G).charpoly = (normAdjMatrix G).charpoly := by
  rw [walkMatrix_eq_conj G hdeg, Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc,
    diagonal_sqrt_mul_inv G hdeg, Matrix.mul_one]

end Averaging
