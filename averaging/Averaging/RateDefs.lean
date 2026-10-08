import Averaging.Basic

/-! # Rate of convergence of the averaging dynamics: definitions

Definitions for the rate bound of roadmap AVG-1: Becchetti, Clementi, Natale, *Consensus
Dynamics: An Overview*, SIGACT News 51(1), 2020 (the Survey), Section 7.2, Theorem 33, which
cites Lovász, *Random walks on graphs: a survey*, 1993, Theorem 5.1.

* `walkMatrix`: the transition matrix `P = D⁻¹A` of the random walk (Survey, footnote 24);
* `normAdjMatrix`: the symmetric matrix `N = D^{-1/2} A D^{-1/2}`, similar to `P`
  (`charpoly_walkMatrix`), so that `P` and `N` have the same eigenvalues;
* `walkLambda`: `λ = max {|λ₂(P)|, |λₙ(P)|}` (Theorem 33), read off Mathlib's decreasingly
  sorted spectrum `Matrix.IsHermitian.eigenvalues₀` of `N`;
* `walkStationary`: the stationary distribution `π(v) = d(v) / 2m` (Theorem 32).

The values after `t` rounds are `avgIter G t x` (`Averaging.Basic`) and the `t`-step transition
probabilities `transW G t u v`.
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The transition matrix `P = D⁻¹A` of the random walk on `G` (Survey, footnote 24):
`P u v = 1 / d(u)` if `u ~ v` and `0` otherwise (the row of an isolated node is zero). -/
noncomputable def walkMatrix : Matrix V V ℝ :=
  diagonal (fun v => (G.degree v : ℝ)⁻¹) * G.adjMatrix ℝ

/-- The normalized adjacency matrix `N = D^{-1/2} A D^{-1/2}`. When every degree is positive,
`P = D^{-1/2} N D^{1/2}`, so `P` and `N` have the same eigenvalues (`charpoly_walkMatrix`). -/
noncomputable def normAdjMatrix : Matrix V V ℝ :=
  diagonal (fun v => (√(G.degree v : ℝ))⁻¹) * G.adjMatrix ℝ *
    diagonal (fun v => (√(G.degree v : ℝ))⁻¹)

/-- `N = D^{-1/2} A D^{-1/2}` is real symmetric. -/
lemma normAdjMatrix_isHermitian : (normAdjMatrix G).IsHermitian := by
  have h := isHermitian_conjTranspose_mul_mul (diagonal fun v => (√(G.degree v : ℝ))⁻¹)
    (G.isHermitian_adjMatrix ℝ)
  rwa [diagonal_conjTranspose, star_trivial] at h

/-- **`λ` of Theorem 33**: `λ = max {|λ₂(P)|, |λₙ(P)|}`, where `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` are the
eigenvalues of `P = D⁻¹A`, listed in decreasing order with multiplicity. They are computed as the
eigenvalues of the similar symmetric matrix `N = D^{-1/2} A D^{-1/2}` (`charpoly_walkMatrix`),
with Mathlib's `Matrix.IsHermitian.eigenvalues₀`, which is indexed from `0` (so `λ₂` has
index `1` and `λₙ` index `n - 1`). By convention `λ = 0` when `n < 2`. -/
noncomputable def walkLambda : ℝ :=
  if h : 2 ≤ Fintype.card V then
    max |(normAdjMatrix_isHermitian G).eigenvalues₀ ⟨1, by omega⟩|
      |(normAdjMatrix_isHermitian G).eigenvalues₀ ⟨Fintype.card V - 1, by omega⟩|
  else 0

/-- The stationary distribution `π(v) = d(v) / 2m` of the random walk on `G`, where `m` is the
number of edges (Survey, Theorem 32). -/
noncomputable def walkStationary (v : V) : ℝ :=
  (G.degree v : ℝ) / (2 * #G.edgeFinset)

end Averaging
