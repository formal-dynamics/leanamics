import Epidemics.CobraDuality

/-! # Spectral quantities for the COBRA cover time (EPI-4)

Cooper, Radzik, Rivera, *The coalescing-branching random walk on expanders and the dual epidemic
process*, PODC 2016 (arXiv:1602.05768), Section 1 and the proof of Lemma 1 (Section 3).

For a connected `r`-regular graph `G` the random walk has transition matrix `P = A(G) / r`, with
eigenvalues `1 = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ ≥ -1`, and the paper's `λ = λ_max = max_{i ≥ 2} |λᵢ|`. Since
`λₙ ≤ λ₂`, this is `max {λ₂, |λₙ|}` (`lambdaG`).

*Duplication note.* `transitionMatrix`, `walkEigenvalues` and `lambdaG` are verbatim copies of
`Median.transitionMatrix`, `Median.walkEigenvalues` and `Median.lambdaG` (median package, two-sample
voting on expanders): the epidemics package does not depend on the median package. They should
move to `dynamics/` together with the spectral lemmas below.

The spectral core of Lemma 1 is `‖P 1_A‖² ≤ λ² |A| + (1 - λ²) |A|² / n`, where
`(P 1_A)(x) = d_A(x) / r` and `d_A(x) = |N(x) ∩ A|` (`sum_sq_neighbor_le`).
-/

namespace Epidemics
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The transition matrix `P = A / d` of the random walk on a `d`-regular graph (copy of
`Median.transitionMatrix`). -/
noncomputable def transitionMatrix (d : ℕ) : Matrix V V ℝ := (d : ℝ)⁻¹ • G.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
/-- `P = A / d` is real symmetric. -/
theorem transitionMatrix_isHermitian (d : ℕ) : (transitionMatrix G d).IsHermitian := by
  ext i j
  simp [transitionMatrix, Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]

/-- The eigenvalues `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` of the transition matrix, in non-increasing order
(copy of `Median.walkEigenvalues`). -/
noncomputable def walkEigenvalues (d : ℕ) : Fin (Fintype.card V) → ℝ :=
  (transitionMatrix_isHermitian G d).eigenvalues₀

/-- The paper's `λ = λ_max = max_{i ≥ 2} |λᵢ|` (Section 1), written `max {λ₂, |λₙ|}` (equal,
since `λₙ ≤ λ₂`), and set to `0` on graphs with fewer than two vertices (copy of
`Median.lambdaG`). -/
noncomputable def lambdaG (d : ℕ) : ℝ :=
  if h : 2 ≤ Fintype.card V then
    max (walkEigenvalues G d ⟨1, by omega⟩) |walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩|
  else 0

/-- `λ ≥ 0`. -/
lemma lambdaG_nonneg (d : ℕ) : 0 ≤ lambdaG G d := by
  unfold lambdaG
  split_ifs
  · exact (abs_nonneg _).trans (le_max_right _ _)
  · exact le_rfl

variable {G}

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
  sorry

end Epidemics
