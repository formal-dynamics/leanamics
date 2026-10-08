import Dynamics.GraphRounds
import Dynamics.Rounds
import Median.Defs

/-! # Two-sample voting on a graph: definitions

Cooper, Elsässer and Radzik, *The power of two choices in distributed voting* (ICALP 2014,
arXiv:1404.7479). Every vertex of a graph `G` holds an opinion; in each synchronous round every
vertex samples two of its neighbours independently and uniformly at random (with replacement)
and, if the two sampled opinions agree, adopts that opinion. With two opinions this is the
median rule of `Median.step` with the two samples restricted to the neighbourhood, so the round
`graphStep` is written with `med3` (`graphStep_bool` gives the 2-Choices form).

The spectral quantity of the paper is `λ_G = max {λ₂, |λₙ|}`, where `1 = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` are
the eigenvalues of the transition matrix `P = A / d` of the random walk on a `d`-regular graph
(`lambdaG`), and `E(S, T)` is the number of ordered pairs `(u, v) ∈ S × T` of adjacent vertices
(`edgeCount`), so that `E(S, S) = 2 |E(S)|` counts every edge inside `S` twice.
-/

namespace Median
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A round of two-sample voting on `G`: the first and the second neighbour sampled by every
vertex. Under the uniform distribution the `2|V|` samples are independent and uniform among the
neighbours (`Dynamics.avg_neighborRound_eval`, `Dynamics.avg_mul_prod`). -/
abbrev GraphRound := NeighborRound G × NeighborRound G

/-- One synchronous round of the median rule on `G`: vertex `v` adopts the median of its own
value and the values of its two sampled neighbours. -/
def graphStep {α : Type*} [LinearOrder α] (x : V → α) (r : GraphRound G) : V → α :=
  fun v => med3 (x v) (x (r.1 v)) (x (r.2 v))

/-- The configuration after a list of rounds (the first round first). -/
def graphRun {α : Type*} [LinearOrder α] (x : V → α) (l : List (GraphRound G)) : V → α :=
  l.foldl (graphStep G) x

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- With two opinions the median rule is two-sample voting: adopt the sampled opinion if the
two samples agree, keep the own opinion otherwise. -/
theorem graphStep_bool (x : V → Bool) (r : GraphRound G) (v : V) :
    graphStep G x r v = if x (r.1 v) = x (r.2 v) then x (r.1 v) else x v := by
  unfold graphStep med3
  cases x v <;> cases x (r.1 v) <;> cases x (r.2 v) <;> rfl

/-- The number of vertices whose opinion differs from `a` (the minority, when `a` is the
majority opinion). -/
def minority (a : Bool) (x : V → Bool) : ℕ := (univ.filter fun v => x v ≠ a).card

/-- `E(S, T)`: the number of ordered pairs `(u, v) ∈ S × T` with `u` adjacent to `v`. Edges
with both endpoints in `S ∩ T` are counted twice; in particular `E(S, S) = 2 |E(S)|`. -/
def edgeCount (S T : Finset V) : ℕ := ∑ u ∈ S, (G.neighborFinset u ∩ T).card

/-- The transition matrix `P = A / d` of the random walk on a `d`-regular graph. -/
noncomputable def transitionMatrix (d : ℕ) : Matrix V V ℝ := (d : ℝ)⁻¹ • G.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
theorem transitionMatrix_isHermitian (d : ℕ) : (transitionMatrix G d).IsHermitian := by
  ext i j
  simp [transitionMatrix, Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]

/-- The eigenvalues `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` of the transition matrix, in non-increasing order
(`Matrix.IsHermitian.eigenvalues₀_antitone`). -/
noncomputable def walkEigenvalues (d : ℕ) : Fin (Fintype.card V) → ℝ :=
  (transitionMatrix_isHermitian G d).eigenvalues₀

/-- `λ_G = max {λ₂, |λₙ|}` (set to `0` on graphs with fewer than two vertices). -/
noncomputable def lambdaG (d : ℕ) : ℝ :=
  if h : 2 ≤ Fintype.card V then
    max (walkEigenvalues G d ⟨1, by omega⟩) |walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩|
  else 0

end Median
