import Averaging.RateDefs
import Dynamics.Kernel
import Dynamics.Uniform

/-! # Averaging in the random sequential model: definitions

Definitions for the expected-matrix identities of roadmap AVG-1: Becchetti, Clementi, Natale,
*Consensus Dynamics: An Overview*, SIGACT News 51(1), 2020 (the Survey), Section 7.2,
equations (2)–(5), after Boyd, Ghosh, Prabhakar, Shah, *Randomized gossip algorithms*,
IEEE Trans. Inf. Theory 52(6), 2006 (BGPS06). In each step one edge is selected and its two
endpoints replace their values by their average (`Averaging(δ)` of Definition 31 with
`δ = 1/2`, the case of Section 7.2).

* `edgeMatrix`: the matrix `W = I - (e_i - e_j)(e_i - e_j)ᵀ / 2` of one step on the edge
  `(i, j)` (equation (2));
* `seqRun`: the state `x⁽ᵗ⁾ = W(t) ⋯ W(1) x⁽⁰⁾` after a sequence of selected oriented edges
  (equation (3));
* `kernelMatrix`, `gossipMeanMatrix`: the stochastic matrix `P` of a transition kernel and the
  right-hand side `I - D̄/(2n) + (P + Pᵀ)/(2n)` of equation (4);
* `meanMatrix`: the expected step matrix `W̄ = I - L/(2m)` when one oriented edge is selected
  uniformly at random (the random sequential model of the Survey, Section 2).
-/

namespace Averaging.Sequential
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Equation (2): the matrix `W = I - (e_i - e_j)(e_i - e_j)ᵀ / 2` of one step of averaging in
which the edge `(i, j)` is selected, `e_h` the `h`-th canonical vector. -/
noncomputable def edgeMatrix (i j : V) : Matrix V V ℝ :=
  1 - (1 / 2 : ℝ) • vecMulVec (Pi.single i 1 - Pi.single j 1) (Pi.single i 1 - Pi.single j 1)

/-- The stochastic matrix `Pᵢⱼ = (K i).weight j` of a transition kernel `K`. -/
noncomputable def kernelMatrix (K : Kernel V) : Matrix V V ℝ :=
  of fun i j => (K i).weight j

/-- The right-hand side of equation (4), `I - D̄/(2n) + (P + Pᵀ)/(2n)`, for the stochastic
matrix `P` of the kernel `K`, with `n = |V|` and `D̄` the diagonal matrix with
`D̄ᵢᵢ = ∑ⱼ (Pᵢⱼ + Pⱼᵢ)`. -/
noncomputable def gossipMeanMatrix (K : Kernel V) : Matrix V V ℝ :=
  1 - (2 * (Fintype.card V : ℝ))⁻¹ •
      diagonal (fun i => ∑ j, (kernelMatrix K i j + kernelMatrix K j i)) +
    (2 * (Fintype.card V : ℝ))⁻¹ • (kernelMatrix K + (kernelMatrix K)ᵀ)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Equation (3): the state `x⁽ᵗ⁾ = W(t) ⋯ W(1) x⁽⁰⁾` after the oriented edges `l` have been
selected, the first step at the head of `l` (as in `Dynamics.expList`). -/
noncomputable def seqRun (x : V → ℝ) (l : List G.Dart) : V → ℝ :=
  l.foldl (fun y d => edgeMatrix d.fst d.snd *ᵥ y) x

/-- The expected step matrix `W̄ = I - L / (2m)` when one oriented edge of `G` is selected
uniformly at random, where `L = D - A` is the Laplacian and `m` the number of edges. -/
noncomputable def meanMatrix : Matrix V V ℝ :=
  1 - (2 * (#G.edgeFinset : ℝ))⁻¹ • G.lapMatrix ℝ

end Averaging.Sequential
