import Voter.LazyLoop
import Voter.Corollaries

/-! # The lazy synchronous voter (VOT-2)

In the lazy voter every vertex keeps its own colour with probability `1/2` and otherwise
copies the colour of a vertex sampled from a kernel `K`, independently of the other vertices:
the synchronous voter with kernel `(I + K)/2`. With uniform neighbour sampling this is
`H = (I + D⁻¹A)/2`, the lazy voter of Berenbrink, Giakkoupis, Kermarrec and Mallmann-Trenn
(roadmap VOT-5).

Laziness puts weight at least `1/2` on every self-loop and does not change stationary
distributions, so the Remark on p. 254 of Hassin and Peleg gives proportionate agreement on
every connected graph, bipartite ones included: consensus in colour `c` has probability equal
to the stationary mass of the vertices initially coloured `c`, which for `(I + D⁻¹A)/2` is
their total degree over `2m`.

The kernels `lazy` and `lazyNeighbor` and their basic lemmas are the core ones of
`Dynamics/Lazy.lean` and `Dynamics/RandomWalk.lean`, exported here into the `Voter` namespace.
-/

namespace Voter
open Dynamics Finset
variable {V C : Type*} [Fintype V] [DecidableEq V]

export Dynamics.Kernel (lazy lazyNeighbor)

/-- Laziness does not change stationary distributions: `p (I + K)/2 = p ↔ p K = p`
(`Dynamics.Kernel.lazy_stationary_iff`, under its VOT-2 name). -/
theorem lazy_stationary_iff (K : Kernel V) (p : Distribution V) :
    (lazy K).Stationary p ↔ K.Stationary p :=
  Kernel.lazy_stationary_iff K p

/-- **Lazy weighted voter (VOT-2), via Hassin–Peleg Theorem 2.1, Section 2.3 and the Remark on
p. 254.** On any connected graph, bipartite or not, let `H` charge every edge and let `p` be
stationary for `H`. Then the lazy voter `(I + H)/2` reaches consensus in colour `c` with
probability equal to the initial `p`-mass of the vertices coloured `c`. -/
theorem lazy_consensus_probability [Fintype C] (G : SimpleGraph V) (hc : G.Connected)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (p : Distribution V) (hp : H.Stationary p) (s : Config V C) (c : C) :
    eventualColor (lazy H) c s = p.prob (fun i => s i = c) := by
  obtain ⟨v⟩ := hc.nonempty
  exact color_consensus_probability_of_selfLoop G hc (lazy H)
    (fun i j h => Kernel.lazy_weight_pos H (hsupport i j h)) ⟨v, Kernel.lazy_selfLoop_pos H v⟩
    p ((lazy_stationary_iff H p).mpr hp) s c

/-- **Lazy synchronous voter (VOT-2), proportionate agreement (Hassin–Peleg Corollary 2.2 for
`(I + D⁻¹A)/2`).** On any connected graph, bipartite or not, the lazy voter reaches consensus
in colour `c` with probability `∑_{i coloured c} dᵢ / 2m`, the initial stationary mass of the
colour. -/
theorem lazyNeighbor_consensus_probability [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) (hd : ∀ i, 0 < G.degree i)
    (s : Config V C) (c : C) :
    eventualColor (lazyNeighbor G hd) c s =
      ∑ i ∈ univ.filter (fun i => s i = c), (G.degree i : ℝ) / (2 * G.edgeFinset.card) := by
  haveI := hc.nonempty
  rw [lazyNeighbor, lazy_consensus_probability G hc _
    (fun i j h => (Kernel.uniformNeighbor_support G hd i j).mpr h) _ (degree_stationary G hd)]
  simp [Distribution.prob, Distribution.expect, degree_weight, sum_filter, mul_ite]

end Voter
