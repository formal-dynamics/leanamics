import Voter.Colors
import Voter.LazyPropagation

/-! # Theorem 2.1 on bipartite graphs with a self-loop (Remark, p. 254)

Hassin and Peleg remark after Theorem 2.1 that adding self-loops with arbitrary positive
weights, even at a single vertex, makes Theorem 2.1 hold without the requirement that the
graph is nonbipartite. In the propagation argument of Lemma 2.1 the vertex with the self-loop
can keep its colour, so it plays the role of the monochromatic edge; the martingale part
(Lemmas 2.2 and 2.3) never used the graph.

This is the form needed by lazy chains (`Voter.Lazy`), which have a self-loop at every vertex,
and by Wright–Fisher sampling on two individuals, whose complete graph `K_2` is bipartite.
-/

namespace Voter
open Dynamics Filter Topology
variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 2.2, graph-free form.** Whenever nonconsensus probability tends to zero, eventual
all-white consensus probability is the initial stationary white mass. -/
theorem eventualColor_eq_whiteMass_of_tendsto [Nonempty V] (H : Kernel V) (p : Distribution V)
    (hp : H.Stationary p) (s : Config V Bool)
    (hsurv : Tendsto (fun n => (transition H).iterate n survival s) atTop (𝓝 0)) :
    eventualColor H true s = whiteMass p s := by
  have hz : Tendsto (fun n => whiteMass p s - colorProbability H true n s) atTop (𝓝 0) :=
    squeeze_zero (fun n => (whiteProbability_error H p hp n s).1)
      (fun n => (whiteProbability_error H p hp n s).2) hsurv
  have hcst : Tendsto (fun _ : ℕ => whiteMass p s) atTop (𝓝 (whiteMass p s)) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique (colorProbability_tendsto H true s) (by simpa using hcst.sub hz)

/-- **Hassin–Peleg Theorem 2.1 with the Remark on p. 254.** On a connected graph, bipartite or
not, if the kernel charges every edge and some vertex keeps its own colour with positive
probability, then eventual all-white consensus probability is the initial stationary white
mass. -/
theorem consensus_probability_of_selfLoop (G : SimpleGraph V) (hc : G.Connected)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (hloop : ∃ v, 0 < (H v).weight v)
    (p : Distribution V) (hp : H.Stationary p) (s : Config V Bool) :
    eventualColor H true s = whiteMass p s := by
  haveI := hc.nonempty
  exact eventualColor_eq_whiteMass_of_tendsto H p hp s
    (consensus_tendsto_of_selfLoop G hc H hsupport hloop s)

/-- **Hassin–Peleg Section 2.3 with the Remark on p. 254.** Under the hypotheses of
`consensus_probability_of_selfLoop`, consensus in any colour `c` of a finite palette has
probability equal to the initial stationary mass of the vertices coloured `c`. -/
theorem color_consensus_probability_of_selfLoop [Fintype C]
    (G : SimpleGraph V) (hc : G.Connected)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (hloop : ∃ v, 0 < (H v).weight v)
    (p : Distribution V) (hp : H.Stationary p) (s : Config V C) (c : C) :
    eventualColor H c s = p.prob (fun i => s i = c) := by
  classical
  rw [← eventualColor_project, consensus_probability_of_selfLoop G hc H hsupport hloop p hp]
  simp [whiteMass, mass, colorIndicator, Distribution.prob]

end Voter
