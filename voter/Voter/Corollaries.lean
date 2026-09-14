import Voter.Colors
import Voter.Uniform

/-! # Uniform-neighbor and regular-graph consensus probabilities -/
namespace Voter
open Dynamics Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma graph_degree_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : ¬ G.Colorable 2) (v : V) : 0 < G.degree v := by
  obtain ⟨i, j, hij, _⟩ := monochromatic_edge G hn (fun _ => false)
  haveI : Nontrivial V := ⟨⟨i, j, hij.ne⟩⟩
  exact (G.degree_pos_iff_exists_adj v).mpr (hc.preconnected.exists_adj_of_nontrivial v)

lemma uniformNeighbor_support (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ i, 0 < G.degree i) (i j : V) :
    0 < (uniformNeighbor G hd i).weight j ↔ G.Adj i j := by
  simp only [uniformNeighbor]
  split_ifs with h
  · simp [h, hd i]
  · simp [h]

/-- **Corollary 2.2.** Uniform neighbor sampling weights initial white vertices by degree. -/
theorem uniform_consensus_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : ¬ G.Colorable 2) (s : Config V Bool) :
    eventualColor (uniformNeighbor G (graph_degree_pos G hc hn)) true s =
      ∑ i ∈ univ.filter (fun i => s i = true), (G.degree i : ℝ) / (2 * G.edgeFinset.card) := by
  rw [consensus_probability G hc hn _ (uniformNeighbor_support G _) _ (degree_stationary G _)]
  unfold whiteMass mass Distribution.expect
  simp_rw [degree_weight]
  simp [sum_filter, mul_ite]

/-- On a regular graph, the consensus probability is the initial white fraction. -/
theorem regular_consensus_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : ¬ G.Colorable 2) (d : ℕ) (hreg : ∀ i, G.degree i = d)
    (s : Config V Bool) :
    eventualColor (uniformNeighbor G (graph_degree_pos G hc hn)) true s =
      ((univ.filter fun i => s i = true).card : ℝ) / Fintype.card V := by
  rw [consensus_probability G hc hn _ (uniformNeighbor_support G _) _ (degree_stationary G _)]
  exact degree_mass_regular G _ d hreg s

end Voter
