import Moran.Isothermal

/-! # Push versus pull: neutral fixation on arbitrary graphs (VOT-4)

Two sequential neutral voter dynamics on a finite graph:

* **push** (Birth–death, the neutral Moran process `moranKernel G 1`): a uniformly random vertex
  places a copy of its type on a uniformly random neighbour;
* **pull** (death–Birth, `pullKernel G`): a uniformly random vertex adopts the type of a uniformly
  random neighbour.

On the complete graph they coincide, but on an irregular graph they do not: from a mutant set
`S` on a connected graph, push fixes with probability `∑_{v ∈ S} 1/deg v / ∑_v 1/deg v`, while
pull fixes with probability `∑_{v ∈ S} deg v / ∑_v deg v`. Each follows from an invariant
"reproductive value" (`1/deg` for push, `deg` for pull), whose expected change vanishes edge by
edge on every graph.
-/

namespace Moran
open Dynamics Finset Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weight of the pair (vertex that updates, neighbour it copies) in one death–Birth step. -/
noncomputable def pullWeight (G : SimpleGraph V) [DecidableRel G.Adj] (p : V × V) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ * target G p.1 p.2

/-- The death–Birth pair weights are nonnegative. -/
theorem pull_weight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (p : V × V) :
    0 ≤ pullWeight G p := by
  sorry

/-- The death–Birth pair weights sum to one. -/
theorem pull_weight_sum_one [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ p : V × V, pullWeight G p = 1 := by
  sorry

/-- Distribution of (vertex that updates, neighbour it copies). -/
noncomputable def pullDist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Distribution (V × V) where
  weight := pullWeight G
  nonneg := pull_weight_nonneg G
  sum_one := pull_weight_sum_one G

/-- The death–Birth (sequential pull voter) kernel: a uniformly random vertex adopts the type of
a uniformly random neighbour (an isolated vertex keeps its type). -/
noncomputable def pullKernel [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Kernel (Config V) :=
  fun s => (pullDist G).map (fun p => Function.update s p.1 (s p.2))

/-- Reproductive value of the mutants under push: `∑_{v mutant} 1 / deg v`. -/
noncomputable def pushValue (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) : ℝ :=
  ∑ v ∈ univ.filter (fun v => s v = true), (G.degree v : ℝ)⁻¹

/-- Reproductive value of the mutants under pull: `∑_{v mutant} deg v`. -/
noncomputable def pullValue (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) : ℝ :=
  ∑ v ∈ univ.filter (fun v => s v = true), (G.degree v : ℝ)

/-- **Push invariant.** On every graph, the neutral Birth–death step preserves
`∑_{v mutant} 1/deg v` in expectation. -/
theorem push_value_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Config V) :
    (moranKernel G 1 one_pos).apply (pushValue G) s = pushValue G s := by
  sorry

/-- **Pull invariant.** On every graph, the death–Birth step preserves `∑_{v mutant} deg v` in
expectation. -/
theorem pull_value_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Config V) :
    (pullKernel G).apply (pullValue G) s = pullValue G s := by
  sorry

/-- **Absorption under pull.** On a connected graph, the probability that neither type has fixed
tends to zero. -/
theorem pull_unfixed_tendsto [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (s : Config V) :
    Tendsto (fun t => (pullKernel G).iterate t unfixed s) atTop (𝓝 0) := by
  sorry

/-- **Push fixation.** On a connected graph with at least two vertices, neutral Birth–death
fixes with probability `∑_{v ∈ S} 1/deg v / ∑_v 1/deg v`. -/
theorem push_fixation [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (s : Config V) :
    fixation (moranKernel G 1 one_pos) s = pushValue G s / pushValue G (fun _ => true) := by
  sorry

/-- **Pull fixation.** On a connected graph with at least two vertices, death–Birth fixes with
probability `∑_{v ∈ S} deg v / ∑_v deg v`. -/
theorem pull_fixation [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (s : Config V) :
    fixation (pullKernel G) s = pullValue G s / pullValue G (fun _ => true) := by
  sorry

end Moran
