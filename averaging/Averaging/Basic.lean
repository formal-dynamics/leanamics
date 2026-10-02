import Mathlib

/-! # Averaging dynamics on graphs

In every round each node replaces its value by the average of its neighbours' values (the
expectation of the value at one step of the random walk). The degree-weighted sum of the values
is conserved, values stay within the initial range, and on a connected graph containing an odd
closed walk (i.e. a connected non-bipartite graph) every node's value converges to the
degree-weighted average `∑ deg v · x v / ∑ deg v` of the initial values. On a connected bipartite
graph with at least two nodes this fails: the values `±1` of a proper 2-colouring alternate forever.
-/

namespace Averaging
open Finset Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One round of averaging: every node takes the average of its neighbours' values. -/
noncomputable def avgStep (x : V → ℝ) : V → ℝ :=
  fun v => (∑ u ∈ G.neighborFinset v, x u) / G.degree v

/-- `t` rounds of averaging. -/
noncomputable def avgIter : ℕ → (V → ℝ) → V → ℝ
  | 0, x => x
  | t + 1, x => avgStep G (avgIter t x)

/-- The degree-weighted average of the values (their mean under the stationary distribution of
the random walk). -/
noncomputable def degAvg (x : V → ℝ) : ℝ :=
  (∑ v, (G.degree v : ℝ) * x v) / ∑ v, (G.degree v : ℝ)

/-- The degree-weighted sum is conserved by a round. -/
theorem degree_weighted_sum_step (x : V → ℝ) :
    ∑ v, (G.degree v : ℝ) * avgStep G x v = ∑ v, (G.degree v : ℝ) * x v := by
  sorry

/-- Maximum principle: without isolated nodes, a round never exceeds an upper bound. -/
theorem avgStep_le (hdeg : ∀ v, 0 < G.degree v) {x : V → ℝ} {M : ℝ} (hM : ∀ v, x v ≤ M) (v : V) :
    avgStep G x v ≤ M := by
  sorry

/-- Minimum principle: without isolated nodes, a round never goes below a lower bound. -/
theorem le_avgStep (hdeg : ∀ v, 0 < G.degree v) {x : V → ℝ} {m : ℝ} (hm : ∀ v, m ≤ x v) (v : V) :
    m ≤ avgStep G x v := by
  sorry

/-- Convergence: on a connected graph with an odd closed walk, every value converges to the
degree-weighted average of the initial values. -/
theorem tendsto_degAvg (hc : G.Connected) (hodd : ∃ (u : V) (p : G.Walk u u), Odd p.length)
    (x : V → ℝ) (v : V) :
    Tendsto (fun t => avgIter G t x v) atTop (𝓝 (degAvg G x)) := by
  sorry

/-- The odd closed walk is needed: on a connected bipartite graph with at least two nodes, some
initial values make no node converge. -/
theorem not_tendsto_of_colorable [Nontrivial V] (hc : G.Connected) (h2 : G.Colorable 2) :
    ∃ x : V → ℝ, ∀ v, ¬ ∃ c, Tendsto (fun t => avgIter G t x v) atTop (𝓝 c) := by
  sorry

end Averaging
