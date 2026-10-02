import Median.Defs

/-! # The median dynamics: structure

The median commutes with monotone maps, so thresholding the median process at any value `θ`
gives exactly the binary median process (2-Choices) driven by the same samples: the multi-valued
dynamics is a family of coupled binary ones. Values stay within the current range, and with two
values one round maps the fraction `p` of `true`s to `3p² − 2p³` in expectation. Every run reaches
consensus almost surely.
-/

namespace Median
open Finset Dynamics Filter Topology

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- The median commutes with monotone maps. -/
theorem med3_monotone {β : Type*} [LinearOrder β] {f : α → β} (hf : Monotone f) (a b c : α) :
    f (med3 a b c) = med3 (f a) (f b) (f c) := by
  sorry

/-- Threshold reduction, one round: thresholding commutes with the median rule. -/
theorem threshold_step (θ : α) (x : Config n α) (r : Round n) :
    (fun v => decide (θ ≤ step x r v)) = step (fun v => decide (θ ≤ x v)) r := by
  sorry

/-- Threshold reduction, any number of rounds (same samples). -/
theorem threshold_run (θ : α) (x : Config n α) (l : List (Round n)) :
    (fun v => decide (θ ≤ run x l v)) = run (fun v => decide (θ ≤ x v)) l := by
  sorry

/-- Validity: every new value is a current value. -/
theorem step_mem (x : Config n α) (r : Round n) (v : Fin n) : ∃ u, step x r v = x u := by
  sorry

/-- The values stay within any interval containing all current values. -/
theorem step_mem_Icc {m M : α} (x : Config n α) (hx : ∀ v, x v ∈ Set.Icc m M) (r : Round n)
    (v : Fin n) : step x r v ∈ Set.Icc m M := by
  sorry

/-- Consensus configurations are fixed points. -/
theorem step_of_consensus (x : Config n α) (h : Consensus x) (r : Round n) : step x r = x := by
  sorry

/-- Binary case: one round maps the fraction `p` of `true`s to `3p² − 2p³` in expectation. -/
theorem expected_ones [NeZero n] (x : Config n Bool) :
    avg (fun r : Round n => (ones (step x r) : ℝ)) =
      n * (3 * ((ones x : ℝ) / n) ^ 2 - 2 * ((ones x : ℝ) / n) ^ 3) := by
  sorry

/-- Almost-sure consensus: the probability of not being in consensus after `t` rounds tends to
zero, from every configuration. -/
theorem absorbed [NeZero n] [Fintype α] [Nonempty α] (x : Config n α) :
    Tendsto (fun t => (kernel n α).iterate t notConsensus x) atTop (𝓝 0) := by
  sorry

end Median
