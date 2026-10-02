import Median.Defs

/-! # The binary median dynamics (2-Choices) from a 60% majority

With two values, a node keeps its value unless both sampled nodes hold the other one. From a
configuration in which at least `3/5` of the nodes hold `true`, all nodes hold `true` within
`O(log n)` rounds with probability `1 - O(1/n)`.
-/

namespace Median
open Finset Dynamics

/-- Binary consensus from a 60% majority in `O(log n)` rounds, w.h.p. -/
theorem consensus_whp : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n Bool, (3 / 5 : ℝ) * n ≤ ones x →
      1 - C / n ≤ expList (Round n) ⌈C * Real.log n⌉₊
        (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  sorry

end Median
