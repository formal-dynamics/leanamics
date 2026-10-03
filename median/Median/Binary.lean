import Median.Defs
import Median.BinaryAssembly

/-! # The binary median dynamics (2-Choices) from a vanishing bias

With two values, a node keeps its value unless both sampled nodes hold the other one. If the
`true` nodes outnumber the `false` ones by at least `C √(n log n)` (a fraction `1/2 + O(√(log n / n))`),
all nodes hold `true` within `O(log n)` rounds with probability `1 - O(1/n)` (Doerr, Goldberg,
Minder, Sauerwald and Scheideler, SPAA 2011, for two values).
-/

namespace Median
open Finset Dynamics

/-- Binary consensus from a gap of order `√(n log n)` in `O(log n)` rounds, w.h.p. -/
theorem consensus_whp : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n Bool, C * √(n * Real.log n) ≤ (ones x : ℝ) - (n - ones x) →
      1 - C / n ≤ expList (Round n) ⌈C * Real.log n⌉₊
        (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  refine ⟨128, by norm_num, ?_⟩
  intro n _ hL x hx
  exact binary_consensus hL x hx

end Median
