import Median.Basic
import Median.Binary

/-! # Many values: the middle value wins fast (median dynamics)

Doerr, Goldberg, Minder, Sauerwald and Scheideler (SPAA 2011; Theorem 21 of the full version)
show that from a uniformly random start with `m` values the median rule reaches consensus in
`O(log m + log log n)` rounds when `m` is odd, but needs `Θ(log n)` rounds when `m` is even.
With two values the dynamics is 2-Choices, and a balanced start needs `Θ(log n)` rounds; with
three equally supported values the middle one wins in `O(log log n)` rounds. This file pins the
deterministic core of the odd case:

* `binary_consensus_fast`: with two values, a gap `Δ ≥ C √(n log n)` gives consensus within
  `O(log (n/Δ) + log log n)` rounds (the gap grows geometrically until the minority is a constant
  fraction, which then shrinks quadratically, `m ↦ ≈ 3m²/n`);
* `median_consensus_fast`: with values in a linear order, a margin `Δ` on both sides of a value
  `v` gives consensus on `v` within `O(log (n/Δ) + log log n)` rounds;
* `odd_split_consensus`: `2k+1` values with equal support: the middle value wins within
  `O(log k + log log n)` rounds.
-/

namespace Median
open Finset Dynamics

/-- **Fast binary consensus from a large gap.** If the `true` nodes outnumber the `false` ones by
at least `Δ ≥ C √(n log n)`, all nodes hold `true` after `⌈C (log (n/Δ) + log log n)⌉` rounds with
probability at least `1 - C/n`. -/
theorem binary_consensus_fast : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n Bool) (Δ : ℝ), C * √(n * Real.log n) ≤ Δ →
      Δ ≤ (ones x : ℝ) - (n - ones x) →
      1 - C / n ≤ expList (Round n) ⌈C * (Real.log (n / Δ) + Real.log (Real.log n))⌉₊
        (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  sorry

variable {α : Type*} [LinearOrder α]

/-- **Consensus on a value with a margin on both sides.** If the nodes holding values `≥ v`
outnumber those holding values `< v`, and those holding values `≤ v` outnumber those holding
values `> v`, both by at least `Δ ≥ C √(n log n)`, then all nodes hold `v` after
`⌈C (log (n/Δ) + log log n)⌉` rounds with probability at least `1 - 2C/n`. -/
theorem median_consensus_fast : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n α) (v : α) (Δ : ℝ), C * √(n * Real.log n) ≤ Δ →
      Δ ≤ ((univ.filter fun u => v ≤ x u).card : ℝ) - (univ.filter fun u => x u < v).card →
      Δ ≤ ((univ.filter fun u => x u ≤ v).card : ℝ) - (univ.filter fun u => v < x u).card →
      1 - 2 * C / n ≤ expList (Round n) ⌈C * (Real.log (n / Δ) + Real.log (Real.log n))⌉₊
        (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) := by
  sorry

/-- **An odd number of equally supported values: the middle one wins fast.** If the nodes hold
`2k+1` distinct values, each held by `n/(2k+1)` nodes, and `C (2k+1) √(n log n) ≤ n`, then the
middle value `v` (exactly `k` values below it) is held by all nodes after
`⌈C (log (2k+1) + log log n)⌉` rounds with probability at least `1 - C/n`. -/
theorem odd_split_consensus : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n α) (k : ℕ), (univ.image x).card = 2 * k + 1 →
      (∀ a ∈ univ.image x, ((univ.filter fun u => x u = a).card : ℝ) = n / (2 * k + 1)) →
      C * (2 * k + 1) * √(n * Real.log n) ≤ n →
      ∀ v ∈ univ.image x, ((univ.image x).filter (· < v)).card = k →
        1 - C / n ≤ expList (Round n) ⌈C * (Real.log (2 * k + 1) + Real.log (Real.log n))⌉₊
          (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) := by
  sorry

end Median
