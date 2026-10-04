import Median.Basic
import Median.Binary

/-! # Consensus from any configuration (median dynamics)

The main theorem of Doerr, Goldberg, Minder, Sauerwald and Scheideler (SPAA 2011, Theorem 1 of the
full version): without an adversary, from **any** configuration, with any number of distinct
values, the median dynamics reaches consensus within `O(log n)` rounds with high probability.

The proof here goes through two values. The threshold reduction (the paper's Lemma 17, our
`threshold_run`) and a union bound over the at most `n - 1` thresholds (`consensus_of_binary`)
turn a failure bound for every binary configuration into one for every configuration; amplifying
a `C/n` failure bound to `≤ (C/n)³` by running three blocks (consensus absorbs) makes the union
bound affordable. What remains is the binary dynamics (2-Choices) from an arbitrary, possibly
perfectly balanced, start (`binary_any_start`, the paper's Lemmas 13-16 followed by
`consensus_whp`): symmetry breaking until the gap reaches order `√(n log n)`.
-/

namespace Median
open Finset Dynamics

/-- **2-Choices from any start.** From any binary configuration, all nodes agree after
`⌈C log n⌉` rounds except with probability at most `C/n`. -/
theorem binary_any_start : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n Bool,
      expList (Round n) ⌈C * Real.log n⌉₊ (fun l => notConsensus (run x l)) ≤ C / n := by
  sorry

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **Reduction to two values.** If every binary configuration fails to reach consensus within
`T` rounds with probability at most `ε`, then a configuration with `m` distinct values fails with
probability at most `(m - 1) ε`. -/
theorem consensus_of_binary [NeZero n] {T : ℕ} {ε : ℝ}
    (hbin : ∀ y : Config n Bool, expList (Round n) T (fun l => notConsensus (run y l)) ≤ ε)
    (x : Config n α) :
    expList (Round n) T (fun l => notConsensus (run x l)) ≤ (((univ.image x).card : ℝ) - 1) * ε := by
  sorry

/-- **Consensus from any configuration** (the paper's Theorem 1, no adversary). From any
configuration with values in a linear order, all nodes agree after `⌈C log n⌉` rounds except
with probability at most `C/n`. -/
theorem median_consensus_any : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n α,
      expList (Round n) ⌈C * Real.log n⌉₊ (fun l => notConsensus (run x l)) ≤ C / n := by
  sorry

end Median
