import Epidemics.Revisited.Protocols
import Epidemics.Revisited.DoubleShrinking

/-! # Sharp upper bounds for push, pull and push–pull on `K_n` (EPI-8, instances)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorems 51, 52 and 53 (upper bounds): the expected rumor spreading time on
the complete graph is at most

* `log₂ n + ln n + O(1)` for push (the sharp bound of Frieze–Grimmett and Pittel, made explicit
  in expectation by Doerr and Künnemann);
* `log₂ n + log₂ ln n + O(1)` for pull;
* `log₃ n + log₂ ln n + O(1)` for push–pull.

Here the tails are exponential as well: overshooting these times by `r` rounds has probability
at most `A e^{-κ r}`. The start may be any nonempty set of informed nodes (the paper starts
from one node). The proofs instantiate the general theorems with the conditions verified in
`Protocols`: push by `spreading_upper_tail` (Theorems 21 and 31), pull and push–pull by
`spreading_upper_tail_double` (Theorems 21 and 43); the middle range of Lemma 19 is empty,
since both thresholds are `n/2`.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

/-- Theorem 51 (upper bound), tail form: push informs all nodes of `K_n` within
`⌈log₂ n⌉ + ⌈ln n⌉ + r` rounds, except with probability at most `A e^{-κ r}`. -/
theorem push_spreading_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        (push n).notYet n (⌈Real.logb 2 n⌉₊ + ⌈Real.log n⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  sorry

/-- Theorem 51 (upper bound): the expected time of push to inform all nodes of `K_n` is at
most `log₂ n + ln n + B`, stated for every partial sum of the tail series
`E[T] = ∑_t P[T > t]`. -/
theorem push_spreading_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, (push n).notYet n t S ≤ Real.logb 2 n + Real.log n + B := by
  sorry

/-- Theorem 52 (upper bound), tail form: pull informs all nodes of `K_n` within
`⌈log₂ n⌉ + ⌈log₂ ln n⌉ + r` rounds, except with probability at most `A e^{-κ r}`. -/
theorem pull_spreading_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        (pull n).notYet n (⌈Real.logb 2 n⌉₊ + ⌈Real.logb 2 (Real.log n)⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  sorry

/-- Theorem 52 (upper bound): the expected time of pull to inform all nodes of `K_n` is at
most `log₂ n + log₂ ln n + B`. -/
theorem pull_spreading_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, (pull n).notYet n t S ≤
          Real.logb 2 n + Real.logb 2 (Real.log n) + B := by
  sorry

/-- Theorem 53 (upper bound), tail form: push–pull informs all nodes of `K_n` within
`⌈log₃ n⌉ + ⌈log₂ ln n⌉ + r` rounds, except with probability at most `A e^{-κ r}`. -/
theorem pushPull_spreading_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        (pushPull n).notYet n (⌈Real.logb 3 n⌉₊ + ⌈Real.logb 2 (Real.log n)⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  sorry

/-- Theorem 53 (upper bound): the expected time of push–pull to inform all nodes of `K_n` is
at most `log₃ n + log₂ ln n + B`. -/
theorem pushPull_spreading_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, (pushPull n).notYet n t S ≤
          Real.logb 3 n + Real.logb 2 (Real.log n) + B := by
  sorry

end Epidemics.Revisited
