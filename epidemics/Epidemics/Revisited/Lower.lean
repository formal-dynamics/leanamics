import Epidemics.Revisited.LowerPush
import Epidemics.Revisited.LowerPull
import Epidemics.Revisited.LowerPushPull

/-! # Sharp lower bounds for push, pull and push–pull on `K_n` (EPI-8, instances)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorems 51, 52 and 53 (lower bounds): started from one informed node, the
rumor spreading time on the complete graph is at least

* `log₂ n + ln n - O(1)` for push;
* `log₂ n + log₂ ln n - O(1)` for pull;
* `log₃ n + log₂ ln n - O(1)` for push–pull,

in expectation, and finishing `r` rounds earlier than this has probability at most
`A e^{-κ r}`. Together with `push_spreading_tail`, `pull_spreading_tail` and
`pushPull_spreading_tail` (and their `_expect` forms) this determines the expected spreading
times up to additive constants.

The paper obtains the lower bounds from Theorems 27, 38 and 48 joined through Lemma 20, which
needs a major correction (see `Lemma20`). The proofs here take a direct route: the growth phase
by the first moment (`push_growth_lower`, `pull_growth_lower`, `pushPull_growth_lower`), the
final phase by a round-by-round lower envelope of the number of uninformed nodes
(`push_final_lower`, `pull_final_lower`, `pushPull_final_lower`), and the two joined by the
Markov property at a fixed time (`reach_add_le`), which needs no overshoot estimate.

`1 - P.notYet n t S` is the probability `P[T(|S|, n) ≤ t]` that all `n` nodes are informed
after `t` rounds. Expectations are sums of tails, `E[T] = ∑_{t ≥ 0} P[T > t]`, and every partial
sum with at least the stated number of terms bounds `E[T]` from below.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

/-- Theorem 51 (lower bound), tail form: started from one informed node, push informs all
nodes of `K_n` within `⌊log₂ n⌋ + ⌊ln n⌋ - r` rounds with probability at most `A e^{-κ r}`. -/
theorem push_spreading_lower_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.card = 1 → ∀ r : ℕ,
        1 - (push n).notYet n (⌊Real.logb 2 n⌋₊ + ⌊Real.log n⌋₊ - r) S
          ≤ A * Real.exp (-κ * r) := by
  sorry

/-- Theorem 51 (lower bound): started from one informed node, the expected time of push to
inform all nodes of `K_n` is at least `log₂ n + ln n - B`, stated for every partial sum of the
tail series `E[T] = ∑_t P[T > t]` with at least `log₂ n + ln n` terms. -/
theorem push_spreading_lower_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.card = 1 → ∀ R : ℕ, Real.logb 2 n + Real.log n ≤ R →
        Real.logb 2 n + Real.log n - B ≤ ∑ t ∈ range R, (push n).notYet n t S := by
  sorry

/-- Theorem 52 (lower bound), tail form: started from one informed node, pull informs all
nodes of `K_n` within `⌊log₂ n⌋ + ⌊log₂ ln n⌋ - r` rounds with probability at most
`A e^{-κ r}`. -/
theorem pull_spreading_lower_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.card = 1 → ∀ r : ℕ,
        1 - (pull n).notYet n (⌊Real.logb 2 n⌋₊ + ⌊Real.logb 2 (Real.log n)⌋₊ - r) S
          ≤ A * Real.exp (-κ * r) := by
  sorry

/-- Theorem 52 (lower bound): started from one informed node, the expected time of pull to
inform all nodes of `K_n` is at least `log₂ n + log₂ ln n - B`. -/
theorem pull_spreading_lower_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.card = 1 → ∀ R : ℕ,
        Real.logb 2 n + Real.logb 2 (Real.log n) ≤ R →
        Real.logb 2 n + Real.logb 2 (Real.log n) - B ≤ ∑ t ∈ range R, (pull n).notYet n t S := by
  sorry

/-- Theorem 53 (lower bound), tail form: started from one informed node, push–pull informs
all nodes of `K_n` within `⌊log₃ n⌋ + ⌊log₂ ln n⌋ - r` rounds with probability at most
`A e^{-κ r}`. -/
theorem pushPull_spreading_lower_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.card = 1 → ∀ r : ℕ,
        1 - (pushPull n).notYet n (⌊Real.logb 3 n⌋₊ + ⌊Real.logb 2 (Real.log n)⌋₊ - r) S
          ≤ A * Real.exp (-κ * r) := by
  sorry

/-- Theorem 53 (lower bound): started from one informed node, the expected time of push–pull
to inform all nodes of `K_n` is at least `log₃ n + log₂ ln n - B`. -/
theorem pushPull_spreading_lower_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.card = 1 → ∀ R : ℕ,
        Real.logb 3 n + Real.logb 2 (Real.log n) ≤ R →
        Real.logb 3 n + Real.logb 2 (Real.log n) - B ≤
          ∑ t ∈ range R, (pushPull n).notYet n t S := by
  sorry

end Epidemics.Revisited
