import ThreeMajority.ManyOpinionsExpect
import Dynamics.Rounds

/-!
# The dropping stage (BCNPT16, Lemmas 3.4 and 3.5; roadmap MAJ-12 (a))

Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many opinions*,
SODA 2016, arXiv:1508.06782 (BCNPT16 below), Section 3. Once a colour `a` is below
`n/j − 16 √(j n log n)` agents in a configuration with at most `j` colours, Lemma 2.1 makes it
shrink geometrically: its gap to the average `n/j` grows by a factor `1 + 1/(4j)` per round, and
below `n/(2j)` the support itself shrinks by a factor `1 − 1/(2j)`.

* `dropping_stage1`: **Lemma 3.4**. Within `O(j log n)` rounds the support of `a` is
  `O(j² log n)`, with probability at least `1 − 1/n` (at every time `t` with
  `C j log n ≤ t ≤ n`).
* `dropping_stage2`: **Lemma 3.5**. From at most `n/(2j)` agents, colour `a` dies within
  `O(j log n)` rounds with probability at least `1/2`.

Both assume `C j³ log n ≤ n`, implied by the paper's `j ≤ n^{1/3 − ε}` for large `n`. The proof of
Lemma 3.4 needs a minor correction: from the paper's threshold `n/j − √(j n log n)` the one-round
Chernoff bound (Appendix B, Equation (7)) only gives failure probability `n^{-1/12}`, still at least
`n^{-1/10}` during the first `j/10` rounds, so the iterated union bound exceeds `1` as soon as
`j ≥ 20 n^{1/10}`, and the same happens near the floor `j² log n`. With the threshold
`n/j − 16 √(j n log n)` and the floor `C j² log n` for a large `C` the failure is at most `n^{-5}`
per round.
-/

namespace ThreeMajority

open Finset Dynamics

/-- **Lemma 3.4** (BCNPT16, dropping stage 1): there is `C` such that, for `j ≥ 2` with
`C j³ log n ≤ n`, from every configuration `x` with at most `j` colours and every colour `a` with
at most `n/j − 16 √(j n log n)` agents, at every time `t` with `C j log n ≤ t ≤ n` colour `a` has
more than `C j² log n` agents with probability at most `1/n`. -/
theorem dropping_stage1 :
    ∃ C : ℝ, ∀ (n j : ℕ) (x : Fin n → Fin n) (a : Fin n), 2 ≤ j →
      C * (j : ℝ) ^ 3 * Real.log n ≤ n → numColours x ≤ j →
      (colourCount x a : ℝ) ≤ n / j - 16 * √(j * n * Real.log n) →
      ∀ t : ℕ, C * j * Real.log n ≤ t → t ≤ n →
        expList (Tgt3 n) t
          (fun l => if C * j ^ 2 * Real.log n < colourCount (runCol x l) a then 1 else 0) ≤
            1 / n := by
  sorry

/-- **Lemma 3.5** (BCNPT16, dropping stage 2): there is `C` such that, for `j ≥ 2` with
`C j³ log n ≤ n`, from every configuration `x` with at most `j` colours and every colour `a` with
at most `n/(2j)` agents, colour `a` has died after any `t ≥ C j log n` rounds with probability at
least `1/2`. -/
theorem dropping_stage2 :
    ∃ C : ℝ, ∀ (n j : ℕ) (x : Fin n → Fin n) (a : Fin n), 2 ≤ j →
      C * (j : ℝ) ^ 3 * Real.log n ≤ n → numColours x ≤ j →
      (colourCount x a : ℝ) ≤ n / (2 * j) →
      ∀ t : ℕ, C * j * Real.log n ≤ t →
        1 / 2 ≤ expList (Tgt3 n) t
          (fun l => if colourCount (runCol x l) a = 0 then 1 else 0) := by
  sorry

end ThreeMajority
