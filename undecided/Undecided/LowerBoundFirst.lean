import Undecided.LowerBoundBasic

/-! # The `Ω(md(c))` lower bound (UND-3): the first round (SODA 2015, Lemma 3)

[BCNPS15, Lemma 3] ("Rise of the undecided"): let `k = o(√(n / log n))`. From any initial
configuration `c̄` (without undecided nodes), after the first round, w.h.p.,
`n / (2R(c̄)²) ≤ C_m' ≤ 2n / R(c̄)²` and `n (1 - 2/Λ(c̄)) ≤ Q' ≤ n (1 - 1/(2Λ(c̄)))`, where `m` is
the plurality colour.

Here the upper bound is stated for **every** colour (`maxCount`), as needed for the lower bound
(no colour, not only the initial plurality, may grow fast); the expected size of colour `i`
after the first round is `c̄ᵢ² / n ≤ c̄_m² / n = n / R(c̄)²`.
"W.h.p." and `o(·)` are made explicit as everywhere in `undecided/`: one constant `C` with
`log n ≥ C`, `C k ≤ (n / log n)^{1/2}` and failure probability at most `C / n`. The probability
of missing a set `S` after `T` rounds from `x` is `miss S T x` (`PluralityStages.lean`).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- **Lemma 3 of [BCNPS15]** (first round, "rise of the undecided"). There is `C > 0` such
that, for every `n` with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/2}`, every
configuration `x` without undecided nodes and every plurality colour `m` of `x`, after one
round, with probability at least `1 - C / n`: the colour `m` has at least `n / (2R(x)²)` nodes,
**every** colour has at most `2n / R(x)²` nodes, and the number of undecided nodes lies in
`[n (1 - 2/Λ(x)), n (1 - 1/(2Λ(x)))]`. -/
theorem first_round : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 2) →
    ∀ (x : Config n k) (m : Fin k), count x none = 0 →
      (∀ i, count x (some i) ≤ count x (some m)) →
      miss {y | (n : ℝ) / (2 * ratioR x ^ 2) ≤ cnt y m ∧
          (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 ∧
          n * (1 - 2 / ratioLam x) ≤ und y ∧ und y ≤ n * (1 - 1 / (2 * ratioLam x))} 1 x
        ≤ C / n := by
  sorry

end Undecided.Plurality
