import Epidemics.Revisited.ShrinkingDefs
import Epidemics.Revisited.Lemma20Aux

/-! # Not jumping over a linear interval (EPI-8, Lemma 20)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Lemma 20 (Lemma 5 of the overview): let `f, p ∈ ]0, 1[` and `c > 0`, and
suppose that `p_k ≤ p` and `c_k ≤ c / n` for every `k < f n`. Then there is `f' ∈ ]f, 1[` such
that with probability `1 - O(1/n)` the number of informed nodes lies in `[f n, f' n]` at the end
of some round.

The paper's proof bounds one round: by Lemma 9 and Chebyshev's inequality, for every
`f' ∈ ]f + p (1 - f), 1[` a round started with `k < f n` informed nodes ends with at least
`f' n` with probability at most `(p + c) / (n (f' - f - p (1 - f))²)`. This is
`overshoot_round`. The lemma's conclusion, that the whole process jumps over the interval with
probability `O(1/n)`, does not follow from it: the process may spend many rounds below `f n`
and have a chance to jump in each. (For instance, the process that from every `k < f n` informs
all nodes with probability `c / n` and otherwise no node satisfies the hypotheses, and jumps
from `1` to `n` with probability one.) `jumpProb_le` is the path statement that does follow,
by a union bound over the rounds: the probability of jumping over `[f n, f' n[` within `t`
rounds is at most `C / n` times the expected number of these rounds that start below `f n`,
that is, `O(E[T(|S|, f n)] / n)`.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

/-- Lemma 20, one round (the Chebyshev estimate in its proof): for `f' ∈ ]f + p (1 - f), 1[`,
a round started with `|S| < f n` informed nodes, in which every uninformed node becomes
informed with probability at most `p` and the covariance numbers are at most `c / n`, ends with
at least `f' n` informed nodes with probability at most `C / n`. -/
theorem overshoot_round {f p c f' : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hc : 0 < c) (hff' : f + p * (1 - f) < f') (hf'1 : f' < 1) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ P : RumorProcess n, ∀ S : Finset (Fin n), (S.card : ℝ) < f * n →
      (∀ x ∉ S, P.informProb S x ≤ p) → (∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c / n) →
      (P.K S).prob (fun S' => f' * n ≤ (S'.card : ℝ)) ≤ C / n := by
  have _ := hf0
  have _ := hf1
  have _ := hf'1
  exact overshoot_round_proof hp0.le hp1.le hc.le hff'

/-- Lemma 20, path form: if every round started with `1 ≤ |S| < f n` informed nodes informs
every uninformed node with probability at most `p` and has covariance numbers at most `c / n`,
then there is `f' ∈ ]f, 1[` such that the process started from a nonempty `S` jumps over
`[f n, f' n[` within its first `t` rounds with probability at most `C / n` times the expected
number of these rounds that start with fewer than `f n` informed nodes. -/
theorem jumpProb_le {f p c : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hc : 0 < c) :
    ∃ f' : ℝ, f < f' ∧ f' < 1 ∧ ∃ C : ℝ, ∀ n : ℕ, ∀ P : RumorProcess n,
      (∀ S : Finset (Fin n), S.Nonempty → (S.card : ℝ) < f * n →
        (∀ x ∉ S, P.informProb S x ≤ p) ∧ (∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c / n)) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ t : ℕ,
        P.jumpProb (f * n) (f' * n) t S ≤ C / n * ∑ i ∈ range t, P.notYet (f * n) i S := by
  have _ := hf0
  exact jumpProb_le_proof hf1 hp0 hp1 hc

end Epidemics.Revisited
