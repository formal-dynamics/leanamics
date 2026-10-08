import Epidemics.Revisited.Defs
import Dynamics.Trajectory

/-! # Exponential shrinking regime and Lemma 20 (EPI-8, definitions)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150).

* `UpperShrinking` is Definition 11 (the upper exponential shrinking conditions, Definition 4 of
  the overview), in the same form as `RumorProcess.UpperGrowth`: bounds for every state, here
  every state with at most `g n` uninformed nodes, for one value of `n`.
* `JumpsOver` and `RumorProcess.jumpProb` express the bad event of Lemma 20 (Lemma 5 of the
  overview): some round starts with fewer than `lo` informed nodes and ends with at least `hi`,
  so that the process jumps over `[lo, hi[`. The event depends on the whole path of the process,
  so its probability is an expectation over paths, `Dynamics.Kernel.trajectory`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

/-- Lemma 20's bad event for a path `S₀, S₁, …, S_t` of informed sets, given as a list: some
round starts with fewer than `lo` informed nodes and ends with at least `hi`, that is, the
process jumps over `[lo, hi[`. -/
def JumpsOver {n : ℕ} (lo hi : ℝ) (path : List (Finset (Fin n))) : Prop :=
  ∃ e ∈ path.zip path.tail, (e.1.card : ℝ) < lo ∧ hi ≤ e.2.card

namespace RumorProcess
variable {n : ℕ} (P : RumorProcess n)

/-- Probability that the process started from `S` jumps over `[lo, hi[` during its first `t`
rounds: the expectation, over the path `S = S₀, S₁, …, S_t` of `t` rounds, of the indicator of
`JumpsOver lo hi [S₀, …, S_t]`. (`Kernel.trajectory t S F` passes the history `[S₀, …, S_{t-1}]`
and the endpoint `S_t` to `F`.) -/
noncomputable def jumpProb (lo hi : ℝ) (t : ℕ) (S : Finset (Fin n)) : ℝ := by
  classical
  exact P.K.trajectory t S (fun h e => if JumpsOver lo hi (h ++ [e]) then 1 else 0)

/-- Definition 11 (upper exponential shrinking conditions), for one value of `n`.
In every round started from `S` with `u = n - |S| ≤ g n` uninformed nodes:
(i) every uninformed node stays uninformed with probability at most `e^{-ρ} + a u / n`, that is,
`1 - p_{n-u} ≤ e^{-ρ} + a u / n`, and
(ii) the covariance numbers satisfy `c_{n-u} ≤ c / u`.
The paper requires these for all large `n`, with `ρ = ρ_n` between two positive constants,
`0 < g < 1`, `a, c ≥ 0` and `e^{-ρ_n} + a g < 1`; the theorems quantify over `n` accordingly. -/
def UpperShrinking (ρ a c g : ℝ) : Prop :=
  ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n →
    (∀ x ∉ S, 1 - P.informProb S x ≤ Real.exp (-ρ) + a * (((n : ℝ) - S.card) / n)) ∧
    (∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c / ((n : ℝ) - S.card))

end RumorProcess
end Epidemics.Revisited
