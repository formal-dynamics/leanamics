import Epidemics.Revisited.Defs

/-! # Double exponential shrinking regime (EPI-8, definitions)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Appendix B.6: when every uninformed node stays uninformed with probability
proportional to a power `ℓ - 1 > 0` of the fraction of uninformed nodes, this fraction is
roughly raised to the power `ℓ` in each round, and the last `g n` nodes are informed within
`log_ℓ ln n + O(1)` rounds. This regime occurs in protocols with pull operations.

* `UpperDoubleShrinking` is Definition 13 (the upper double exponential shrinking conditions),
  in the same form as `RumorProcess.UpperShrinking`: bounds for every state with between
  `n^{1-α}` and `g n` uninformed nodes, for one value of `n`.
* `FastFinishing` is the second hypothesis of Theorem 43: below `n^{1-α}` uninformed nodes,
  every uninformed node stays uninformed with probability at most `n^{-τ}`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

namespace RumorProcess
variable {n : ℕ} (P : RumorProcess n)

/-- Definition 13 (upper double exponential shrinking conditions), for one value of `n`.
In every round started from `S` with `u = n - |S|` uninformed nodes, `n^{1-α} ≤ u ≤ g n`:
(i) every uninformed node stays uninformed with probability at most `a (u / n)^{ℓ-1}`, that is,
`1 - p_{n-u} ≤ a (u/n)^{ℓ-1}`, and
(ii) the covariance numbers satisfy `c_{n-u} ≤ c n / u²`.
The paper requires these for all large `n`, with `g, α ∈ [0, 1]`, `ℓ > 1`, `a, c ≥ 0` and
`a g^{ℓ-1} < 1`; the theorems quantify over `n` accordingly. -/
def UpperDoubleShrinking (ℓ a c g α : ℝ) : Prop :=
  ∀ S : Finset (Fin n), (n : ℝ) ^ (1 - α) ≤ (n : ℝ) - S.card → (n : ℝ) - S.card ≤ g * n →
    (∀ x ∉ S, 1 - P.informProb S x ≤ a * (((n : ℝ) - S.card) / n) ^ (ℓ - 1)) ∧
    (∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c * n / ((n : ℝ) - S.card) ^ 2)

/-- The second hypothesis of Theorem 43, for one value of `n`: in every round started with at
most `n^{1-α}` uninformed nodes, every uninformed node stays uninformed with probability at
most `n^{-τ}`. -/
def FastFinishing (α τ : ℝ) : Prop :=
  ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ (n : ℝ) ^ (1 - α) →
    ∀ x ∉ S, 1 - P.informProb S x ≤ (n : ℝ) ^ (-τ)

end RumorProcess
end Epidemics.Revisited
