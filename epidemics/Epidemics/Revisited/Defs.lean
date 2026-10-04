import Dynamics.Kernel
import Mathlib

/-! # Homogeneous rumor-spreading processes (EPI-8, definitions)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), analyze rumor-spreading processes on `n` nodes, in which informed nodes stay
informed, through two numbers per round: the probability `p_k` that an uninformed node becomes
informed in a round starting with `k` informed nodes, and a bound `c_k` on the covariance of the
events that two distinct uninformed nodes become informed in that round.

Here a rumor-spreading process is a Markov kernel on the set of informed nodes under which no
informed node becomes uninformed. The paper's homogeneity (Definition 6: the probability that an
uninformed node becomes informed depends only on the number of informed nodes) is recorded by
`Homogeneous`. The upper bounds of this development do not need it: their hypotheses are bounds
for every state, which every homogeneous process satisfying the paper's conditions satisfies.

The rumor-spreading time `T(k, m)` of the paper (Definition 8) is handled through its tail:
since the process is monotone, `T(|S|, m) > t` holds exactly when fewer than `m` nodes are
informed after `t` rounds from `S`, whose probability is `notYet m t S`. Expectations are sums
of tails, `E[T] = ∑_{t ≥ 0} P[T > t]`, so bounds on all finite partial sums of `notYet` are
bounds on the expected spreading time.
-/

namespace Epidemics.Revisited
open Finset Dynamics

/-- A rumor-spreading process on `n` nodes: a Markov kernel on the set of informed nodes under
which no informed node becomes uninformed. -/
structure RumorProcess (n : ℕ) where
  /-- One round of the process, acting on the set of informed nodes. -/
  K : Kernel (Finset (Fin n))
  /-- Informed nodes stay informed. -/
  mono : ∀ S, (K S).prob (fun S' => S ⊆ S') = 1

namespace RumorProcess
variable {n : ℕ} (P : RumorProcess n)

/-- Probability that node `x` is informed after one round started from `S`. -/
noncomputable def informProb (S : Finset (Fin n)) (x : Fin n) : ℝ :=
  (P.K S).prob (fun S' => x ∈ S')

/-- Covariance of the indicators of the events that `x` and `y` are informed after one round
started from `S`. -/
noncomputable def cov (S : Finset (Fin n)) (x y : Fin n) : ℝ :=
  (P.K S).prob (fun S' => x ∈ S' ∧ y ∈ S') - P.informProb S x * P.informProb S y

/-- Definition 6 (homogeneity): in a round started from `S`, every uninformed node becomes
informed with the same probability `p |S|`, which depends only on the number of informed
nodes. -/
def Homogeneous (p : ℕ → ℝ) : Prop :=
  ∀ S x, x ∉ S → P.informProb S x = p S.card

/-- Probability that fewer than `m` nodes are informed after `t` rounds started from `S`, that
is, `P[T(|S|, m) > t]`. -/
noncomputable def notYet (m : ℝ) (t : ℕ) (S : Finset (Fin n)) : ℝ :=
  P.K.event (fun S' => (S'.card : ℝ) < m) t S

/-- Definition 9 (upper exponential growth conditions in `[1, f n[`), for one value of `n`.
In every round started from `k = |S|` informed nodes with `1 ≤ k < f n`:
(i) every uninformed node becomes informed with probability at least
`γ (k / n) (1 - a k / n - b / ln n)`, and
(ii) the covariance numbers satisfy `c_k ≤ c k / n²`.
The paper requires these for all large `n`, with `γ = γ_n` between two positive constants and
`a, b, c ≥ 0`, `0 < f < 1`, `a f < 1`; the theorems quantify over `n` accordingly. -/
def UpperGrowth (γ a b c f : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → (S.card : ℝ) < f * n →
    (∀ x ∉ S, γ * (S.card / n) * (1 - a * (S.card / n) - b / Real.log n) ≤ P.informProb S x) ∧
    (∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c * S.card / (n : ℝ) ^ 2)

end RumorProcess
end Epidemics.Revisited
