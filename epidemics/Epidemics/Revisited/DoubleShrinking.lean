import Epidemics.Revisited.DoubleShrinkingDefs
import Epidemics.Revisited.Shrinking

/-! # Double exponential shrinking regime, upper bound, and the total spreading time (EPI-8)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorem 43 (Theorem 3 of the overview, upper bounds): under the upper double
exponential shrinking conditions (Definition 13) and fast finishing below `n^{1-α}` uninformed
nodes, once at most `g n` nodes are uninformed, all nodes are informed within
`log_ℓ ln n + O(1)` rounds in expectation, and overshooting this by `r` rounds has probability
`O(n^{A' - α' r})`.

The total spreading time: Theorem 21 (growth from one node to `f n` nodes), Lemma 19 (from
`f n` informed nodes to at most `g n` uninformed ones) and Theorem 43 combine to
`E[T(1, n)] ≤ log_{1+γ} n + log_ℓ ln n + O(1)` with an exponential tail, the way the paper
obtains the spreading times of the pull and push–pull protocols (Theorems 52 and 53).

As in `Growth` and `Shrinking`, the process may start from any admissible set of informed nodes,
and expected times are bounded through all finite partial sums of the tail series
`∑_t P[T > t]`.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

/-- Theorem 43, tail bound: under the upper double exponential shrinking conditions and fast
finishing, starting with at most `g n` uninformed nodes, some node is still uninformed after
`⌈log_ℓ ln n⌉ + r` rounds with probability at most `C n^{A' - α' r}`. The constants and the
threshold `N` depend only on `ℓ, a, c, g, α, τ`. -/
theorem double_shrinking_upper_tail {ℓ a c g α τ : ℝ} (hℓ : 1 < ℓ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hag : a * g ^ (ℓ - 1) < 1)
    (hτ : 0 < τ) :
    ∃ C A' α' : ℝ, 0 < α' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : RumorProcess n,
      P.UpperDoubleShrinking ℓ a c g α → P.FastFinishing α τ →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ r : ℕ,
        P.notYet n (⌈Real.logb ℓ (Real.log n)⌉₊ + r) S ≤ C * (n : ℝ) ^ (A' - α' * r) := by
  sorry

/-- Theorem 43, expectation: under the same conditions, `E[T(⌈(1 - g) n⌉, n)] ≤ log_ℓ ln n + B`,
stated for every partial sum of the tail series `E[T] = ∑_t P[T > t]`. -/
theorem double_shrinking_upper_expect {ℓ a c g α τ : ℝ} (hℓ : 1 < ℓ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hag : a * g ^ (ℓ - 1) < 1)
    (hτ : 0 < τ) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : RumorProcess n,
      P.UpperDoubleShrinking ℓ a c g α → P.FastFinishing α τ →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤ Real.logb ℓ (Real.log n) + B := by
  sorry

/-- Total spreading time with a double exponential shrinking regime, tail bound (Theorems 21
and 43 composed through Lemma 19): under the upper exponential growth conditions in `[1, f n[`
(with `γ` between two positive constants), the upper double exponential shrinking conditions
and fast finishing, and, in between, a probability at least `p > 0` for every uninformed node
to become informed, some node is still uninformed after
`⌈log_{1+γ} n⌉ + ⌈log_ℓ ln n⌉ + r` rounds with probability at most `A e^{-κ r}`. The constants
depend only on the parameters of the conditions. -/
theorem spreading_upper_tail_double {γlo γhi a b c f ℓ a' c' g α τ p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hℓ : 1 < ℓ) (ha' : 0 ≤ a') (hc' : 0 ≤ c') (hg0 : 0 < g)
    (hg1 : g ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hag : a' * g ^ (ℓ - 1) < 1) (hτ : 0 < τ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperDoubleShrinking ℓ a' c' g α → P.FastFinishing α τ →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        P.notYet n (⌈Real.logb (1 + γ) n⌉₊ + ⌈Real.logb ℓ (Real.log n)⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  sorry

/-- Total spreading time with a double exponential shrinking regime, expectation: under the
same conditions, `E[T(1, n)] ≤ log_{1+γ} n + log_ℓ ln n + B`, stated for every partial sum of
the tail series `E[T] = ∑_t P[T > t]`. -/
theorem spreading_upper_expect_double {γlo γhi a b c f ℓ a' c' g α τ p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hℓ : 1 < ℓ) (ha' : 0 ≤ a') (hc' : 0 ≤ c') (hg0 : 0 < g)
    (hg1 : g ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hag : a' * g ^ (ℓ - 1) < 1) (hτ : 0 < τ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperDoubleShrinking ℓ a' c' g α → P.FastFinishing α τ →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤
          Real.logb (1 + γ) n + Real.logb ℓ (Real.log n) + B := by
  sorry

end Epidemics.Revisited
