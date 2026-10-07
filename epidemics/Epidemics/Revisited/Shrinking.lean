import Epidemics.Revisited.ShrinkingDefs
import Epidemics.Revisited.Growth
import Epidemics.Revisited.ShrinkingTotal

/-! # Exponential shrinking regime, upper bound, and the total spreading time (EPI-8)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorem 2 (upper bounds), proved in Appendix B.4 as Theorem 31: under the
upper exponential shrinking conditions (Definition 11), once at most `g n` nodes are uninformed,
all nodes are informed within `(1/ρ) ln n + O(1)` rounds in expectation, and overshooting this
by `r` rounds has probability at most `A e^{-α r}`.

The total spreading time: the paper obtains the spreading times of concrete protocols
(Section 3.4 and Appendix C, e.g. Theorem 51 for the push protocol) by composing the regimes.
Here Theorem 21 (growth from one node to `f n` nodes), Lemma 19 (from `f n` informed nodes to at
most `g n` uninformed ones, when every uninformed node becomes informed with probability at
least `p` in between) and Theorem 31 combine to `E[T(1, n)] ≤ log_{1+γ} n + (1/ρ) ln n + O(1)`
with an exponential tail.

As in `Growth`, the process may start from any admissible set of informed nodes, and expected
times are bounded through all finite partial sums of the tail series `∑_t P[T > t]`.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

/-- Theorem 2 / Theorem 31, tail bound: under the upper exponential shrinking conditions, with
`ρ` between two positive constants and `e^{-ρlo} + a g < 1`, starting with at most `g n`
uninformed nodes, some node is still uninformed after `⌈(1/ρ) ln n⌉ + r` rounds with
probability at most `A e^{-α r}`. The constants `A, α` and the threshold `N` depend only on
`ρlo, ρhi, a, c, g`. -/
theorem shrinking_upper_tail {ρlo ρhi a c g : ℝ} (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hg0 : 0 < g) (hg1 : g < 1) (hag : Real.exp (-ρlo) + a * g < 1) :
    ∃ A α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi →
      ∀ P : RumorProcess n, P.UpperShrinking ρ a c g →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ r : ℕ,
        P.notYet n (⌈Real.log n / ρ⌉₊ + r) S ≤ A * Real.exp (-α * r) := by
  have _ := hg1
  exact shrinking_upper_tail_proof hρlo hρ ha hc hg0 hag

/-- Theorem 2 / Theorem 31, expectation: under the same conditions,
`E[T(n - ⌊g n⌋, n)] ≤ (1/ρ) ln n + B`, stated for every partial sum of the tail series
`E[T] = ∑_t P[T > t]`. -/
theorem shrinking_upper_expect {ρlo ρhi a c g : ℝ} (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hg0 : 0 < g) (hg1 : g < 1) (hag : Real.exp (-ρlo) + a * g < 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi →
      ∀ P : RumorProcess n, P.UpperShrinking ρ a c g →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤ Real.log n / ρ + B := by
  have _ := hg1
  exact shrinking_upper_expect_proof hρlo hρ ha hc hg0 hag

/-- Total spreading time, tail bound (Theorems 21 and 31 composed through Lemma 19): under the
upper exponential growth conditions in `[1, f n[` (with `γ` between two positive constants), the
upper exponential shrinking conditions for at most `g n` uninformed nodes (with `ρ` between two
positive constants), and, in between, a probability at least `p > 0` for every uninformed node
to become informed, some node is still uninformed after
`⌈log_{1+γ} n⌉ + ⌈(1/ρ) ln n⌉ + r` rounds with probability at most `A e^{-α r}`. The constants
depend only on the parameters of the conditions. -/
theorem spreading_upper_tail {γlo γhi a b c f ρlo ρhi a' c' g p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi) (ha' : 0 ≤ a')
    (hc' : 0 ≤ c') (hg0 : 0 < g) (hg1 : g < 1) (hag : Real.exp (-ρlo) + a' * g < 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ A α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi → ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperShrinking ρ a' c' g →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        P.notYet n (⌈Real.logb (1 + γ) n⌉₊ + ⌈Real.log n / ρ⌉₊ + r) S
          ≤ A * Real.exp (-α * r) := by
  have _ := hg1
  obtain ⟨A, α, -, hα, N, h⟩ := spreading_upper_tail_proof hγlo hγ ha hb hc hf0 hf1 haf hρlo hρ
    ha' hc' hg0 hag hp0 hp1
  exact ⟨A, α, hα, N, h⟩

/-- Total spreading time, expectation: under the same conditions,
`E[T(1, n)] ≤ log_{1+γ} n + (1/ρ) ln n + B`, stated for every partial sum of the tail series
`E[T] = ∑_t P[T > t]`. -/
theorem spreading_upper_expect {γlo γhi a b c f ρlo ρhi a' c' g p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi) (ha' : 0 ≤ a')
    (hc' : 0 ≤ c') (hg0 : 0 < g) (hg1 : g < 1) (hag : Real.exp (-ρlo) + a' * g < 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi → ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperShrinking ρ a' c' g →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤ Real.logb (1 + γ) n + Real.log n / ρ + B := by
  have _ := hg1
  exact spreading_upper_expect_proof hγlo hγ ha hb hc hf0 hf1 haf hρlo hρ ha' hc' hg0 hag hp0 hp1

end Epidemics.Revisited
