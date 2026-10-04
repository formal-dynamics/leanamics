import Epidemics.Revisited.Defs

/-! # Exponential growth regime, upper bound (EPI-8)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorem 1 (upper bounds), proved in Appendix B.2 as Theorem 21: under the
upper exponential growth conditions, a linear number `f n` of nodes is informed within
`log_{1+γ} n + O(1)` rounds in expectation, and overshooting this by `r` rounds has probability
at most `A e^{-α r}`. Also Lemma 9 (variance of the number of newly informed nodes) and
Lemma 19 (crossing a middle range where every uninformed node is informed with probability at
least `p`).

The paper starts from one informed node; here the process may start from any nonempty set,
which also covers the later phases when the regimes are composed.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

variable {n : ℕ}

/-- Lemma 9: the number of informed nodes after one round has variance at most its expected
increase plus `c (n - |S|)²`, when distinct uninformed nodes have covariance at most `c`. -/
theorem variance_card_le (P : RumorProcess n) (S : Finset (Fin n)) {c : ℝ} (hc : 0 ≤ c)
    (hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c) :
    (P.K S).expect (fun S' => ((S'.card : ℝ) - (P.K S).expect (fun S'' => (S''.card : ℝ))) ^ 2)
      ≤ (P.K S).expect (fun S' => (S'.card : ℝ)) - S.card + c * ((n : ℝ) - S.card) ^ 2 := by
  sorry

/-- Lemma 19 (i): if, while fewer than `m` nodes are informed (and at least `ℓ`), every
uninformed node becomes informed with probability at least `p` in each round, then
`P[T(ℓ, m) > r] ≤ (n - ℓ) / (n - m) · (1 - p)^r`. -/
theorem connect_tail (P : RumorProcess n) {ℓ : ℕ} {m p : ℝ} (hℓm : (ℓ : ℝ) < m) (hmn : m < n)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ S : Finset (Fin n), ℓ ≤ S.card → (S.card : ℝ) < m → ∀ x ∉ S, p ≤ P.informProb S x)
    (S : Finset (Fin n)) (hS : ℓ ≤ S.card) (r : ℕ) :
    P.notYet m r S ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 - p) ^ r := by
  sorry

/-- Lemma 19 (ii): under the same hypotheses with `p > 0`,
`E[T(ℓ, m)] ≤ (n - ℓ) / (n - m) · 1 / p`. -/
theorem connect_expect (P : RumorProcess n) {ℓ : ℕ} {m p : ℝ} (hℓm : (ℓ : ℝ) < m) (hmn : m < n)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hp : ∀ S : Finset (Fin n), ℓ ≤ S.card → (S.card : ℝ) < m → ∀ x ∉ S, p ≤ P.informProb S x)
    (S : Finset (Fin n)) (hS : ℓ ≤ S.card) (R : ℕ) :
    ∑ t ∈ range R, P.notYet m t S ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 / p) := by
  sorry

/-- Theorem 1 / Theorem 21, tail bound: under the upper exponential growth conditions, with
`γ` between two positive constants, fewer than `f n` nodes are informed after
`⌈log_{1+γ} n⌉ + r` rounds with probability at most `A e^{-α r}`. The constants `A, α` and the
threshold `N` depend only on `γlo, γhi, a, b, c, f`. -/
theorem growth_upper_tail {γlo γhi a b c f : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f) (hf1 : f < 1) (haf : a * f < 1) :
    ∃ A α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n, P.UpperGrowth γ a b c f →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        P.notYet (f * n) (⌈Real.logb (1 + γ) n⌉₊ + r) S ≤ A * Real.exp (-α * r) := by
  sorry

/-- Theorem 1 / Theorem 21, expectation: under the same conditions,
`E[T(1, f n)] ≤ log_{1+γ} n + B`, stated for every partial sum of the tail series
`E[T] = ∑_t P[T > t]`. -/
theorem growth_upper_expect {γlo γhi a b c f : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f) (hf1 : f < 1) (haf : a * f < 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n, P.UpperGrowth γ a b c f →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet (f * n) t S ≤ Real.logb (1 + γ) n + B := by
  sorry

end Epidemics.Revisited
