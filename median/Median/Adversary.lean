import Median.AdversaryDefs

/-! # Almost stable consensus against an adaptive adversary

Doerr, Goldberg, Minder, Sauerwald and Scheideler, *Stabilizing consensus with the power of two
choices* (2009 version: Theorems 2, 3 and 10; SPAA 2011: Theorem 1.1). Against an adversary that
knows the history and recolours at most `F ≤ √n / C` nodes per round, the median rule reaches
almost stable consensus within `O(log n)` rounds with high probability: from round
`T₀ = ⌈C log n⌉` on, all but `C (F + log n)` nodes hold the same value, and keep holding it for
`H` more rounds, except with probability at most `(C log n + H)/n²` per threshold (pair of
consecutive legal values).

* `binary_almost_stable_of_isAdvRun`, `binary_almost_stable`: two values (2-Choices), from any
  configuration;
* `median_almost_stable`: any number `m` of legal values, the adversary writing legal values
  only; the failure probability is at most `(m - 1)` times the binary one.
-/

namespace Median
open Finset Dynamics

variable {α : Type*} [LinearOrder α]

/-- A run against a bounded adversary is a perturbed run of the median rule. -/
theorem runAdv_isAdvRun {n : ℕ} {F : ℕ} {A : Adversary n α} (hA : A.Bounded F)
    (x : Config n α) : IsAdvRun F x (runAdv A x) := by
  sorry

/-- **2-Choices against an adaptive adversary, perturbed-run form.** From any binary
configuration `x`, for any run `P` of the median rule perturbed by at most `F ≤ √n / C`
recolourings per round, all but at most `C (F + log n)` nodes hold a common value `b` at every
time from `⌈C log n⌉` to `⌈C log n⌉ + H`, except with probability at most `(C log n + H)/n²`. -/
theorem binary_almost_stable_of_isAdvRun : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n],
    C ≤ Real.log n → ∀ F : ℕ, C * F ≤ √(n : ℝ) →
    ∀ (x : Config n Bool) (P : List (Round n) → Config n Bool), IsAdvRun F x P → ∀ H : ℕ,
      expList (Round n) (⌈C * Real.log n⌉₊ + H)
          (notAlmostStable (C * (F + Real.log n)) ⌈C * Real.log n⌉₊ H P)
        ≤ (C * Real.log n + H) / (n : ℝ) ^ 2 := by
  sorry

/-- **2-Choices against an adaptive adversary** (the paper's two-value case: Theorem 10 of the
2009 version, `O(√n)`-bounded adversary). From any binary configuration, against any adversary
that knows the history and recolours at most `F ≤ √n / C` nodes per round, all but at most
`C (F + log n)` nodes hold a common value `b` at every time from `⌈C log n⌉` to `⌈C log n⌉ + H`,
except with probability at most `(C log n + H)/n²`. -/
theorem binary_almost_stable : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ F : ℕ, C * F ≤ √(n : ℝ) → ∀ A : Adversary n Bool, A.Bounded F →
    ∀ (x : Config n Bool) (H : ℕ),
      expList (Round n) (⌈C * Real.log n⌉₊ + H)
          (notAlmostStable (C * (F + Real.log n)) ⌈C * Real.log n⌉₊ H (runAdv A x))
        ≤ (C * Real.log n + H) / (n : ℝ) ^ 2 := by
  sorry

/-- **Almost stable consensus against an adaptive adversary** (the paper's main theorem with
adversary: Theorem 1.1 of SPAA 2011, Theorems 2, 3 and 20 of the 2009 version). Let `S` be a set
of `m` legal values containing the values of the configuration `x` (in the paper, the initial
values; a larger `S` also covers a corruption before the first round). Against any adversary
that knows the history, recolours at most `F ≤ √n / C` nodes per round and only writes values
of `S`, all but at most `C (F + log n)` nodes hold a common value at every time from
`⌈C log n⌉` to `⌈C log n⌉ + H`, except with probability at most `(m - 1) (C log n + H)/n²`. -/
theorem median_almost_stable : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ F : ℕ, C * F ≤ √(n : ℝ) → ∀ (S : Finset α) (x : Config n α), (∀ v, x v ∈ S) →
    ∀ A : Adversary n α, A.Bounded F → A.UsesValues (S : Set α) → ∀ H : ℕ,
      expList (Round n) (⌈C * Real.log n⌉₊ + H)
          (notAlmostStable (C * (F + Real.log n)) ⌈C * Real.log n⌉₊ H (runAdv A x))
        ≤ ((S.card : ℝ) - 1) * ((C * Real.log n + H) / (n : ℝ) ^ 2) := by
  sorry

end Median
