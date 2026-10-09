import Epidemics.Revisited.Protocols
import Epidemics.Revisited.LowerGeneric

/-! # Lower bound for pull on `K_n`: the two phases (EPI-8, Theorem 52)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorem 52 (lower bound): pull needs `log₂ n + log₂ ln n - O(1)` rounds.

* **Growth** (the role of Theorem 27 with `γ = 1`): an uninformed node is informed with
  probability `|S| / n`, so the expected number of informed nodes at most doubles per round
  (`pull_expect_card_le`), and at least `m` nodes are informed after `t` rounds with probability
  at most `2^t |S| / m` (`pull_growth_lower`).
* **Final phase** (the role of Theorem 48 with `ℓ = 2`): with `u` uninformed nodes, each stays
  uninformed with probability `u / n` (`pull_expect_uninformed`), and fewer than `u² / (2n)`
  stay uninformed with probability at most `4 n² / u³` (`pull_round_lower`). From at least
  `n / 2` uninformed nodes, informing everybody within `log₂ ln n - r₀` rounds has probability
  `O(n^{-1/2})` (`pull_final_lower`).
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

variable {n : ℕ}

/-- One round of pull at most doubles the expected number of informed nodes:
`E|S'| = |S| + (n - |S|) |S| / n ≤ 2|S|`. -/
theorem pull_expect_card_le (S : Finset (Fin n)) :
    ((pull n).K S).expect (fun T => (T.card : ℝ)) ≤ 2 * S.card := by
  have h := expect_card_le_of_informProb_le (pull n) S zero_le_one fun x hx => by
    rw [pull_informProb hx, one_mul]
  linarith only [h]

/-- Expected number of uninformed nodes after one round of pull:
`E[n - |S'|] = (n - |S|)(1 - |S| / n)`. -/
theorem pull_expect_uninformed (S : Finset (Fin n)) :
    ((pull n).K S).expect (fun T => (n : ℝ) - T.card) =
      ((n : ℝ) - S.card) * (1 - S.card / (n : ℝ)) := by
  rw [expect_deficit]
  have heq : ∀ x ∈ (univ : Finset (Fin n)) \ S,
      1 - (pull n).informProb S x = 1 - S.card / (n : ℝ) := by
    intro x hx
    rw [pull_informProb (mem_sdiff.mp hx).2]
  rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, card_compl_cast]

/-- Growth phase (Theorem 27 for pull, first-moment form): at least `m` nodes are informed
after `t` rounds with probability at most `2^t |S| / m`. -/
theorem pull_growth_lower {m : ℝ} (hm : 0 < m) (t : ℕ) (S : Finset (Fin n)) :
    1 - (pull n).notYet m t S ≤ 2 ^ t * S.card / m :=
  reach_le_of_expect_card_le (pull n) zero_le_two pull_expect_card_le hm t S

/-- One round of the final phase (Lemma 49 for pull, `ℓ = 2`, `a = 1`): with `u = n - |S|`
uninformed nodes, fewer than `u² / (2n)` nodes stay uninformed with probability at most
`4 n² / u³`. -/
theorem pull_round_lower (S : Finset (Fin n)) :
    ((pull n).K S).prob (fun T => (n : ℝ) - T.card < ((n : ℝ) - S.card) ^ 2 / (2 * n)) ≤
      4 * (n : ℝ) ^ 2 / ((n : ℝ) - S.card) ^ 3 := by
  sorry

/-- Final phase (Theorem 48 for pull, `ℓ = 2`): from at least `n / 2` uninformed nodes, pull
informs all nodes within `log₂ ln n - r₀` rounds with probability at most `C n^{-1/2}`. -/
theorem pull_final_lower :
    ∃ C : ℝ, ∃ r₀ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      ∀ t : ℕ, (t : ℝ) + r₀ ≤ Real.logb 2 (Real.log n) →
        1 - (pull n).notYet n t S ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  sorry

end Epidemics.Revisited
