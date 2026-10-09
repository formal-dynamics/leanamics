import Epidemics.Revisited.Protocols
import Epidemics.Revisited.LowerGeneric
import Epidemics.Revisited.LowerRound

/-! # Lower bound for push on `K_n`: the two phases (EPI-8, Theorem 51)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorem 51 (lower bound): push needs `log₂ n + ln n - O(1)` rounds.

* **Growth** (the role of Theorem 27 with `γ = 1`): every informed node informs at most one new
  node per round, so the expected number of informed nodes at most doubles per round
  (`push_expect_card_le`), and at least `m` nodes are informed after `t` rounds with
  probability at most `2^t |S| / m` (`push_growth_lower`).
* **Final phase** (the role of Theorem 38 with `ρ = 1`): an uninformed node stays uninformed in
  a round with probability `(1 - 1/n)^{|S|} ≥ e^{-1}` (`push_expect_uninformed`), and the number
  `u` of uninformed nodes concentrates, so that it falls below `v / e - v^{3/4}` (any
  `4 ≤ v ≤ u`) in one round with probability at most `v^{-1/2}` (`push_round_lower`). Hence
  informing all of `u` uninformed nodes within `ln u - r` rounds has probability at most
  `C e^{-κ r}` (`push_final_lower`).
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

variable {n : ℕ}

/-- One round of push at most doubles the expected number of informed nodes:
`E|S'| = |S| + (n - |S|)(1 - (1 - 1/n)^{|S|}) ≤ 2|S|`. -/
theorem push_expect_card_le (S : Finset (Fin n)) :
    ((push n).K S).expect (fun T => (T.card : ℝ)) ≤ 2 * S.card := by
  have h := expect_card_le_of_informProb_le (push n) S zero_le_one fun x hx => by
    rw [push_informProb hx, one_mul]
    exact one_sub_one_sub_inv_pow_le x.pos S.card
  linarith only [h]

/-- Expected number of uninformed nodes after one round of push:
`E[n - |S'|] = (n - |S|)(1 - 1/n)^{|S|}`. -/
theorem push_expect_uninformed (S : Finset (Fin n)) :
    ((push n).K S).expect (fun T => (n : ℝ) - T.card) =
      ((n : ℝ) - S.card) * (1 - 1 / (n : ℝ)) ^ S.card := by
  rw [expect_deficit]
  have heq : ∀ x ∈ (univ : Finset (Fin n)) \ S,
      1 - (push n).informProb S x = (1 - 1 / (n : ℝ)) ^ S.card := by
    intro x hx
    rw [push_informProb (mem_sdiff.mp hx).2]
    ring
  rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, card_compl_cast]

/-- Growth phase (Theorem 27 for push, first-moment form): at least `m` nodes are informed
after `t` rounds with probability at most `2^t |S| / m`. -/
theorem push_growth_lower {m : ℝ} (hm : 0 < m) (t : ℕ) (S : Finset (Fin n)) :
    1 - (push n).notYet m t S ≤ 2 ^ t * S.card / m :=
  reach_le_of_expect_card_le (push n) zero_le_two push_expect_card_le hm t S

/-- One round of the final phase (Lemma 39 for push, with `A = 1`, `B = 1/4`), at any level
`v ∈ [4, u]`: with `u = n - |S|` uninformed nodes, fewer than `v / e - v^{3/4}` nodes stay
uninformed with probability at most `v^{-1/2}`. -/
theorem push_round_lower (S : Finset (Fin n)) {v : ℝ} (hv : 4 ≤ v)
    (hvu : v ≤ (n : ℝ) - S.card) :
    ((push n).K S).prob (fun T => (n : ℝ) - T.card < v / Real.exp 1 - v ^ (3 / 4 : ℝ)) ≤
      v ^ (-(1 / 2 : ℝ)) :=
  push_round_lower_proof S hv hvu

/-- Final phase (Theorem 38 for push, `ρ = 1`): from `u = n - |S|` uninformed nodes, push
informs all nodes within `t` rounds with probability at most `C e^{κ (t - ln u)}`, that is,
`P[T(|S|, n) ≤ ln u - r] ≤ C e^{-κ r}`. Uniform in `n` and in the starting set. -/
theorem push_final_lower :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (S : Finset (Fin n)) (t : ℕ),
      1 - (push n).notYet n t S ≤ C * Real.exp (κ * ((t : ℝ) - Real.log ((n : ℝ) - S.card))) := by
  sorry

end Epidemics.Revisited
