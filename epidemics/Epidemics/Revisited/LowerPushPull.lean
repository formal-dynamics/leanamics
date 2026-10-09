import Epidemics.Revisited.Protocols
import Epidemics.Revisited.LowerGeneric

/-! # Lower bound for push–pull on `K_n`: the two phases (EPI-8, Theorem 53)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorem 53 (lower bound): push–pull needs `log₃ n + log₂ ln n - O(1)`
rounds.

* **Growth** (the role of Theorem 27 with `γ = 2`): an uninformed node is informed with
  probability `1 - (1 - 1/n)^{|S|} (1 - |S|/n) ≤ 2 |S| / n`, so the expected number of informed
  nodes at most triples per round (`pushPull_expect_card_le`), and at least `m` nodes are
  informed after `t` rounds with probability at most `3^t |S| / m` (`pushPull_growth_lower`).
* **Final phase** (the role of Theorem 48 with `ℓ = 2`): with `u` uninformed nodes, each stays
  uninformed with probability `(u/n)(1 - 1/n)^{n-u} ≥ u / (e n)` (`pushPull_expect_uninformed`),
  and fewer than `u² / (2 e n)` stay uninformed with probability at most `4 e² n² / u³`
  (`pushPull_round_lower`). From at least `n / 2` uninformed nodes, informing everybody within
  `log₂ ln n - r₀` rounds has probability `O(n^{-1/2})` (`pushPull_final_lower`).
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

variable {n : ℕ}

/-- One round of push–pull at most triples the expected number of informed nodes:
`p_k = 1 - (1 - 1/n)^k (1 - k/n) ≤ 2k/n`, so `E|S'| ≤ 3|S|`. -/
theorem pushPull_expect_card_le (S : Finset (Fin n)) :
    ((pushPull n).K S).expect (fun T => (T.card : ℝ)) ≤ 3 * S.card := by
  have h := expect_card_le_of_informProb_le (pushPull n) S zero_le_two fun x hx => by
    have hn : (0 : ℝ) < n := by exact_mod_cast x.pos
    have hb := one_sub_one_sub_inv_pow_le x.pos S.card
    have hkn : S.card / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn]
      exact card_le_n S
    have hk0 : 0 ≤ S.card / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hn.le
    rw [pushPull_informProb hx]
    nlinarith
  linarith only [h]

/-- Expected number of uninformed nodes after one round of push–pull:
`E[n - |S'|] = (n - |S|)(1 - 1/n)^{|S|}(1 - |S| / n)`. -/
theorem pushPull_expect_uninformed (S : Finset (Fin n)) :
    ((pushPull n).K S).expect (fun T => (n : ℝ) - T.card) =
      ((n : ℝ) - S.card) * ((1 - 1 / (n : ℝ)) ^ S.card * (1 - S.card / (n : ℝ))) := by
  rw [expect_deficit]
  have heq : ∀ x ∈ (univ : Finset (Fin n)) \ S,
      1 - (pushPull n).informProb S x = (1 - 1 / (n : ℝ)) ^ S.card * (1 - S.card / (n : ℝ)) := by
    intro x hx
    rw [pushPull_informProb (mem_sdiff.mp hx).2]
    ring
  rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, card_compl_cast]

/-- Growth phase (Theorem 27 for push–pull, first-moment form): at least `m` nodes are
informed after `t` rounds with probability at most `3^t |S| / m`. -/
theorem pushPull_growth_lower {m : ℝ} (hm : 0 < m) (t : ℕ) (S : Finset (Fin n)) :
    1 - (pushPull n).notYet m t S ≤ 3 ^ t * S.card / m :=
  reach_le_of_expect_card_le (pushPull n) (by norm_num) pushPull_expect_card_le hm t S

/-- One round of the final phase (Lemma 49 for push–pull, `ℓ = 2`, `a = 1/e`): with
`u = n - |S|` uninformed nodes, fewer than `u² / (2 e n)` nodes stay uninformed with
probability at most `4 e² n² / u³`. -/
theorem pushPull_round_lower (S : Finset (Fin n)) :
    ((pushPull n).K S).prob (fun T => (n : ℝ) - T.card <
        ((n : ℝ) - S.card) ^ 2 / (2 * Real.exp 1 * n)) ≤
      4 * Real.exp 1 ^ 2 * (n : ℝ) ^ 2 / ((n : ℝ) - S.card) ^ 3 := by
  sorry

/-- Final phase (Theorem 48 for push–pull, `ℓ = 2`): from at least `n / 2` uninformed nodes,
push–pull informs all nodes within `log₂ ln n - r₀` rounds with probability at most
`C n^{-1/2}`. -/
theorem pushPull_final_lower :
    ∃ C : ℝ, ∃ r₀ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      ∀ t : ℕ, (t : ℝ) + r₀ ≤ Real.logb 2 (Real.log n) →
        1 - (pushPull n).notYet n t S ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  sorry

end Epidemics.Revisited
