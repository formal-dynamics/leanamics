import Epidemics.Revisited.Protocols
import Epidemics.Revisited.DoubleShrinking

/-! # Sharp upper bounds for push, pull and push–pull on `K_n` (EPI-8, instances)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Theorems 51, 52 and 53 (upper bounds): the expected rumor spreading time on
the complete graph is at most

* `log₂ n + ln n + O(1)` for push (the sharp bound of Frieze–Grimmett and Pittel, made explicit
  in expectation by Doerr and Künnemann);
* `log₂ n + log₂ ln n + O(1)` for pull;
* `log₃ n + log₂ ln n + O(1)` for push–pull.

Here the tails are exponential as well: overshooting these times by `r` rounds has probability
at most `A e^{-κ r}`. The start may be any nonempty set of informed nodes (the paper starts
from one node). The proofs instantiate the general theorems with the conditions verified in
`Protocols`: push by `spreading_upper_tail` (Theorems 21 and 31), pull and push–pull by
`spreading_upper_tail_double` (Theorems 21 and 43); the middle range of Lemma 19 is empty,
since both thresholds are `n/2`.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess

/-- The side condition of the push shrinking conditions: `e^{-1} + (2/e)(1/2) = 2/e < 1`. -/
lemma exp_neg_one_add_lt : Real.exp (-1) + 2 / Real.exp 1 * (1 / 2) < 1 := by
  have he : 2 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  rw [Real.exp_neg, show 2 / Real.exp 1 * (1 / 2) = (Real.exp 1)⁻¹ by field_simp]
  have : (Real.exp 1)⁻¹ < 1 / 2 := by
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num
    exact he
  linarith

/-- The side condition of the pull and push–pull double shrinking conditions:
`1 · (1/2)^{2-1} < 1`. -/
lemma half_pow_lt_one : (1 : ℝ) * (1 / 2 : ℝ) ^ ((2 : ℝ) - 1) < 1 := by
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  norm_num

/-- With `f = g = 1/2` the middle range of Lemma 19 is empty. -/
lemma middle_empty {n : ℕ} (P : RumorProcess n) :
    ∀ S : Finset (Fin n), (1 / 2 : ℝ) * n ≤ S.card → (1 / 2 : ℝ) * n < (n : ℝ) - S.card →
      ∀ x ∉ S, (1 : ℝ) ≤ P.informProb S x := by
  intro S h1 h2
  exfalso
  linarith

/-- Theorem 51 (upper bound), tail form: push informs all nodes of `K_n` within
`⌈log₂ n⌉ + ⌈ln n⌉ + r` rounds, except with probability at most `A e^{-κ r}`. -/
theorem push_spreading_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        (push n).notYet n (⌈Real.logb 2 n⌉₊ + ⌈Real.log n⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  obtain ⟨A, κ, hκ, N, h⟩ := spreading_upper_tail (γlo := 1) (γhi := 1) (a := 1 / 2) (b := 0)
    (c := 0) (f := 1 / 2) (ρlo := 1) (ρhi := 1) (a' := 2 / Real.exp 1) (c' := 0) (g := 1 / 2)
    (p := 1) one_pos le_rfl (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
    (by norm_num) one_pos le_rfl (by positivity) le_rfl (by norm_num) (by norm_num)
    exp_neg_one_add_lt one_pos le_rfl
  refine ⟨A, κ, hκ, N, fun n hn S hS r => ?_⟩
  have := h n hn 1 le_rfl le_rfl 1 le_rfl le_rfl (push n) push_upperGrowth push_upperShrinking
    (middle_empty _) S hS r
  rwa [one_add_one_eq_two, div_one] at this

/-- Theorem 51 (upper bound): the expected time of push to inform all nodes of `K_n` is at
most `log₂ n + ln n + B`, stated for every partial sum of the tail series
`E[T] = ∑_t P[T > t]`. -/
theorem push_spreading_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, (push n).notYet n t S ≤ Real.logb 2 n + Real.log n + B := by
  obtain ⟨B, N, h⟩ := spreading_upper_expect (γlo := 1) (γhi := 1) (a := 1 / 2) (b := 0)
    (c := 0) (f := 1 / 2) (ρlo := 1) (ρhi := 1) (a' := 2 / Real.exp 1) (c' := 0) (g := 1 / 2)
    (p := 1) one_pos le_rfl (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
    (by norm_num) one_pos le_rfl (by positivity) le_rfl (by norm_num) (by norm_num)
    exp_neg_one_add_lt one_pos le_rfl
  refine ⟨B, N, fun n hn S hS R => ?_⟩
  have := h n hn 1 le_rfl le_rfl 1 le_rfl le_rfl (push n) push_upperGrowth push_upperShrinking
    (middle_empty _) S hS R
  rwa [one_add_one_eq_two, div_one] at this

/-- Theorem 52 (upper bound), tail form: pull informs all nodes of `K_n` within
`⌈log₂ n⌉ + ⌈log₂ ln n⌉ + r` rounds, except with probability at most `A e^{-κ r}`. -/
theorem pull_spreading_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        (pull n).notYet n (⌈Real.logb 2 n⌉₊ + ⌈Real.logb 2 (Real.log n)⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  obtain ⟨A, κ, hκ, N, h⟩ := spreading_upper_tail_double (γlo := 1) (γhi := 1) (a := 0)
    (b := 0) (c := 0) (f := 1 / 2) (ℓ := 2) (a' := 1) (c' := 0) (g := 1 / 2) (α := 1 / 2)
    (τ := 1 / 2) (p := 1) (by norm_num) le_rfl (by norm_num) le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) zero_le_one le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) half_pow_lt_one (by norm_num) one_pos le_rfl
  refine ⟨A, κ, hκ, N, fun n hn S hS r => ?_⟩
  have := h n hn 1 le_rfl le_rfl (pull n) pull_upperGrowth pull_upperDoubleShrinking
    pull_fastFinishing (middle_empty _) S hS r
  rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this

/-- Theorem 52 (upper bound): the expected time of pull to inform all nodes of `K_n` is at
most `log₂ n + log₂ ln n + B`. -/
theorem pull_spreading_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, (pull n).notYet n t S ≤
          Real.logb 2 n + Real.logb 2 (Real.log n) + B := by
  obtain ⟨B, N, h⟩ := spreading_upper_expect_double (γlo := 1) (γhi := 1) (a := 0)
    (b := 0) (c := 0) (f := 1 / 2) (ℓ := 2) (a' := 1) (c' := 0) (g := 1 / 2) (α := 1 / 2)
    (τ := 1 / 2) (p := 1) (by norm_num) le_rfl (by norm_num) le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) zero_le_one le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) half_pow_lt_one (by norm_num) one_pos le_rfl
  refine ⟨B, N, fun n hn S hS R => ?_⟩
  have := h n hn 1 le_rfl le_rfl (pull n) pull_upperGrowth pull_upperDoubleShrinking
    pull_fastFinishing (middle_empty _) S hS R
  rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this

/-- Theorem 53 (upper bound), tail form: push–pull informs all nodes of `K_n` within
`⌈log₃ n⌉ + ⌈log₂ ln n⌉ + r` rounds, except with probability at most `A e^{-κ r}`. -/
theorem pushPull_spreading_tail :
    ∃ A κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        (pushPull n).notYet n (⌈Real.logb 3 n⌉₊ + ⌈Real.logb 2 (Real.log n)⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  obtain ⟨A, κ, hκ, N, h⟩ := spreading_upper_tail_double (γlo := 2) (γhi := 2) (a := 3 / 4)
    (b := 0) (c := 0) (f := 1 / 2) (ℓ := 2) (a' := 1) (c' := 0) (g := 1 / 2) (α := 1 / 2)
    (τ := 1 / 2) (p := 1) (by norm_num) le_rfl (by norm_num) le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) zero_le_one le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) half_pow_lt_one (by norm_num) one_pos le_rfl
  refine ⟨A, κ, hκ, N, fun n hn S hS r => ?_⟩
  have := h n hn 2 le_rfl le_rfl (pushPull n) pushPull_upperGrowth pushPull_upperDoubleShrinking
    pushPull_fastFinishing (middle_empty _) S hS r
  rwa [show (1 : ℝ) + 2 = 3 by norm_num] at this

/-- Theorem 53 (upper bound): the expected time of push–pull to inform all nodes of `K_n` is
at most `log₃ n + log₂ ln n + B`. -/
theorem pushPull_spreading_expect :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, (pushPull n).notYet n t S ≤
          Real.logb 3 n + Real.logb 2 (Real.log n) + B := by
  obtain ⟨B, N, h⟩ := spreading_upper_expect_double (γlo := 2) (γhi := 2) (a := 3 / 4)
    (b := 0) (c := 0) (f := 1 / 2) (ℓ := 2) (a' := 1) (c' := 0) (g := 1 / 2) (α := 1 / 2)
    (τ := 1 / 2) (p := 1) (by norm_num) le_rfl (by norm_num) le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) zero_le_one le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) half_pow_lt_one (by norm_num) one_pos le_rfl
  refine ⟨B, N, fun n hn S hS R => ?_⟩
  have := h n hn 2 le_rfl le_rfl (pushPull n) pushPull_upperGrowth pushPull_upperDoubleShrinking
    pushPull_fastFinishing (middle_empty _) S hS R
  rwa [show (1 : ℝ) + 2 = 3 by norm_num] at this

end Epidemics.Revisited
