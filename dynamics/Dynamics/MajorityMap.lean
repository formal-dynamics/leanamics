import Dynamics.Binomial

/-!
# The majority map and the recursions of conformist transmission and of Galam's rule

The probability that the majority of three independent samples, each of type `1` with
probability `p`, is of type `1` is `p³ + 3p²(1 - p) = 3p² - 2p³`: the **majority map**
(`majorityMap`). It is the expected one-round map of binary 3-Majority and of 2-Choices (the
binary median rule), a mean field in the sense of `Dynamics.Kernel.MeanField` (packages
`plurality` and `median`), and the deterministic recursion of two models of other fields (rows
`three-majority` and `two-choices` of the cross-field dictionary):

* **Conformist transmission** (Boyd and Richerson 1985, Eq. 7.1). A naive individual samples three
  models and acquires a variant held by 3, 2, 1, 0 of them with probability `1`, `2/3 + D/3`,
  `1/3 - D/3`, `0` (`conformistTable`). If the models are independent and each holds the variant
  with probability `p`, the variant is acquired with probability `p + D p (1 - p)(2p - 1)`
  (`conformistMap`, `conformistMap_eq_expect`). The table adopts the majority of the three models
  with probability `D` and copies one of them, drawn uniformly, otherwise (`conformistTable_eq`),
  so `D = 0` is unbiased transmission (`conformistMap_zero`) and `D = 1` gives the majority map
  (`conformistMap_one`).
* **Galam's majority rule with groups of three** (Galam 2002, Eq. 4 with `a_3 = 1`): the
  proportion of an opinion follows `P ↦ P³ + 3P²(1 - P)` (`galamMap`), the majority map
  (`galamMap_eq`).
-/

namespace Dynamics
open Finset

/-! ### The majority map -/

/-- The **majority map** `p ↦ 3p² - 2p³`: the probability that the majority of three independent
samples is of type `1` when each sample is of type `1` with probability `p`. -/
def majorityMap (p : ℝ) : ℝ := 3 * p ^ 2 - 2 * p ^ 3

/-- The majority of three independent samples: the map is the probability that at least two of
three independent coins of bias `p` show heads. -/
theorem majorityMap_eq_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (Distribution.binomial 3 p h0 h1).prob (fun j => 2 ≤ (j : ℕ)) = majorityMap p := by
  rw [Distribution.prob_eq_expect]
  simp only [Distribution.expect, Distribution.binomial]
  simp [Fin.sum_univ_succ, Nat.choose, majorityMap]
  ring

theorem majorityMap_nonneg {p : ℝ} (h1 : p ≤ 1) : 0 ≤ majorityMap p := by
  unfold majorityMap
  nlinarith [mul_nonneg (sq_nonneg p) (by linarith : (0 : ℝ) ≤ 3 - 2 * p)]

theorem majorityMap_le_one {p : ℝ} (h0 : 0 ≤ p) : majorityMap p ≤ 1 := by
  unfold majorityMap
  nlinarith [mul_nonneg (sq_nonneg (1 - p)) (by linarith : (0 : ℝ) ≤ 1 + 2 * p)]

/-- The two types are symmetric: the other type follows the same map. -/
theorem majorityMap_one_sub (p : ℝ) : majorityMap (1 - p) = 1 - majorityMap p := by
  unfold majorityMap
  ring

/-! ### Conformist transmission -/

/-- **Conformist transmission** (Boyd and Richerson 1985, Eq. 7.1): the frequency `p` of a
variant becomes `p + D p (1 - p)(2p - 1)` in the next generation, `D` measuring the strength of
conformism. -/
def conformistMap (D p : ℝ) : ℝ := p + D * p * (1 - p) * (2 * p - 1)

/-- Boyd and Richerson's table of conformist transmission: a naive individual whose three models
include `j` holders of the variant acquires it with probability `0`, `1/3 - D/3`, `2/3 + D/3`, `1`
for `j = 0, 1, 2, 3`. -/
noncomputable def conformistTable (D : ℝ) : Fin 4 → ℝ := ![0, 1 / 3 - D / 3, 2 / 3 + D / 3, 1]

/-- **The table adopts the majority with probability `D` and otherwise copies one model.** With `j`
holders among the three models, the acquisition probability is `D` times the indicator that they
are a majority plus `1 - D` times the probability `j/3` that a model drawn uniformly among the
three holds the variant. -/
theorem conformistTable_eq (D : ℝ) (j : Fin 4) :
    conformistTable D j = D * (if 2 ≤ (j : ℕ) then 1 else 0) + (1 - D) * ((j : ℕ) / 3) := by
  fin_cases j <;> simp [conformistTable] <;> ring

/-- **Boyd and Richerson's Eq. 7.1 from the table.** If the three models are independent and
each holds the variant with probability `p`, so that the number of holders among them has the law
`Bin(3, p)`, the variant is acquired with probability `p + D p (1 - p)(2p - 1)`. -/
theorem conformistMap_eq_expect (D p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (Distribution.binomial 3 p h0 h1).expect (conformistTable D) = conformistMap D p := by
  simp only [Distribution.expect, Distribution.binomial]
  simp [Fin.sum_univ_succ, Nat.choose, conformistTable, conformistMap]
  ring

/-- Conformist transmission is a mixture of unbiased transmission and of the majority map. -/
theorem conformistMap_eq_mix (D p : ℝ) :
    conformistMap D p = (1 - D) * p + D * majorityMap p := by
  unfold conformistMap majorityMap
  ring

/-- **With `D = 1`, conformist transmission is the majority map** `p ↦ 3p² - 2p³`. -/
theorem conformistMap_one (p : ℝ) : conformistMap 1 p = majorityMap p := by
  rw [conformistMap_eq_mix]
  ring

/-- With `D = 0`, conformist transmission is unbiased: the frequency is unchanged. -/
theorem conformistMap_zero (p : ℝ) : conformistMap 0 p = p := by
  rw [conformistMap_eq_mix]
  ring

theorem conformistMap_nonneg {D p : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ conformistMap D p := by
  rw [conformistMap_eq_mix]
  have := majorityMap_nonneg h1
  nlinarith

theorem conformistMap_le_one {D p : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    conformistMap D p ≤ 1 := by
  rw [conformistMap_eq_mix]
  have := majorityMap_le_one h0
  nlinarith

/-! ### Galam's majority rule -/

/-- **Galam's majority rule with groups of three** (Galam 2002, Eq. 4 with `a_3 = 1`): every group
of three adopts its majority, and the proportion `P` of an opinion becomes `P³ + 3P²(1 - P)`. -/
def galamMap (P : ℝ) : ℝ := P ^ 3 + 3 * P ^ 2 * (1 - P)

/-- **Galam's map is the majority map.** -/
theorem galamMap_eq : galamMap = majorityMap := by
  funext P
  unfold galamMap majorityMap
  ring

end Dynamics
