import Epidemics.SmallWorldDefs
import Dynamics.Adaptive

/-! # Adaptive observations: a finite supermartingale lemma (EPI-6, tools)

Tools for the exploration argument of [BCDPTZ22] (Appendix C), in finite probability.

* **Histories.** An adaptive process observes `obs h ω` after the history `h` of previous
  observations (`hist obs ω k` is the history after `k` steps, in the core's
  `Dynamics.Adaptive`). EPI-3's `queryAnswers` (one coin per step) is the special case
  `obs h ω = ω (next h)`; here the observations are arbitrary (blocks of coins, partners in a
  matching, …).
* **Supermartingale lemma** (the core's `Distribution.expect_prod_hist_le_one`): if every factor
  `f h b ≥ 0` has conditional expectation at most `1` given the history `h`, the product of the
  factors along the process has expectation at most `1`. With Markov's inequality this gives the
  tail bound of the exploration (`Epidemics.SmallWorldExplore`), in the role of the
  Galton–Watson comparison of the paper.
* **Coordinatewise combination of independent families** (the core's
  `Distribution.expect_expect_coord`, in `Dynamics.Independent`): if `x` and `y` are independent
  families, `fun i => φ i (x i) (y i)` is an independent family. This gives the independence of
  disjoint sets of coordinates (`Distribution.expect_mul_of_dep`) and, in
  `Epidemics.SmallWorldCollapse`, the law of the percolated `SWG(n, q)`.
* **Fresh observations of independent coordinates** (the core's
  `Distribution.expect_prod_hist_le_one_of_fresh`): if each observation reads coordinates not
  read before, the conditional expectation is the unconditional one, so it suffices that
  `E[f h (obs h ω)] ≤ 1` for every history `h` (principle of deferred decisions).
* **Blocks of coins**: the moment-generating function of the open coordinates of a block (the
  core's `Distribution.independent_bernoulli_expect_exp_sum`, in `Dynamics.Chernoff`) and the
  bound `1 - r + r eˣ ≤ exp (κ r x)` (`one_sub_add_mul_exp_le`).
-/

namespace Epidemics
open Finset Dynamics

/-- For `0 ≤ x ≤ κ - 1 ≤ 1`: `1 - r + r eˣ ≤ exp (κ r x)`. -/
lemma one_sub_add_mul_exp_le {r x κ : ℝ} (hr : 0 ≤ r) (hx0 : 0 ≤ x) (hxκ : x ≤ κ - 1)
    (hκ : κ ≤ 2) : 1 - r + r * Real.exp x ≤ Real.exp (κ * r * x) := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; linarith
  have h1 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx1)).2
  have h2 : Real.exp x - 1 ≤ κ * x := by nlinarith
  have h3 : 1 + κ * r * x ≤ Real.exp (κ * r * x) := by
    linarith [Real.add_one_le_exp (κ * r * x)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hr]

end Epidemics
