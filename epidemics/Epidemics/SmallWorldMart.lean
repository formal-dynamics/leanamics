import Epidemics.SmallWorldDefs
import Dynamics.Adaptive

/-! # Adaptive observations: a finite supermartingale lemma (EPI-6, tools)

Tools for the exploration argument of [BCDPTZ22] (Appendix C), in finite probability.

* **Histories.** An adaptive process observes `obs h ω` after the history `h` of previous
  observations (`hist obs ω k` is the history after `k` steps, in the core's
  `Dynamics.Adaptive`). EPI-3's `queryAnswers` (one coin per step) is the special case
  `obs h ω = ω (next h)`; here the observations are arbitrary (blocks of coins, partners in a
  matching, …).
* **Supermartingale lemma** (`expect_prod_hist_le_one`, from the core): if every factor
  `f h b ≥ 0` has conditional expectation at most `1` given the history `h`, the product of the
  factors along the process has expectation at most `1`. With Markov's inequality this gives the
  tail bound of the exploration (`Epidemics.SmallWorldExplore`), in the role of the
  Galton–Watson comparison of the paper.
* **Coordinatewise combination of independent families** (the core's
  `Distribution.expect_expect_coord`, in `Dynamics.Independent`): if `x` and `y` are independent
  families, `fun i => φ i (x i) (y i)` is an independent family. This gives the independence of
  disjoint sets of coordinates (`Distribution.expect_mul_of_dep`) and, in
  `Epidemics.SmallWorldCollapse`, the law of the percolated `SWG(n, q)`.
* **Fresh observations of independent coordinates** (`expect_prod_hist_le_one_of_fresh`, from
  the core): if each observation reads coordinates not read before, the conditional expectation
  is the unconditional one, so it suffices that `E[f h (obs h ω)] ≤ 1` for every history `h`
  (principle of deferred decisions).
* **Blocks of coins**: the moment-generating function of the open coordinates of a block
  (`expect_exp_sum_open`) and the bound `1 - r + r eˣ ≤ exp (κ r x)`
  (`one_sub_add_mul_exp_le`).
-/

namespace Epidemics
open Finset Dynamics

/-! ### The supermartingale lemma along adaptive histories

The histories `hist`, the products `histProd` and the read sets `readSet` are the core's
(`Dynamics.Adaptive`); the two lemmas below are the core's `Distribution.expect_prod_hist_le_one`
and `Distribution.expect_prod_hist_le_one_of_fresh`. -/

section Supermartingale

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]

/-- **Supermartingale lemma.** If the factors `f h b ≥ 0` have conditional expectation at most
`1` given every history `h`, then the product of the factors along the first `m` steps of the
process has expectation at most `1`. -/
theorem expect_prod_hist_le_one (P : Distribution Ω) (obs : List β → Ω → β)
    (f : List β → β → ℝ) (hf0 : ∀ h b, 0 ≤ f h b)
    (hf : ∀ h : List β, P.expect (fun ω => if hist obs ω h.length = h then f h (obs h ω) else 0)
      ≤ P.expect (fun ω => if hist obs ω h.length = h then 1 else 0)) (m : ℕ) :
    P.expect (fun ω => histProd obs f ω 0 m) ≤ 1 :=
  Distribution.expect_prod_hist_le_one P obs f hf0 hf m

end Supermartingale

section Fresh

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β] [DecidableEq β]

/-- **Deferred decisions for adaptive observations of independent coordinates.** If every
observation `obs h ω` reads only the coordinates `supp h`, which were not read before along `h`,
and the factors satisfy `E[f h (obs h ω)] ≤ 1` for every history `h` (an unconditional
expectation), then the product of the factors along the process has expectation at most `1`. -/
theorem expect_prod_hist_le_one_of_fresh (P : ι → Distribution α)
    (obs : List β → (ι → α) → β) (supp : List β → Finset ι)
    (hobs : ∀ h ω ω', (∀ i ∈ supp h, ω i = ω' i) → obs h ω = obs h ω')
    (hfresh : ∀ h : List β, Disjoint (supp h) (readSet supp h))
    (f : List β → β → ℝ) (hf0 : ∀ h b, 0 ≤ f h b)
    (hf : ∀ h : List β, (Distribution.independent P).expect (fun ω => f h (obs h ω)) ≤ 1)
    (m : ℕ) :
    (Distribution.independent P).expect (fun ω => histProd obs f ω 0 m) ≤ 1 :=
  Distribution.expect_prod_hist_le_one_of_fresh P obs supp hobs hfresh f hf0 hf m

/-- The moment-generating function of the total weight of the open coordinates of a block:
`E[exp (∑_{e ∈ B open} a e)] = ∏_{e ∈ B} (1 - r e + r e · exp (a e))`. -/
lemma expect_exp_sum_open {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1) (B : Finset ι) (a : ι → ℝ) :
    (Distribution.independent fun e => Distribution.bernoulli (r e) (hr0 e) (hr1 e)).expect
      (fun ω => Real.exp (∑ e ∈ B.filter fun e => ω e = true, a e)) =
      ∏ e ∈ B, (1 - r e + r e * Real.exp (a e)) := by
  classical
  set g : ι → Bool → ℝ := fun e b =>
    if e ∈ B then (if b = true then Real.exp (a e) else 1) else 1 with hg
  have hpt (ω : ι → Bool) : Real.exp (∑ e ∈ B.filter fun e => ω e = true, a e) =
      ∏ e, g e (ω e) := by
    rw [Real.exp_sum, Finset.prod_filter, hg]
    simp only
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [show (fun ω : ι → Bool => Real.exp (∑ e ∈ B.filter fun e => ω e = true, a e)) =
    fun ω => ∏ e, g e (ω e) from funext hpt, Distribution.independent_expect_prod, hg]
  simp only
  rw [← Finset.prod_subset (Finset.subset_univ B) (fun e _ he => by simp [he])]
  refine Finset.prod_congr rfl fun e he => ?_
  simp only [he, if_true, Distribution.bernoulli_expect]
  simp
  ring

/-- For `0 ≤ x ≤ κ - 1 ≤ 1`: `1 - r + r eˣ ≤ exp (κ r x)`. -/
lemma one_sub_add_mul_exp_le {r x κ : ℝ} (hr : 0 ≤ r) (hx0 : 0 ≤ x) (hxκ : x ≤ κ - 1)
    (hκ : κ ≤ 2) : 1 - r + r * Real.exp x ≤ Real.exp (κ * r * x) := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; linarith
  have h1 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx1)).2
  have h2 : Real.exp x - 1 ≤ κ * x := by nlinarith
  have h3 : 1 + κ * r * x ≤ Real.exp (κ * r * x) := by
    linarith [Real.add_one_le_exp (κ * r * x)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hr]

end Fresh

end Epidemics
