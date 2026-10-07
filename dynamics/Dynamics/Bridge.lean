import Dynamics.Distribution

/-!
# Bridges between the expectation APIs

Three finite expectation APIs are available to the packages of this repository:

* `Dynamics.avg f`, the uniform average `(∑ a, f a) / |α|` (zero on an empty type), and its
  iterate `Dynamics.expList α T F` over `T` i.i.d. uniform rounds (`Dynamics.Uniform`);
* `Dynamics.Distribution.expect`, the expectation under a weighted finite distribution, with the
  uniform law `Distribution.uniform` and the independent product `Distribution.independent`
  (`Dynamics.Distribution`);
* Mathlib's `Finset.expect`, written `𝔼 a, f a` (`Mathlib.Algebra.BigOperators.Expect`).

This file identifies them, so that results proved in one API apply in the others:

* `avg_eq_expect`: `avg f = 𝔼 a, f a`;
* `Distribution.uniform_expect` (in `Dynamics.Distribution`): `(uniform α).expect f = avg f`;
* `Distribution.independent_uniform_expect`: the independent product of uniform laws is the
  uniform law on the product space;
* `expList_eq_expect` and `expList_eq_independent_expect`: `expList α T F` is the expectation of
  `F` over `T` i.i.d. uniform draws, in Mathlib's and in the distribution form. They complete
  `expList_eq_avg_ofFn` (in `Dynamics.Equivalence`), the uniform-average form.
-/

namespace Dynamics

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- **The uniform average is Mathlib's finite expectation** (blueprint `def:avg`):
`avg f = 𝔼 a, f a`, i.e. `Finset.expect univ f`. Both sides vanish on an empty type. -/
theorem avg_eq_expect (f : α → ℝ) : avg f = 𝔼 a, f a := by
  rw [Fintype.expect_eq_sum_div_card]
  rfl

/-- **`T` i.i.d. uniform rounds, Mathlib form** (blueprint `lem:uniform-trajectory`):
`expList α T F` is the finite expectation of `F` over all length-`T` sequences of draws. -/
theorem expList_eq_expect (T : ℕ) (F : List α → ℝ) :
    expList α T F = 𝔼 ω : Fin T → α, F (List.ofFn ω) := by
  rw [expList_eq_avg_ofFn, avg_eq_expect]

namespace Distribution

/-- **The independent product of uniform laws is uniform** (blueprint `lem:uniform-agreement`,
`lem:weighted-product`):
the expectation under `independent fun _ : ι => uniform α` is the uniform average over
`ι → α`. -/
theorem independent_uniform_expect {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty α]
    (g : (ι → α) → ℝ) :
    (independent fun _ : ι => uniform α).expect g = avg g := by
  -- every point of `ι → α` has weight `|α|^(-|ι|) = |ι → α|⁻¹`
  have hw (x : ι → α) :
      (independent fun _ : ι => uniform α).weight x = (Fintype.card (ι → α) : ℝ)⁻¹ := by
    simp only [independent, uniform, prod_const, card_univ, Fintype.card_fun, inv_pow]
    push_cast
    rfl
  simp_rw [expect, hw, ← mul_sum]
  rw [avg, div_eq_inv_mul]

end Distribution

/-- **`T` i.i.d. uniform rounds, distribution form** (blueprint `lem:uniform-trajectory`):
`expList α T F` is the expectation of `F (List.ofFn ω)` under the independent product of `T`
uniform distributions on `α`. -/
theorem expList_eq_independent_expect [Nonempty α] (T : ℕ) (F : List α → ℝ) :
    expList α T F =
      (Distribution.independent fun _ : Fin T => Distribution.uniform α).expect
        (fun ω => F (List.ofFn ω)) := by
  rw [Distribution.independent_uniform_expect, expList_eq_avg_ofFn]

end Dynamics
