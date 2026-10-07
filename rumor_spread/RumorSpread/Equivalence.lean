import Dynamics.Bridge

/-!
# Faithfulness of the transition-operator expectation

`expList α T F` was *defined* by recursion (average out the first draw, then
recurse).  This file records that it equals the textbook object: the uniform
average of `F` over **all** length-`T` sequences of draws, i.e. over the
product probability space `Fin T → α` of `T` i.i.d. uniform rounds.

The expectation layer (`avg`, `expList`) is the shared one of `Dynamics.Uniform`, and so is the
proof (`Dynamics.expList_eq_avg_ofFn`); the statement is kept under this name for the
blueprint's theorem "Faithfulness of the model". `Dynamics.expList_eq_expect` and
`Dynamics.expList_eq_independent_expect` give the same identity with Mathlib's `Finset.expect`
and with the independent product of uniform distributions.
-/

namespace RumorPush

open Dynamics

variable {α : Type*} [Fintype α]

/-- **Faithfulness of the model**: the recursive trajectory expectation `expList α T F` is the
uniform average of `F` over the product space `Fin T → α` of `T` i.i.d. rounds. -/
lemma expList_eq_avg_ofFn (T : ℕ) (F : List α → ℝ) :
    expList α T F = avg (fun ω : Fin T → α => F (List.ofFn ω)) :=
  Dynamics.expList_eq_avg_ofFn T F

end RumorPush
