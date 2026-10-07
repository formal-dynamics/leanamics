import Undecided.PluralityBasic

/-! # The binary undecided-state dynamics is the case `k = 2`

The states of the two-colour dynamics correspond to the binary opinions of `Undecided.Basic`
(`opEquiv`): undecided ↦ `u`, colour `0` ↦ `a`, colour `1` ↦ `b`. Under this bijection the update
rule of Table 1 becomes the binary update (`update_two`), so one round (`step_two`) and any
sequence of rounds (`foldl_two`) of the `k`-colour dynamics with `k = 2` are the binary dynamics,
and the counts agree (`count_two`).
-/

namespace Undecided.Plurality
open Finset

/-- The two-colour states are the binary opinions: undecided ↦ `u`, colour `0` ↦ `a`,
colour `1` ↦ `b`. -/
def opEquiv : Option (Fin 2) ≃ Op where
  toFun
    | none => .u
    | some i => if i = 0 then .a else .b
  invFun
    | .a => some 0
    | .b => some 1
    | .u => none
  left_inv := by decide
  right_inv := by decide

/-- Table 1 with two colours is the binary update rule of `Undecided.Basic`. -/
lemma update_two (s t : Option (Fin 2)) :
    Undecided.update (opEquiv s) (opEquiv t) = opEquiv (update s t) := by
  revert s t
  decide

variable {n : ℕ}

/-- One round of the two-colour dynamics is one round of the binary dynamics. -/
theorem step_two (x : Config n 2) (r : Fin n → Fin n) :
    Undecided.step (fun v => opEquiv (x v)) r = fun v => opEquiv (step x r v) := by
  funext v
  exact update_two (x v) (x (r v))

/-- **The binary model is the case `k = 2`**: running the two-colour dynamics and translating
the result by `opEquiv` is the same as running the binary dynamics of `Undecided.Basic` on the
translated configuration, for every sequence of rounds. -/
theorem foldl_two (x : Config n 2) (l : List (Fin n → Fin n)) :
    l.foldl Undecided.step (fun v => opEquiv (x v)) = fun v => opEquiv (l.foldl step x v) := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih =>
    simp only [List.foldl_cons]
    rw [step_two, ih]

/-- The counts of the two models agree under `opEquiv`. -/
theorem count_two (x : Config n 2) (o : Option (Fin 2)) :
    Undecided.count (fun v => opEquiv (x v)) (opEquiv o) = count x o := by
  unfold Undecided.count count
  congr 1
  ext v
  simp [opEquiv.apply_eq_iff_eq]

end Undecided.Plurality
