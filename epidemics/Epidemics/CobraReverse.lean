import Dynamics.Equivalence

/-! # Time reversal of i.i.d. uniform rounds (FND-6)

`T` i.i.d. uniform rounds have the same joint law read forwards or backwards:
`expList α T (F ∘ List.reverse) = expList α T F`. Through `Dynamics.expList_eq_avg_ofFn` this is
the invariance of the uniform average on `Fin T → α` under `ω ↦ ω ∘ Fin.rev`. Used for the
COBRA–BIPS duality (EPI-4), whose pathwise form reverses the sampled rounds.
-/

namespace Epidemics
open Dynamics

/-- Reversing the list of values of `f : Fin T → α` reads `f` along `Fin.rev`. -/
lemma reverse_ofFn {α : Type*} {T : ℕ} (f : Fin T → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_reverse, List.finRange_reverse,
    List.map_map]
  rfl

/-- Precomposition with `Fin.rev`, an involution of `Fin T → α`. -/
def revEquiv (α : Type*) (T : ℕ) : (Fin T → α) ≃ (Fin T → α) where
  toFun ω i := ω i.rev
  invFun ω i := ω i.rev
  left_inv ω := by funext i; simp
  right_inv ω := by funext i; simp

/-- **Time reversal of i.i.d. rounds** (roadmap FND-6): averaging a functional of the reversed
list of `T` i.i.d. uniform rounds is averaging the functional itself. -/
theorem expList_reverse {α : Type*} [Fintype α] (T : ℕ) (F : List α → ℝ) :
    expList α T (fun l => F l.reverse) = expList α T F := by
  rw [expList_eq_avg_ofFn, expList_eq_avg_ofFn]
  simp_rw [reverse_ofFn]
  exact avg_equiv (revEquiv α T) (fun ω => F (List.ofFn ω))

/-- `expList α T` only evaluates its functional on lists of length `T`. -/
lemma expList_congr_length {α : Type*} [Fintype α] (T : ℕ) {F G : List α → ℝ}
    (h : ∀ l, l.length = T → F l = G l) : expList α T F = expList α T G := by
  induction T generalizing F G with
  | zero => exact h [] rfl
  | succ T ih =>
    rw [expList_succ, expList_succ]
    exact congrArg avg (funext fun a => ih fun l hl => h (a :: l) (by simp [hl]))

end Epidemics
