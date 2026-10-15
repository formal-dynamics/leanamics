import Dynamics.Reverse

/-! # Functionals of `T` rounds (EPI-4)

The COBRA–BIPS duality reverses the sampled rounds: time reversal of i.i.d. uniform rounds is
the core's `Dynamics.expList_comp_reverse` (FND-6). Its pathwise form only holds on lists of the
right length, so the comparison uses that `expList α T` only evaluates its functional on lists of
length `T`.
-/

namespace Epidemics
open Dynamics

/-- `expList α T` only evaluates its functional on lists of length `T` (the core
`Dynamics.expList_congr_length`, with the horizon explicit). -/
lemma expList_congr_length {α : Type*} [Fintype α] (T : ℕ) {F G : List α → ℝ}
    (h : ∀ l, l.length = T → F l = G l) : expList α T F = expList α T G :=
  Dynamics.expList_congr_length h

end Epidemics
