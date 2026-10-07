import Dynamics.Distribution

/-!
# Normalized weights and conditioning

Two operations on `Dynamics.Distribution` that `dynamics/` does not provide yet: the
distribution proportional to nonnegative weights, and a distribution conditioned on an event of
nonzero probability. The jump chain of a CRN (`Crn.Network.jumpKernel`) chooses its next reaction
with probability proportional to the propensities, and the population protocol is conditioned
on the drawn pair reacting (`Crn.condStep`).
-/

namespace Crn
open Dynamics Finset

variable {α : Type*} [Fintype α]

/-- The distribution proportional to nonnegative weights `w` with nonzero total. -/
noncomputable def normalize (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (h : ∑ a, w a ≠ 0) :
    Distribution α where
  weight a := w a / ∑ b, w b
  nonneg a := div_nonneg (hw a) (sum_nonneg fun b _ => hw b)
  sum_one := by rw [← sum_div, div_self h]

/-- `p` conditioned on an event `E` of nonzero probability: weight `p(a) / p(E)` on `E`. -/
noncomputable def condition (p : Distribution α) (E : α → Prop) (h : p.prob E ≠ 0) :
    Distribution α := by
  classical
  exact normalize (fun a => if E a then p.weight a else 0)
    (fun a => by split_ifs <;> simp [p.nonneg a])
    (by simpa [Distribution.prob, Distribution.expect] using h)

end Crn
