import Dynamics.Drift

/-! # Phase composition

`iterate_add_le` (**two phases**), a fact about an arbitrary finite Markov kernel `K` used for the
median dynamics from any start (`Median/AnyStartPhases.lean`): if the second phase, from every
state `y`, gives an expected observable at most `a + bad y`, and the first phase gives an
expected `bad` at most `b`, then both phases together give at most `a + b`. The `expList` form
for round-based processes (`expList_add_le`) follows through `Dynamics.Kernel.iterate_ofStep`.
The fixed-time drift lemmas used with it are `Dynamics.Kernel.iterate_le_of_drift` and
`Dynamics.expList_le_of_drift`.
-/

namespace Median
open Dynamics

variable {S : Type*} [Fintype S]

/-- **Two phases.** If `T₂` steps from any state `y` give an expected `F` at most `a + bad y`,
and `T₁` steps from `s` give an expected `bad` at most `b`, then `T₁ + T₂` steps from `s` give
an expected `F` at most `a + b`. -/
lemma iterate_add_le (K : Kernel S) {F bad : S → ℝ} {T₁ T₂ : ℕ} {a b : ℝ} {s : S}
    (h₂ : ∀ y, K.iterate T₂ F y ≤ a + bad y) (h₁ : K.iterate T₁ bad s ≤ b) :
    K.iterate (T₁ + T₂) F s ≤ a + b := by
  rw [K.iterate_add_time]
  calc K.iterate T₁ (K.iterate T₂ F) s ≤ K.iterate T₁ (fun y => a + bad y) s :=
        K.iterate_mono T₁ h₂ s
    _ = a + K.iterate T₁ bad s := by rw [K.iterate_add, K.iterate_const]
    _ ≤ a + b := by linarith

/-! ### Round-based processes -/

variable {R : Type*} [Fintype R] [Nonempty R]

/-- **Two phases** for a round-based process (`iterate_add_le`). -/
lemma expList_add_le (step : S → R → S) (F bad : S → ℝ) {T₁ T₂ : ℕ} {a b : ℝ} {s : S}
    (h₂ : ∀ y, expList R T₂ (fun l => F (l.foldl step y)) ≤ a + bad y)
    (h₁ : expList R T₁ (fun l => bad (l.foldl step s)) ≤ b) :
    expList R (T₁ + T₂) (fun l => F (l.foldl step s)) ≤ a + b := by
  simp only [← Kernel.iterate_ofStep] at h₁ h₂ ⊢
  exact iterate_add_le _ h₂ h₁

end Median
