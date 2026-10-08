import Dynamics.Rounds

/-! # Fixed-time drift and phase composition

Two facts about an arbitrary finite Markov kernel `K`, used for the median dynamics from any
start (`Median/AnyStartPhases.lean`):

* `iterate_le_of_drift` (**fixed-time drift**): if one step contracts the expectation of a
  potential `φ` by a factor `ρ ∈ [0, 1]` up to an additive error `ε ≥ 0`, then after `T` steps
  the expected potential is at most `ρ ^ T φ + T ε` (no stopping times needed);
* `iterate_add_le` (**two phases**): if the second phase, from every state `y`, gives an expected
  observable at most `a + bad y`, and the first phase gives an expected `bad` at most `b`, then
  both phases together give at most `a + b`.

The `expList` forms for round-based processes (`expList_le_of_drift`, `expList_add_le`) follow
through `Dynamics.Kernel.iterate_ofStep`; `expList_one_sub` computes the expectation of `1 - F`.
-/

namespace Median
open Dynamics

variable {S : Type*} [Fintype S]

/-- **Fixed-time drift.** If one step of `K` maps the potential `φ` to at most `ρ φ + ε`, with
`0 ≤ ρ ≤ 1` and `0 ≤ ε`, then after `T` steps the expected potential is at most
`ρ ^ T φ + T ε`. -/
lemma iterate_le_of_drift (K : Kernel S) (φ : S → ℝ) {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hε : 0 ≤ ε) (hφ : ∀ a, K.apply φ a ≤ ρ * φ a + ε) (T : ℕ) (a : S) :
    K.iterate T φ a ≤ ρ ^ T * φ a + T * ε := by
  induction T with
  | zero => simp
  | succ T ih =>
    -- the last step first: `K^{T+1} φ = K^T (K φ) ≤ K^T (ρ φ + ε) = ρ K^T φ + ε`
    have hstep : K.iterate (T + 1) φ a ≤ ρ * K.iterate T φ a + ε := by
      rw [K.iterate_add_time T 1]
      calc K.iterate T (K.iterate 1 φ) a ≤ K.iterate T (fun b => ρ * φ b + ε) a :=
            K.iterate_mono T hφ a
        _ = ρ * K.iterate T φ a + ε := by rw [K.iterate_add, K.iterate_mul, K.iterate_const]
    have hTε : ρ * (T * ε) ≤ T * ε := mul_le_of_le_one_left (by positivity) hρ1
    calc K.iterate (T + 1) φ a ≤ ρ * (ρ ^ T * φ a + T * ε) + ε :=
          hstep.trans (by gcongr)
      _ ≤ ρ ^ (T + 1) * φ a + ((T + 1 : ℕ) : ℝ) * ε := by
          push_cast
          rw [pow_succ]
          linarith

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

/-- **Fixed-time drift** for a round-based process: if one uniform round maps the potential `φ`
to at most `ρ φ + ε` in expectation (`0 ≤ ρ ≤ 1`, `0 ≤ ε`), then after `T` rounds the expected
potential is at most `ρ ^ T φ + T ε`. -/
lemma expList_le_of_drift (step : S → R → S) (φ : S → ℝ) {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hε : 0 ≤ ε) (hφ : ∀ s, avg (fun r => φ (step s r)) ≤ ρ * φ s + ε) (T : ℕ) (s : S) :
    expList R T (fun l => φ (l.foldl step s)) ≤ ρ ^ T * φ s + T * ε := by
  rw [← Kernel.iterate_ofStep step T φ s]
  exact iterate_le_of_drift _ φ hρ0 hρ1 hε
    (fun s => (Kernel.apply_ofStep step φ s).trans_le (hφ s)) T s

/-- **Two phases** for a round-based process (`iterate_add_le`). -/
lemma expList_add_le (step : S → R → S) (F bad : S → ℝ) {T₁ T₂ : ℕ} {a b : ℝ} {s : S}
    (h₂ : ∀ y, expList R T₂ (fun l => F (l.foldl step y)) ≤ a + bad y)
    (h₁ : expList R T₁ (fun l => bad (l.foldl step s)) ≤ b) :
    expList R (T₁ + T₂) (fun l => F (l.foldl step s)) ≤ a + b := by
  simp only [← Kernel.iterate_ofStep] at h₁ h₂ ⊢
  exact iterate_add_le _ h₂ h₁

/-- The expectation of `1 - F` over `T` rounds is `1 - 𝔼F`. -/
lemma expList_one_sub (T : ℕ) (F : List R → ℝ) :
    expList R T (fun l => 1 - F l) = 1 - expList R T F := by
  have h := expList_add T (fun l => 1 - F l) F
  simp only [sub_add_cancel, expList_const] at h
  linarith

end Median
