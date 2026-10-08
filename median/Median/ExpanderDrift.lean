import Dynamics.Uniform

/-! # Multiplicative drift inside a region

A fixed-time bound for a process driven by i.i.d. uniform rounds: inside a region `Good`, a
nonnegative potential `Φ` contracts in expectation by the factor `ρ`, and one round leaves the
region with probability at most `q`. Then any observable `f ≤ 1` with `f ≤ Φ` on the
region has expectation at most `ρ^T Φ(s) + T q` after `T` rounds. This is the supermartingale
argument behind `two_choices_expander_explicit` (with `Φ` the minority size and `f` the
indicator of not being in consensus).
-/

namespace Median
open Dynamics

/-- **Contraction inside a region with a small exit probability.** -/
theorem expList_le_of_contract {S R : Type*} [Fintype R] [Nonempty R] (step : S → R → S)
    (Φ f : S → ℝ) (Good : S → Prop) [DecidablePred Good] {ρ q : ℝ} (hρ : 0 ≤ ρ) (hq : 0 ≤ q)
    (hf1 : ∀ s, f s ≤ 1) (hΦ0 : ∀ s, 0 ≤ Φ s)
    (hfΦ : ∀ s, Good s → f s ≤ Φ s)
    (hdrift : ∀ s, Good s → avg (fun r => Φ (step s r)) ≤ ρ * Φ s)
    (hexit : ∀ s, Good s → avg (fun r => if Good (step s r) then (0 : ℝ) else 1) ≤ q) :
    ∀ (T : ℕ) (s : S), Good s →
      expList R T (fun l => f (l.foldl step s)) ≤ ρ ^ T * Φ s + T * q := by
  intro T
  induction T with
  | zero =>
    intro s hs
    simpa using hfΦ s hs
  | succ T ih =>
    intro s hs
    rw [expList_succ]
    have hpt (r : R) :
        expList R T (fun l => f ((r :: l).foldl step s))
          ≤ ρ ^ T * Φ (step s r) + T * q + (if Good (step s r) then (0 : ℝ) else 1) := by
      by_cases hr : Good (step s r)
      · rw [if_pos hr, add_zero]
        exact ih (step s r) hr
      · rw [if_neg hr]
        have h1 : expList R T (fun l => f ((r :: l).foldl step s)) ≤ 1 := by
          calc _ ≤ expList R T (fun _ => (1 : ℝ)) := expList_le_expList fun l => hf1 _
            _ = 1 := expList_const T 1
        have : 0 ≤ ρ ^ T * Φ (step s r) := mul_nonneg (pow_nonneg hρ T) (hΦ0 _)
        have : (0 : ℝ) ≤ T * q := mul_nonneg (Nat.cast_nonneg T) hq
        linarith
    calc avg (fun r => expList R T (fun l => f ((r :: l).foldl step s)))
        ≤ avg (fun r => ρ ^ T * Φ (step s r) + T * q
            + (if Good (step s r) then (0 : ℝ) else 1)) := avg_le_avg hpt
      _ = ρ ^ T * avg (fun r => Φ (step s r)) + T * q
            + avg (fun r => if Good (step s r) then (0 : ℝ) else 1) := by
          rw [avg_add, avg_add, avg_const, avg_const_mul]
      _ ≤ ρ ^ T * (ρ * Φ s) + T * q + q := by
          have := mul_le_mul_of_nonneg_left (hdrift s hs) (pow_nonneg hρ T)
          linarith [hexit s hs]
      _ = ρ ^ (T + 1) * Φ s + ((T + 1 : ℕ) : ℝ) * q := by push_cast; ring

end Median
