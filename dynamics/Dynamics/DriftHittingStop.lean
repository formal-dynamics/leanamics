import Dynamics.DriftHittingDefs
import Dynamics.Drift

/-!
# Hitting probabilities through the stopped chain

The chain `K.stopped B` follows `K` outside `B` and stays put once in `B`. It is in `B` at time
`n` exactly when the original chain has visited `B` by time `n`, so the non-hitting probability
`1 - K.hitProb B n a` is the event `¬ B` at time `n` of the stopped chain
(`one_sub_hitProb_eq_event_stopped`). This turns hitting times into finite-time events, to which
the drift theorems of `Dynamics.Drift` apply.

`one_sub_hitProb_le_of_drift` is the resulting **geometric drift bound**: a potential `V ≥ 0`
vanishing on `B`, at least `Vmin > 0` off `B`, with `𝔼[V(X_{t+1}) | X_t = a] ≤ ρ V(a)` off `B`,
gives `P_a(T_B > t) ≤ ρ^t V(a) / Vmin`. It is `multiplicative_drift` (the argument of Lemma 2.4 of
Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, ICALP 2016) for the stopped chain.
-/

namespace Dynamics.Kernel
variable {α : Type*} [Fintype α]

/-! ### Recursion for `hitProb` -/

/-- A chain started in `B` has hit `B` at time `0`. -/
lemma hitProb_of_mem (K : Dynamics.Kernel α) {B : α → Prop} {a : α} (h : B a) (n : ℕ) :
    K.hitProb B n a = 1 := by
  classical
  unfold hitProb
  cases n with
  | zero => exact if_pos (Or.inr h)
  | succ n =>
    have hF : (fun l c => if (∃ x ∈ a :: l, B x) ∨ B c then (1 : ℝ) else 0) =
        fun (_ : List α) (_ : α) => (1 : ℝ) :=
      funext fun l => funext fun c => if_pos (Or.inl ⟨a, List.mem_cons_self, h⟩)
    change (K a).expect (fun b => K.trajectory n b
      (fun l c => if (∃ x ∈ a :: l, B x) ∨ B c then (1 : ℝ) else 0)) = 1
    simp_rw [hF]
    have h1 (b : α) : K.trajectory n b (fun _ _ => (1 : ℝ)) = 1 := by
      rw [trajectory_endpoint K n b (fun _ => 1), iterate_const]
    simp_rw [h1, Distribution.expect_const]

/-- Outside `B`, the chain has not hit `B` at time `0`. -/
lemma hitProb_zero_of_not_mem (K : Dynamics.Kernel α) {B : α → Prop} {a : α} (h : ¬ B a) :
    K.hitProb B 0 a = 0 := by
  classical
  unfold hitProb
  exact if_neg (by simp [h])

/-- Outside `B`, hitting `B` within `n + 1` steps means hitting it within `n` steps from the next
state. -/
lemma hitProb_succ_of_not_mem (K : Dynamics.Kernel α) {B : α → Prop} {a : α} (h : ¬ B a)
    (n : ℕ) : K.hitProb B (n + 1) a = (K a).expect (K.hitProb B n) := by
  classical
  unfold hitProb
  have hF : (fun l c => if (∃ x ∈ a :: l, B x) ∨ B c then (1 : ℝ) else 0) =
      fun l c => if (∃ x ∈ l, B x) ∨ B c then (1 : ℝ) else 0 := by
    funext l c
    simp [h]
  change (K a).expect (fun b => K.trajectory n b
    (fun l c => if (∃ x ∈ a :: l, B x) ∨ B c then (1 : ℝ) else 0)) = _
  rw [hF]

/-! ### The stopped chain -/

/-- The chain `K` stopped on entering `B`: it moves with `K` outside `B` and stays put in `B`. -/
noncomputable def stopped (K : Dynamics.Kernel α) (B : α → Prop) : Dynamics.Kernel α := by
  classical
  exact fun a => if B a then Distribution.point a else K a

lemma stopped_of_mem (K : Dynamics.Kernel α) {B : α → Prop} {a : α} (h : B a) :
    K.stopped B a = Distribution.point a := by
  classical
  unfold stopped
  exact if_pos h

lemma stopped_of_not_mem (K : Dynamics.Kernel α) {B : α → Prop} {a : α} (h : ¬ B a) :
    K.stopped B a = K a := by
  classical
  unfold stopped
  exact if_neg h

/-- The stopped chain started at `a` is outside `B` at time `n` with probability
`1 - K.hitProb B n a`, for any observable `f` that is the indicator of the complement of `B`. -/
lemma iterate_stopped_eq_one_sub_hitProb (K : Dynamics.Kernel α) (B : α → Prop) (f : α → ℝ)
    (hf0 : ∀ b, B b → f b = 0) (hf1 : ∀ b, ¬ B b → f b = 1) (n : ℕ) (a : α) :
    (K.stopped B).iterate n f a = 1 - K.hitProb B n a := by
  induction n generalizing a with
  | zero =>
    by_cases h : B a
    · rw [iterate_zero, hf0 a h, hitProb_of_mem K h, sub_self]
    · rw [iterate_zero, hf1 a h, hitProb_zero_of_not_mem K h, sub_zero]
  | succ n ih =>
    rw [iterate_succ, apply]
    by_cases h : B a
    · rw [stopped_of_mem K h, Distribution.point_expect, ih, hitProb_of_mem K h,
        hitProb_of_mem K h]
    · rw [stopped_of_not_mem K h, funext ih, hitProb_succ_of_not_mem K h,
        Distribution.expect_sub, Distribution.expect_const]

/-- The non-hitting probability `P_a(T_B > n)` is the probability that the stopped chain is
outside `B` at time `n`. -/
lemma one_sub_hitProb_eq_event_stopped (K : Dynamics.Kernel α) (B : α → Prop) (n : ℕ)
    (a : α) : 1 - K.hitProb B n a = (K.stopped B).event (fun b => ¬ B b) n a := by
  classical
  unfold event
  exact (iterate_stopped_eq_one_sub_hitProb K B _ (fun b h => by simp [h])
    (fun b h => by simp [h]) n a).symm

/-- **Geometric drift bound for hitting times.** Let `V ≥ 0` vanish on `B` and be at least
`Vmin > 0` off `B`. If `𝔼[V(X_{t+1}) | X_t = x] ≤ ρ V(x)` from every `x ∉ B`, then the chain
started at `a` has not hit `B` within `t` steps with probability at most `ρ^t V(a) / Vmin`.
This is `multiplicative_drift` for the stopped chain. -/
theorem one_sub_hitProb_le_of_drift (K : Dynamics.Kernel α) (B : α → Prop) (V : α → ℝ)
    {ρ Vmin : ℝ} (hV : ∀ x, 0 ≤ V x) (hVB : ∀ x, B x → V x = 0) (hmin : 0 < Vmin)
    (hgap : ∀ x, ¬ B x → Vmin ≤ V x) (hdrift : ∀ x, ¬ B x → K.apply V x ≤ ρ * V x)
    (t : ℕ) (a : α) : 1 - K.hitProb B t a ≤ ρ ^ t * V a / Vmin := by
  have hpos : (fun x => 0 < V x) = fun x => ¬ B x := by
    funext x
    by_cases h : B x
    · simp [h, hVB x h]
    · exact propext ⟨fun _ => h, fun _ => hmin.trans_le (hgap x h)⟩
  have hgap' : ∀ x, 0 < V x → Vmin ≤ V x := fun x hx =>
    hgap x fun h => (hVB x h ▸ hx).false
  have hdrift' : ∀ x, (K.stopped B).apply V x ≤ (1 - (1 - ρ)) * V x := by
    intro x
    rw [sub_sub_cancel]
    by_cases h : B x
    · rw [apply, stopped_of_mem K h, Distribution.point_expect, hVB x h, mul_zero]
    · rw [apply, stopped_of_not_mem K h]
      exact hdrift x h
  have h := multiplicative_drift (K.stopped B) V hV hmin hgap' hdrift' a t
  rwa [hpos, sub_sub_cancel, ← one_sub_hitProb_eq_event_stopped] at h

end Dynamics.Kernel
