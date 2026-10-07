import Dynamics.Rounds

/-! # Many values: generic tools for chaining one-round moves

Kernel-level facts behind the fast consensus proofs of `Median/ManyValues.lean`. None of them
mentions the median rule: they hold for any finite Markov kernel `K`, or any process driven by
i.i.d. uniform rounds, and are candidates for `Dynamics/` (they live in namespace `Median` until
they are generalized there).

* `kernel_event_mono_set`: occupation probabilities are monotone in the target set;
* `kernel_event_chain`: if every state of `B i` enters `B (i+1)` in one step with
  probability `≥ 1 - ε`, then from `B 0` the chain is in `B T` after `T` steps with probability
  `≥ 1 - T ε` (union bound over the steps);
* `kernel_event_comp`: two segments compose (Markov property), adding their failures;
* `expList_ge_of_and`: the union bound for two events of `T` uniform rounds;
* `expList_foldl_mono`: for a round-based process, the probability of an event that is
  closed under the update rule is nondecreasing in the number of rounds.
-/

namespace Median
open Dynamics Dynamics.Kernel

section Kernel

variable {α : Type*} [Fintype α] (K : Dynamics.Kernel α)

/-- **Monotonicity in the target set.** If `B ⊆ C`, being in `B` after `t` steps is at most as
likely as being in `C`. -/
lemma kernel_event_mono_set {B C : Set α} (h : B ⊆ C) (t : ℕ) (a : α) :
    K.event (· ∈ B) t a ≤ K.event (· ∈ C) t a := by
  classical
  unfold event
  refine K.iterate_mono t (fun b => ?_) a
  by_cases hb : b ∈ B
  · simp [hb, h hb]
  · by_cases hc : b ∈ C <;> simp [hb, hc]

/-- **Chaining one-step moves (union bound over the steps).** If from every state of `B i` one
step enters `B (i+1)` with probability at least `1 - ε`, then from any state of `B 0` the chain
lies in `B T` after `T` steps with probability at least `1 - T ε`. -/
lemma kernel_event_chain {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) (B : ℕ → Set α)
    (hB : ∀ i, ∀ a ∈ B i, 1 - ε ≤ (K a).prob (· ∈ B (i + 1))) :
    ∀ a ∈ B 0, 1 - T * ε ≤ K.event (· ∈ B T) T a := by
  classical
  induction T generalizing B with
  | zero =>
    intro a ha
    simp [event, ha]
  | succ T ih =>
    intro a ha
    have hIH := ih (fun i => B (i + 1)) (fun i b hb => hB (i + 1) b hb)
    have hpt : ∀ b, (if b ∈ B 1 then (1 : ℝ) else 0) - T * ε
        ≤ K.event (· ∈ B (T + 1)) T b := by
      intro b
      by_cases hb : b ∈ B 1
      · rw [if_pos hb]
        exact hIH b hb
      · rw [if_neg hb]
        have h0 := K.event_nonneg (· ∈ B (T + 1)) T b
        have h1 : 0 ≤ (T : ℝ) * ε := mul_nonneg (Nat.cast_nonneg T) hε
        linarith
    have hexp := (K a).expect_mono hpt
    rw [Distribution.expect_sub, Distribution.expect_const] at hexp
    have hprob : (K a).expect (fun b => if b ∈ B 1 then (1 : ℝ) else 0)
        = (K a).prob (· ∈ B 1) := rfl
    have h1 := hB 0 a ha
    show 1 - ((T + 1 : ℕ) : ℝ) * ε ≤ (K a).expect (K.event (· ∈ B (T + 1)) T)
    push_cast
    linarith

/-- **Composing two segments (Markov property).** If from `a` the chain is in `B` after `t₁`
steps with probability at least `1 - δ₁`, and from every state of `B` it is in `C` after `t₂`
steps with probability at least `1 - δ₂`, then from `a` it is in `C` after `t₁ + t₂` steps with
probability at least `1 - (δ₁ + δ₂)`. -/
lemma kernel_event_comp {B C : Set α} {t₁ t₂ : ℕ} {δ₁ δ₂ : ℝ} (hδ₂ : 0 ≤ δ₂) {a : α}
    (h₁ : 1 - δ₁ ≤ K.event (· ∈ B) t₁ a) (h₂ : ∀ b ∈ B, 1 - δ₂ ≤ K.event (· ∈ C) t₂ b) :
    1 - (δ₁ + δ₂) ≤ K.event (· ∈ C) (t₁ + t₂) a := by
  classical
  have hsplit : K.event (· ∈ C) (t₁ + t₂) a = K.iterate t₁ (K.event (· ∈ C) t₂) a := by
    unfold event
    rw [iterate_add_time]
  have hpt : ∀ b, (if b ∈ B then (1 : ℝ) else 0) + (-δ₂) ≤ K.event (· ∈ C) t₂ b := by
    intro b
    by_cases hb : b ∈ B
    · rw [if_pos hb]
      linarith [h₂ b hb]
    · rw [if_neg hb]
      linarith [K.event_nonneg (· ∈ C) t₂ b]
  have hmono := K.iterate_mono t₁ hpt a
  rw [iterate_add, iterate_const] at hmono
  have hB : K.event (· ∈ B) t₁ a = K.iterate t₁ (fun b => if b ∈ B then (1 : ℝ) else 0) a := rfl
  simp only at hmono
  rw [hsplit]
  linarith

end Kernel

/-- **Union bound for two events.** If `P` and `Q` together imply `R`, then over `T` i.i.d.
uniform rounds `ℙ[R] ≥ ℙ[P] + ℙ[Q] - 1`. -/
lemma expList_ge_of_and {α : Type*} [Fintype α] [Nonempty α] {T : ℕ} {P Q R : List α → Prop}
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] (h : ∀ l, P l → Q l → R l) :
    expList α T (fun l => if P l then (1 : ℝ) else 0)
        + expList α T (fun l => if Q l then (1 : ℝ) else 0) - 1
      ≤ expList α T (fun l => if R l then (1 : ℝ) else 0) := by
  have hpt : ∀ l, (if P l then (1 : ℝ) else 0) + (if Q l then (1 : ℝ) else 0)
      ≤ (if R l then (1 : ℝ) else 0) + 1 := by
    intro l
    by_cases hP : P l
    · by_cases hQ : Q l
      · rw [if_pos hP, if_pos hQ, if_pos (h l hP hQ)]
      · rw [if_neg hQ]
        split_ifs <;> norm_num
    · rw [if_neg hP]
      split_ifs <;> norm_num
  have hE := expList_le_expList (T := T) hpt
  rw [expList_add, expList_add, expList_const] at hE
  linarith

/-- **Padding with an absorbing event.** If the event `P` is closed under the update rule
`step`, the probability that `P` holds after `T` i.i.d. uniform rounds is nondecreasing in `T`. -/
lemma expList_foldl_mono {S R : Type*} [Fintype R] [Nonempty R] (step : S → R → S)
    {P : S → Prop} [DecidablePred P] (hP : ∀ s r, P s → P (step s r)) (s : S) :
    Monotone fun T => expList R T (fun l => if P (l.foldl step s) then (1 : ℝ) else 0) := by
  refine monotone_nat_of_le_succ fun T => ?_
  rw [expList_append T 1]
  apply expList_le_expList
  intro l
  rw [expList_succ]
  simp only [expList_zero]
  by_cases hl : P (l.foldl step s)
  · have hf : (fun r : R => if P ((l ++ [r]).foldl step s) then (1 : ℝ) else 0)
        = fun _ => 1 :=
      funext fun r => if_pos (by rw [List.foldl_append]; exact hP _ r hl)
    rw [if_pos hl, hf, avg_const]
  · rw [if_neg hl]
    exact avg_nonneg fun r => by split_ifs <;> norm_num

end Median
