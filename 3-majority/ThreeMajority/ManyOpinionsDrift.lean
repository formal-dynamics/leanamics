import Dynamics.Hitting

/-!
# Hitting times under an additive drift (BCNPT16, Lemma 3.2; roadmap MAJ-12 (a))

Facts about an arbitrary finite Markov kernel `K`, for the symmetry-breaking stage of 3-Majority
with many colours (Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with
many opinions*, SODA 2016, arXiv:1508.06782, BCNPT16 below).

* `hitProb_additive_drift`: **Lemma 3.2** of BCNPT16 in finite-horizon form. If, inside an
  invariant set `I` and outside the target `B`, an observable `f ≤ M` grows by at least `λ` in
  expectation per step, is at most `β` outside `B`, and overshoots `β` in one step with
  probability at most `η`, then `λ t P(T_B > t) ≤ β + M η t`. The paper states
  `𝔼[T_B] ≤ 2 α m / λ` (`β = α m`, with the overshoot controlled at the hitting time, its
  Hypothesis 2 and Lemma B.1) and then applies Markov's inequality; here the overshoot is
  controlled one step at a time and no infinite-horizon expectation is needed.
* `hitProb_mul_le_event` (**hit, then absorb**, multiplicative form): if from every state of `B`
  the chain is in an absorbing event `P` after `s` steps with probability at least `q`, then it is
  in `P` at time `t + s` with probability at least `q P(T_B ≤ t)` (the strong Markov property at
  the hitting time of `B`, by induction on `t`; `Dynamics.Kernel.hitProb_sub_le_event` is the
  additive form `P(T_B ≤ t) − ε`).

The general facts on hitting probabilities used here (`hitProb_le_one`, `hitProb_mono_time`) are
in `Dynamics.Hitting`.
-/

namespace ThreeMajority

open Dynamics Dynamics.Kernel

variable {α : Type*} [Fintype α]

/-- **Hit, then absorb** (multiplicative form). Let `P` be absorbing for `K`. If from every state
of `B` the chain is in `P` after `s` steps with probability at least `q`, then from any state
`a` it is in `P` at time `t + s` with probability at least `q P_a(T_B ≤ t)`. -/
theorem hitProb_mul_le_event (K : Kernel α) {B P : α → Prop}
    (habs : ∀ a, P a → (K a).prob P = 1) {s : ℕ} {q : ℝ}
    (hB : ∀ b, B b → q ≤ K.event P s b) (t : ℕ) (a : α) :
    q * K.hitProb B t a ≤ K.event P (t + s) a := by
  classical
  induction t generalizing a with
  | zero =>
    by_cases h : B a
    · rw [hitProb_of_mem K h, mul_one, zero_add]
      exact hB a h
    · rw [hitProb_zero_of_not_mem K h, mul_zero]
      exact K.event_nonneg P (0 + s) a
  | succ t ih =>
    by_cases h : B a
    · rw [hitProb_of_mem K h, mul_one]
      exact (hB a h).trans (K.event_monotone habs a (show s ≤ t + 1 + s by omega))
    · have e : K.event P (t + 1 + s) a = (K a).expect (fun b => K.event P (t + s) b) := by
        rw [show t + 1 + s = (t + s) + 1 by omega, event_eq_iterate, iterate_succ, apply]
        simp only [event_eq_iterate]
      rw [hitProb_succ_of_not_mem K h, e, ← Distribution.expect_mul]
      exact (K a).expect_mono ih

/-- A distribution giving probability one to `I` has expectations monotone on `I`. -/
lemma expect_le_expect_of_prob_eq_one (p : Distribution α) {I : α → Prop} (hp : p.prob I = 1)
    {g h : α → ℝ} (hgh : ∀ x, I x → g x ≤ h x) : p.expect g ≤ p.expect h := by
  classical
  -- the weight outside `I` vanishes
  have hout : ∀ x, ¬ I x → p.weight x = 0 := by
    intro x hx
    rw [Distribution.prob_eq_expect] at hp
    unfold Distribution.expect at hp
    have hsum : ∑ y, p.weight y * (1 - if I y then (1 : ℝ) else 0) = 0 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, p.sum_one, hp, sub_self]
    have hnn : ∀ y ∈ Finset.univ, 0 ≤ p.weight y * (1 - if I y then (1 : ℝ) else 0) :=
      fun y _ => mul_nonneg (p.nonneg y) (by split_ifs <;> norm_num)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum x (Finset.mem_univ x)
    simpa [hx] using this
  unfold Distribution.expect
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : I x
  · exact mul_le_mul_of_nonneg_left (hgh x hx) (p.nonneg x)
  · simp [hout x hx]

/-- The iterates of a kernel that keeps `I` with probability one are monotone on `I`. -/
lemma iterate_le_iterate_of_invariant (K : Kernel α) {I : α → Prop}
    (hI : ∀ x, I x → (K x).prob I = 1) {g h : α → ℝ} (hgh : ∀ x, I x → g x ≤ h x) (s : ℕ) :
    ∀ x, I x → K.iterate s g x ≤ K.iterate s h x := by
  induction s with
  | zero => exact hgh
  | succ s ih => exact fun x hx => expect_le_expect_of_prob_eq_one (K x) (hI x hx) ih

/-- **Lemma 3.2** (BCNPT16), finite-horizon form. Let `I` be invariant for `K` and let `B` be a
target set. Suppose that, for every `x ∈ I`, `f x ≤ M`, and for every `x ∈ I` outside `B`:
`f x ≤ β`; the drift `𝔼[f(X₁) | X₀ = x] ≥ f x + λ` (Hypothesis 1); and the overshoot
`P(f(X₁) > β | X₀ = x) ≤ η` (the one-step form of Hypothesis 2). Then for every start `a ∈ I`
with `f a ≥ 0` and every `t`, `λ t P_a(T_B > t) ≤ β + M η t`.

In the paper `B = {f ≥ m}`, `β = α m`, the conclusion is `𝔼_a[T_B] ≤ 2 α m / λ`, and the
symmetry-breaking stage (Lemma 3.3) applies Markov's inequality to it. -/
theorem hitProb_additive_drift (K : Kernel α) (I B : α → Prop) (f : α → ℝ) {lam β M η : ℝ}
    (hβ : 0 ≤ β) (hη : 0 ≤ η) (hI : ∀ x, I x → (K x).prob I = 1)
    (hfM : ∀ x, I x → f x ≤ M) (hfβ : ∀ x, I x → ¬ B x → f x ≤ β)
    (hdrift : ∀ x, I x → ¬ B x → f x + lam ≤ K.apply f x)
    (hjump : ∀ x, I x → ¬ B x → (K x).prob (fun y => β < f y) ≤ η)
    (t : ℕ) (a : α) (ha : I a) (hfa : 0 ≤ f a) :
    lam * t * (1 - K.hitProb B t a) ≤ β + M * η * t := by
  classical
  have hM : 0 ≤ M := hfa.trans (hfM a ha)
  have hq : 0 ≤ 1 - K.hitProb B t a := by linarith [hitProb_le_one K B t a]
  have hR : 0 ≤ β + M * η * t := by positivity
  by_cases hlam : lam ≤ 0
  · have : lam * t * (1 - K.hitProb B t a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hlam (Nat.cast_nonneg t)) hq
    linarith
  push Not at hlam
  by_cases haB : B a
  · rw [hitProb_of_mem K haB, sub_self, mul_zero]
    exact hR
  -- the stopped chain keeps `I`
  have hI' : ∀ x, I x → (K.stopped B x).prob I = 1 := by
    intro x hx
    by_cases hB : B x
    · rw [stopped_of_mem K hB, Distribution.prob_eq_expect, Distribution.point_expect, if_pos hx]
    · rw [stopped_of_not_mem K hB]
      exact hI x hx
  have hsucc (g : α → ℝ) (s : ℕ) :
      (K.stopped B).iterate (s + 1) g a = (K.stopped B).iterate s ((K.stopped B).apply g) a := by
    rw [iterate_add_time]
    rfl
  -- lower bound: `𝔼 f(X'_s) ≥ f a + λ ∑_{i < s} P(T_B > i)`
  have hlow (s : ℕ) : f a + lam * ∑ i ∈ Finset.range s, (1 - K.hitProb B i a) ≤
      (K.stopped B).iterate s f a := by
    induction s with
    | zero => simp
    | succ s ih =>
      have hstep : ∀ x, I x → f x + lam * (if B x then 0 else 1) ≤ (K.stopped B).apply f x := by
        intro x hx
        by_cases hB : B x
        · rw [if_pos hB, mul_zero, add_zero, apply, stopped_of_mem K hB,
            Distribution.point_expect]
        · rw [if_neg hB, mul_one, apply, stopped_of_not_mem K hB]
          exact hdrift x hx hB
      have h2 := iterate_le_iterate_of_invariant (K.stopped B) hI' hstep s a ha
      rw [iterate_add, iterate_mul] at h2
      beta_reduce at h2
      have h3 : (K.stopped B).iterate s (fun x => if B x then (0 : ℝ) else 1) a =
          1 - K.hitProb B s a :=
        iterate_stopped_eq_one_sub_hitProb K B _ (fun b h => by simp [h])
          (fun b h => by simp [h]) s a
      rw [h3] at h2
      rw [Finset.sum_range_succ, hsucc]
      linarith
  -- overshoot: `P(f(X'_s) > β) ≤ η s`
  have hover (s : ℕ) :
      (K.stopped B).iterate s (fun x => if β < f x then (1 : ℝ) else 0) a ≤ η * s := by
    induction s with
    | zero =>
      simp only [iterate_zero, Nat.cast_zero, mul_zero]
      rw [if_neg (not_lt.mpr (hfβ a ha haB))]
    | succ s ih =>
      have hstep : ∀ x, I x → (K.stopped B).apply (fun x => if β < f x then (1 : ℝ) else 0) x ≤
          (if β < f x then (1 : ℝ) else 0) + η := by
        intro x hx
        by_cases hB : B x
        · rw [apply, stopped_of_mem K hB, Distribution.point_expect]
          linarith
        · rw [apply, stopped_of_not_mem K hB, if_neg (not_lt.mpr (hfβ x hx hB)), zero_add]
          have := hjump x hx hB
          rwa [Distribution.prob_eq_expect] at this
      have h2 := iterate_le_iterate_of_invariant (K.stopped B) hI' hstep s a ha
      rw [iterate_add, iterate_const] at h2
      beta_reduce at h2
      rw [hsucc]
      push_cast
      linarith
  -- upper bound: `𝔼 f(X'_t) ≤ β + M P(f(X'_t) > β)`
  have hupp : ∀ x, I x → f x ≤ β + M * (if β < f x then (1 : ℝ) else 0) := by
    intro x hx
    split_ifs with h
    · linarith [hfM x hx]
    · push Not at h
      linarith
  have hup : (K.stopped B).iterate t f a ≤ β + M * η * t := by
    have h := iterate_le_iterate_of_invariant (K.stopped B) hI' hupp t a ha
    rw [iterate_add, iterate_const, iterate_mul] at h
    beta_reduce at h
    have := mul_le_mul_of_nonneg_left (hover t) hM
    linarith
  -- `t P(T_B > t) ≤ ∑_{i < t} P(T_B > i)`
  have hsum : (t : ℝ) * (1 - K.hitProb B t a) ≤
      ∑ i ∈ Finset.range t, (1 - K.hitProb B i a) := by
    have hle : ∀ i ∈ Finset.range t, 1 - K.hitProb B t a ≤ 1 - K.hitProb B i a :=
      fun i hi => by
        have := hitProb_mono_time K B (le_of_lt (Finset.mem_range.mp hi)) a
        linarith
    have := Finset.card_nsmul_le_sum (Finset.range t) _ _ hle
    simpa using this
  have := hlow t
  have := mul_le_mul_of_nonneg_left hsum hlam.le
  nlinarith

end ThreeMajority
