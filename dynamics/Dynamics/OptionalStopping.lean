import Dynamics.Kernel

/-!
# Finite-horizon optional stopping (roadmap FND-4)

Let `K` be a finite kernel, `A` and `B` two target events on which an observable `φ` takes
constant values `φA` and `φB`, and suppose that `φ` is conserved in expectation from `x₀`:
`𝔼[φ(X_T)] = φ(x₀)` for every time `T`. Pointwise,
`φ - φB = (φA - φB) · 1_A + (φ - φB) · 1_{¬A ∧ ¬B}`, so the conservation law determines the
probability of `A` at time `T` up to the survival probability `P(X_T ∉ A ∪ B)`
(`event_error_of_invariant`). When survival vanishes, the probability of `A` tends to
`(φ(x₀) − φB) / (φA − φB)` (`tendsto_event_of_invariant`); if `A` is absorbing, this limit is
the absorption probability, the supremum of the increasing finite-time probabilities
(`iSup_event_of_invariant`).

This is the argument of Hassin–Peleg, Lemma 2.2 (`Voter.whiteProbability_error`), and of the
fixation formulas of `moran/` (`Moran.fixation_eq_of_invariant`). Since `φ` is constant on the
absorbing targets, `φ(X_T)` and the stopped value `φ(X_{τ ∧ T})` agree, so no stopping time or
path space is needed.
-/

namespace Dynamics.Kernel
open Filter Topology Finset
variable {α : Type*} [Fintype α]

omit [Fintype α] in
/-- Pointwise decomposition behind optional stopping: `φ - φB` equals `φA - φB` on `A`, vanishes
on `B`, and is unchanged off `A ∪ B`. No disjointness is needed: on `A ∩ B`, `φA = φB`. -/
lemma eq_add_target_add_survival (φ : α → ℝ) (A B : α → Prop) [DecidablePred A]
    [DecidablePred B] (φA φB : ℝ) (hA : ∀ a, A a → φ a = φA) (hB : ∀ a, B a → φ a = φB)
    (a : α) :
    φ a = φB + ((φA - φB) * (if A a then 1 else 0) +
      (φ a - φB) * (if ¬ A a ∧ ¬ B a then 1 else 0)) := by
  by_cases ha : A a
  · by_cases hb : B a
    · have h : φA = φB := (hA a ha).symm.trans (hB a hb)
      simp [ha, hb, hA a ha, h]
    · simp [ha, hA a ha]
  · by_cases hb : B a
    · simp [ha, hb, hB a hb]
    · simp [ha, hb]

/-- Optional-stopping identity at time `T`: the expectation of `φ` is `φB`, plus the
contribution `(φA - φB) P(X_T ∈ A)` of `A`, plus the contribution of the survivors. -/
lemma iterate_eq_event_add (K : Kernel α) (φ : α → ℝ) (A B : α → Prop) [DecidablePred A]
    [DecidablePred B] (φA φB : ℝ) (hA : ∀ a, A a → φ a = φA) (hB : ∀ a, B a → φ a = φB)
    (T : ℕ) (x₀ : α) :
    K.iterate T φ x₀ = φB + ((φA - φB) * K.event A T x₀ +
      K.iterate T (fun a => (φ a - φB) * if ¬ A a ∧ ¬ B a then 1 else 0) x₀) := by
  have h : φ = fun a => (fun _ => φB) a + ((fun a => (φA - φB) * (if A a then 1 else 0)) a +
      (fun a => (φ a - φB) * (if ¬ A a ∧ ¬ B a then (1 : ℝ) else 0)) a) :=
    funext (eq_add_target_add_survival φ A B φA φB hA hB)
  conv_lhs => rw [h]
  rw [K.iterate_add, K.iterate_const, K.iterate_add, K.iterate_mul, K.event_eq_iterate]

/-- **Finite-horizon optional stopping** (roadmap FND-4, finite-time form). Let `φ` equal `φA`
on `A` and `φB` on `B`, satisfy `m ≤ φ - φB ≤ M` outside `A ∪ B`, and have expectation `φ x₀`
at time `T` from `x₀`. Then `φ x₀ - φB - (φA - φB) P(X_T ∈ A)` lies between `m` and `M` times
the survival probability `P(X_T ∉ A ∪ B)`. -/
theorem event_error_of_invariant (K : Kernel α) (φ : α → ℝ) (A B : α → Prop)
    (φA φB m M : ℝ) (hA : ∀ a, A a → φ a = φA) (hB : ∀ a, B a → φ a = φB)
    (hS : ∀ a, ¬ A a → ¬ B a → m ≤ φ a - φB ∧ φ a - φB ≤ M) (x₀ : α) (T : ℕ)
    (hinv : K.iterate T φ x₀ = φ x₀) :
    m * K.event (fun a => ¬ A a ∧ ¬ B a) T x₀ ≤ φ x₀ - φB - (φA - φB) * K.event A T x₀ ∧
      φ x₀ - φB - (φA - φB) * K.event A T x₀ ≤
        M * K.event (fun a => ¬ A a ∧ ¬ B a) T x₀ := by
  classical
  have hdec := K.iterate_eq_event_add φ A B φA φB hA hB T x₀
  rw [hinv] at hdec
  have hlo := K.iterate_mono T (f := fun a => m * if ¬ A a ∧ ¬ B a then 1 else 0)
    (g := fun a => (φ a - φB) * if ¬ A a ∧ ¬ B a then 1 else 0) (fun a => by
      split_ifs with h
      · simpa using (hS a h.1 h.2).1
      · simp) x₀
  have hhi := K.iterate_mono T (f := fun a => (φ a - φB) * if ¬ A a ∧ ¬ B a then 1 else 0)
    (g := fun a => M * if ¬ A a ∧ ¬ B a then 1 else 0) (fun a => by
      split_ifs with h
      · simpa using (hS a h.1 h.2).2
      · simp) x₀
  rw [K.iterate_mul] at hlo hhi
  rw [K.event_eq_iterate (fun a => ¬ A a ∧ ¬ B a)]
  constructor <;> linarith

/-- **Finite-horizon optional stopping** (roadmap FND-4, limit form). If `φ` equals `φA` on `A`
and `φB ≠ φA` on `B`, `𝔼[φ(X_T)] = φ(x₀)` for every `T`, and the survival probability
`P(X_T ∉ A ∪ B)` tends to `0`, then `P(X_T ∈ A)` tends to `(φ(x₀) − φB) / (φA − φB)`. -/
theorem tendsto_event_of_invariant (K : Kernel α) (φ : α → ℝ) (A B : α → Prop) (φA φB : ℝ)
    (hA : ∀ a, A a → φ a = φA) (hB : ∀ a, B a → φ a = φB) (hAB : φA ≠ φB) (x₀ : α)
    (hinv : ∀ T, K.iterate T φ x₀ = φ x₀)
    (hsurv : Tendsto (fun T => K.event (fun a => ¬ A a ∧ ¬ B a) T x₀) atTop (𝓝 0)) :
    Tendsto (fun T => K.event A T x₀) atTop (𝓝 ((φ x₀ - φB) / (φA - φB))) := by
  set M : ℝ := ∑ a, |φ a - φB|
  have hM (a : α) : |φ a - φB| ≤ M :=
    single_le_sum (f := fun a => |φ a - φB|) (fun _ _ => abs_nonneg _) (mem_univ a)
  have herr (T : ℕ) := K.event_error_of_invariant φ A B φA φB (-M) M hA hB
    (fun a _ _ => abs_le.mp (hM a)) x₀ T (hinv T)
  have hz : Tendsto (fun T => φ x₀ - φB - (φA - φB) * K.event A T x₀) atTop (𝓝 0) := by
    have hlo := hsurv.const_mul (-M)
    have hhi := hsurv.const_mul M
    rw [mul_zero] at hlo hhi
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun T => (herr T).1)
      (fun T => (herr T).2)
  have hlim : Tendsto (fun T => (φA - φB) * K.event A T x₀) atTop (𝓝 (φ x₀ - φB)) := by
    simpa using (tendsto_const_nhds (x := φ x₀ - φB)).sub hz
  have h := hlim.const_mul (φA - φB)⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hAB), one_mul] at h
  rwa [div_eq_inv_mul]

/-- **Finite-horizon optional stopping** (roadmap FND-4, absorption probability). Under the
hypotheses of `tendsto_event_of_invariant`, if moreover `A` is absorbing, the absorption
probability in `A` from `x₀`, i.e. the supremum of the finite-time probabilities
`P(X_T ∈ A)`, is `(φ(x₀) − φB) / (φA − φB)`. -/
theorem iSup_event_of_invariant (K : Kernel α) (φ : α → ℝ) (A B : α → Prop) (φA φB : ℝ)
    (hA : ∀ a, A a → φ a = φA) (hB : ∀ a, B a → φ a = φB) (hAB : φA ≠ φB)
    (hAabs : ∀ a, A a → (K a).prob A = 1) (x₀ : α)
    (hinv : ∀ T, K.iterate T φ x₀ = φ x₀)
    (hsurv : Tendsto (fun T => K.event (fun a => ¬ A a ∧ ¬ B a) T x₀) atTop (𝓝 0)) :
    ⨆ T, K.event A T x₀ = (φ x₀ - φB) / (φA - φB) := by
  classical
  have hstep (a : α) :
      (if A a then (1 : ℝ) else 0) ≤ K.apply (fun b => if A b then 1 else 0) a := by
    by_cases ha : A a
    · rw [if_pos ha, apply, ← Distribution.prob_eq_expect, hAabs a ha]
    · rw [if_neg ha]
      exact (K a).expect_nonneg fun b => by split <;> norm_num
  have hmono : Monotone fun T => K.event A T x₀ := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [K.event_eq_iterate A, K.iterate_add_time n 1]
    exact K.iterate_mono n hstep x₀
  exact tendsto_nhds_unique (tendsto_atTop_ciSup hmono
    ⟨1, by rintro _ ⟨n, rfl⟩; exact K.event_le_one A n x₀⟩)
    (K.tendsto_event_of_invariant φ A B φA φB hA hB hAB x₀ hinv hsurv)

end Dynamics.Kernel
