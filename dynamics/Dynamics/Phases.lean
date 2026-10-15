import Dynamics.Drift

/-!
# Progress through nested phases

A finite Markov chain that, from every state of `Aᵢ`, stays in `Aᵢ` with
probability `≥ 1 - ε` and moves into the smaller set `Aᵢ₊₁` with
probability `≥ 1 - ν`, reaches the innermost set `A_T` within `ℓ T` steps
except with probability `T (ℓ ε + ν^ℓ)`. This is Lemma A.4 of Becchetti,
Clementi, Natale, Pasquale, Silvestri, Trevisan, *Simple dynamics for
plurality consensus* (SPAA 2014); its proof is omitted there.

The proof works phase by phase with the survival observable `outside B`
(the indicator of having left `B`): within `ℓ` steps the chain leaves `Aᵢ`
with probability at most `ℓ ε` and fails to jump in each of the `ℓ` steps
with probability at most `ν^ℓ`. The hypothesis `ε ≤ ν` of the paper is not
needed.

**Phase calculus with a potential** (`iterate_outside_le_of_phases`): if every set `A j` is
closed under the chain and, for `j < J`, one step from `A j` enters `A (j + 1)` with probability
at least `1 - q`, then from `A 0` the chain is outside `A J` after `t` steps with probability at
most `(q + 1/λ)^t λ^J`, for every `λ ≥ 1`. The potential is `λ^{J - j}` in phase `j` (the largest
`j ≤ J` with the state in `A j`, `phaseOf`) and `0` in `A J` (`phasePot`); it contracts by
`q + 1/λ` per step, and `iterate_le_pow_of_closed` iterates the contraction. The sets need not
be nested, and the bound is exponential in `t` rather than a union bound over the phases.
-/

namespace Dynamics.Kernel
open Finset
variable {α : Type*} [Fintype α]

/-- Indicator of lying outside `B`. -/
noncomputable def outside (B : Set α) (b : α) : ℝ := by
  classical
  exact if b ∈ B then 0 else 1

omit [Fintype α] in
lemma outside_of_mem {B : Set α} {b : α} (h : b ∈ B) : outside B b = 0 := by
  classical
  simp [outside, h]

omit [Fintype α] in
lemma outside_of_not_mem {B : Set α} {b : α} (h : b ∉ B) : outside B b = 1 := by
  classical
  simp [outside, h]

omit [Fintype α] in
lemma outside_nonneg (B : Set α) (b : α) : 0 ≤ outside B b := by
  classical
  unfold outside
  split <;> norm_num

omit [Fintype α] in
lemma outside_le_one (B : Set α) (b : α) : outside B b ≤ 1 := by
  classical
  unfold outside
  split <;> norm_num

/-- One step leaves `B` with probability `1 - P(stay in B)`. -/
lemma apply_outside (K : Dynamics.Kernel α) (B : Set α) (a : α) :
    K.apply (outside B) a = 1 - (K a).prob (· ∈ B) := by
  classical
  have h : outside B = fun b => 1 - (if b ∈ B then (1 : ℝ) else 0) := by
    funext b
    unfold outside
    split <;> norm_num
  rw [h]
  simp only [apply, Distribution.expect_sub, Distribution.expect_const, Distribution.prob]

/-- Occupation probability is one minus the survival observable. -/
lemma event_eq_one_sub (K : Dynamics.Kernel α) (B : Set α) (n : ℕ) (a : α) :
    K.event (· ∈ B) n a = 1 - K.iterate n (outside B) a := by
  classical
  have h : (fun b => if b ∈ B then (1 : ℝ) else 0) = fun b => 1 + (-1) * outside B b := by
    funext b
    unfold outside
    split <;> norm_num
  unfold event
  simp only [h, iterate_add, iterate_mul, iterate_const]
  ring

/-- **Staying**: if from every state of `B` the chain stays in `B` with
probability `≥ 1 - ε`, then it has left `B` after `ℓ` steps with probability
at most `ℓ ε`. -/
lemma iterate_outside_le_of_stay (K : Dynamics.Kernel α) (B : Set α) {ε : ℝ} (hε : 0 ≤ ε)
    (hstay : ∀ a ∈ B, 1 - ε ≤ (K a).prob (· ∈ B)) :
    ∀ ℓ : ℕ, ∀ a ∈ B, K.iterate ℓ (outside B) a ≤ ℓ * ε := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro a ha
    simp [outside_of_mem ha]
  | succ ℓ ih =>
    intro a ha
    have hpt (b : α) : K.iterate ℓ (outside B) b ≤ ℓ * ε + outside B b := by
      by_cases hb : b ∈ B
      · rw [outside_of_mem hb]
        linarith [ih b hb]
      · rw [outside_of_not_mem hb]
        have := K.iterate_le_one ℓ (outside_le_one B) b
        have : (0 : ℝ) ≤ ℓ * ε := by positivity
        linarith
    rw [iterate_succ]
    calc K.apply (K.iterate ℓ (outside B)) a
        ≤ (K a).expect (fun b => ℓ * ε + outside B b) := (K a).expect_mono hpt
      _ = ℓ * ε + K.apply (outside B) a := by
          rw [Distribution.expect_add, Distribution.expect_const]
          rfl
      _ ≤ ((ℓ + 1 : ℕ) : ℝ) * ε := by
          rw [apply_outside]
          have := hstay a ha
          push_cast
          linarith

/-- **One phase**: from `A`, which is left with probability `≤ ε` per step,
the chain is outside `B ⊆ A` after `ℓ` steps with probability at most
`ℓ ε + ν^ℓ`, if every step from `A` enters `B` with probability `≥ 1 - ν` and
`B` itself is left with probability `≤ ε` per step. -/
lemma iterate_outside_le_of_move (K : Dynamics.Kernel α) {A B : Set α} (hBA : B ⊆ A)
    {ε ν : ℝ} (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (hstayA : ∀ a ∈ A, 1 - ε ≤ (K a).prob (· ∈ A))
    (hstayB : ∀ a ∈ B, 1 - ε ≤ (K a).prob (· ∈ B))
    (hmove : ∀ a ∈ A, 1 - ν ≤ (K a).prob (· ∈ B)) :
    ∀ ℓ : ℕ, ∀ a ∈ A, K.iterate ℓ (outside B) a ≤ ℓ * ε + ν ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro a _
    simpa using outside_le_one B a
  | succ ℓ ih =>
    intro a ha
    have hpt (b : α) :
        K.iterate ℓ (outside B) b ≤ ℓ * ε + ν ^ ℓ * outside B b + outside A b := by
      have hℓε : (0 : ℝ) ≤ ℓ * ε := by positivity
      have hνℓ : (0 : ℝ) ≤ ν ^ ℓ := pow_nonneg hν ℓ
      by_cases hb : b ∈ B
      · rw [outside_of_mem hb, outside_of_mem (hBA hb)]
        linarith [K.iterate_outside_le_of_stay B hε hstayB ℓ b hb]
      · by_cases hbA : b ∈ A
        · rw [outside_of_not_mem hb, outside_of_mem hbA]
          linarith [ih b hbA]
        · rw [outside_of_not_mem hb, outside_of_not_mem hbA]
          have := K.iterate_le_one ℓ (outside_le_one B) b
          linarith
    rw [iterate_succ]
    calc K.apply (K.iterate ℓ (outside B)) a
        ≤ (K a).expect (fun b => ℓ * ε + ν ^ ℓ * outside B b + outside A b) :=
          (K a).expect_mono hpt
      _ = ℓ * ε + ν ^ ℓ * K.apply (outside B) a + K.apply (outside A) a := by
          rw [Distribution.expect_add, Distribution.expect_add, Distribution.expect_const,
            Distribution.expect_mul]
          rfl
      _ ≤ ((ℓ + 1 : ℕ) : ℝ) * ε + ν ^ (ℓ + 1) := by
          rw [apply_outside, apply_outside]
          have h1 := hmove a ha
          have h2 := hstayA a ha
          have h3 : ν ^ ℓ * (1 - (K a).prob (· ∈ B)) ≤ ν ^ ℓ * ν :=
            mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hν ℓ)
          push_cast
          rw [pow_succ]
          linarith

/-- **Lemma A.4 (nested phases).** Let `A₁ ⊇ A₂ ⊇ ⋯ ⊇ A_T` be such that
from every state of `Aᵢ` the chain stays in `Aᵢ` with probability
`≥ 1 - ε`, and for `i < T` moves into `Aᵢ₊₁` with probability `≥ 1 - ν`.
Then from any state of `A₁`, after `ℓ T` steps the chain lies in `A_T` with
probability at least `1 - T (ℓ ε + ν^ℓ)`. -/
theorem nested_phases (K : Dynamics.Kernel α) (A : ℕ → Set α) {T : ℕ} (hT : 1 ≤ T) (ℓ : ℕ)
    {ε ν : ℝ} (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (hnest : ∀ i, 1 ≤ i → i < T → A (i + 1) ⊆ A i)
    (hstay : ∀ i, 1 ≤ i → i ≤ T → ∀ a ∈ A i, 1 - ε ≤ (K a).prob (· ∈ A i))
    (hmove : ∀ i, 1 ≤ i → i < T → ∀ a ∈ A i, 1 - ν ≤ (K a).prob (· ∈ A (i + 1))) :
    ∀ a ∈ A 1, 1 - T * (ℓ * ε + ν ^ ℓ) ≤ K.event (· ∈ A T) (ℓ * T) a := by
  have hc : (0 : ℝ) ≤ ℓ * ε + ν ^ ℓ := by positivity
  -- after `j` phases the chain is in `A (j+1)` except with probability `j (ℓ ε + ν^ℓ)`
  have hphase : ∀ j : ℕ, j + 1 ≤ T → ∀ a ∈ A 1,
      K.iterate (ℓ * j) (outside (A (j + 1))) a ≤ j * (ℓ * ε + ν ^ ℓ) := by
    intro j
    induction j with
    | zero =>
      intro _ a ha
      simp [outside_of_mem ha]
    | succ j ih =>
      intro hj a ha
      have hpt (b : α) : K.iterate ℓ (outside (A (j + 2))) b
          ≤ (ℓ * ε + ν ^ ℓ) + outside (A (j + 1)) b := by
        by_cases hb : b ∈ A (j + 1)
        · rw [outside_of_mem hb, add_zero]
          exact K.iterate_outside_le_of_move (hnest (j + 1) (by omega) (by omega)) hε hν
            (hstay (j + 1) (by omega) (by omega)) (hstay (j + 2) (by omega) (by omega))
            (hmove (j + 1) (by omega) (by omega)) ℓ b hb
        · rw [outside_of_not_mem hb]
          have := K.iterate_le_one ℓ (outside_le_one (A (j + 2))) b
          linarith
      have hsplit : ℓ * (j + 1) = ℓ * j + ℓ := by ring
      rw [hsplit, iterate_add_time]
      calc K.iterate (ℓ * j) (K.iterate ℓ (outside (A (j + 1 + 1)))) a
          ≤ K.iterate (ℓ * j) (fun b => (ℓ * ε + ν ^ ℓ) + outside (A (j + 1)) b) a :=
            K.iterate_mono _ hpt a
        _ = (ℓ * ε + ν ^ ℓ) + K.iterate (ℓ * j) (outside (A (j + 1))) a := by
            rw [iterate_add, iterate_const]
        _ ≤ (ℓ * ε + ν ^ ℓ) + j * (ℓ * ε + ν ^ ℓ) := by
            linarith [ih (by omega) a ha]
        _ = ((j + 1 : ℕ) : ℝ) * (ℓ * ε + ν ^ ℓ) := by push_cast; ring
  intro a ha
  obtain ⟨j, rfl⟩ : ∃ j, T = j + 1 := ⟨T - 1, by omega⟩
  have hpt (b : α) : K.iterate ℓ (outside (A (j + 1))) b ≤ ℓ * ε + outside (A (j + 1)) b := by
    by_cases hb : b ∈ A (j + 1)
    · rw [outside_of_mem hb, add_zero]
      exact K.iterate_outside_le_of_stay _ hε (hstay (j + 1) (by omega) le_rfl) ℓ b hb
    · rw [outside_of_not_mem hb]
      have := K.iterate_le_one ℓ (outside_le_one (A (j + 1))) b
      have : (0 : ℝ) ≤ ℓ * ε := by positivity
      linarith
  have hsplit : ℓ * (j + 1) = ℓ * j + ℓ := by ring
  rw [event_eq_one_sub, hsplit, iterate_add_time]
  have hfin : K.iterate (ℓ * j) (K.iterate ℓ (outside (A (j + 1)))) a
      ≤ ℓ * ε + j * (ℓ * ε + ν ^ ℓ) := by
    calc K.iterate (ℓ * j) (K.iterate ℓ (outside (A (j + 1)))) a
        ≤ K.iterate (ℓ * j) (fun b => ℓ * ε + outside (A (j + 1)) b) a :=
          K.iterate_mono _ hpt a
      _ = ℓ * ε + K.iterate (ℓ * j) (outside (A (j + 1))) a := by
          rw [iterate_add, iterate_const]
      _ ≤ ℓ * ε + j * (ℓ * ε + ν ^ ℓ) := by
          linarith [hphase j le_rfl a ha]
  have hν' : (0 : ℝ) ≤ ν ^ ℓ := pow_nonneg hν ℓ
  push_cast
  nlinarith

/-! ### Phase calculus with a potential -/

/-- The phase of `a`: the largest `j ≤ J` with `a ∈ A j` (`0` if there is none). -/
noncomputable def phaseOf (A : ℕ → Set α) (J : ℕ) (a : α) : ℕ := by
  classical
  exact Nat.findGreatest (fun j => a ∈ A j) J

omit [Fintype α] in
lemma phaseOf_le (A : ℕ → Set α) (J : ℕ) (a : α) : phaseOf A J a ≤ J := by
  classical
  unfold phaseOf
  convert Nat.findGreatest_le J

omit [Fintype α] in
lemma mem_phaseOf {A : ℕ → Set α} {J : ℕ} {a : α} (h0 : a ∈ A 0) : a ∈ A (phaseOf A J a) := by
  classical
  unfold phaseOf
  convert Nat.findGreatest_spec (P := fun j => a ∈ A j) (Nat.zero_le J) h0

omit [Fintype α] in
lemma le_phaseOf {A : ℕ → Set α} {J j : ℕ} {a : α} (hj : j ≤ J) (h : a ∈ A j) :
    j ≤ phaseOf A J a := by
  classical
  unfold phaseOf
  convert Nat.le_findGreatest (P := fun j => a ∈ A j) hj h

/-- The phase potential: `0` on `A J`, and `λ^{J - j}` in phase `j` otherwise. -/
noncomputable def phasePot (A : ℕ → Set α) (J : ℕ) (lam : ℝ) (a : α) : ℝ := by
  classical
  exact if a ∈ A J then 0 else lam ^ (J - phaseOf A J a)

omit [Fintype α] in
lemma phasePot_le (A : ℕ → Set α) (J : ℕ) {lam : ℝ} (hlam : 1 ≤ lam) (a : α) :
    phasePot A J lam a ≤ lam ^ J := by
  unfold phasePot
  split_ifs
  · exact pow_nonneg (by linarith) _
  · exact pow_le_pow_right₀ hlam (Nat.sub_le _ _)

omit [Fintype α] in
lemma outside_le_phasePot (A : ℕ → Set α) (J : ℕ) {lam : ℝ} (hlam : 1 ≤ lam) (a : α) :
    outside (A J) a ≤ phasePot A J lam a := by
  unfold phasePot
  by_cases h : a ∈ A J
  · simp [outside_of_mem h, h]
  · simp only [outside_of_not_mem h, h, if_false]
    exact one_le_pow₀ hlam

/-- One step of the phase potential contracts it by `q + 1/λ` from every state of `A 0`. -/
lemma apply_phasePot_le (K : Dynamics.Kernel α) (A : ℕ → Set α) (J : ℕ) {q lam : ℝ}
    (hlam : 1 ≤ lam) (hclosed : ∀ j ≤ J, ∀ a b, a ∈ A j → (K a).weight b ≠ 0 → b ∈ A j)
    (hmove : ∀ j < J, ∀ a ∈ A j, 1 - q ≤ (K a).prob (· ∈ A (j + 1)))
    (a : α) (ha : a ∈ A 0) :
    K.apply (phasePot A J lam) a ≤ (q + 1 / lam) * phasePot A J lam a := by
  classical
  have hlam0 : 0 < lam := by linarith
  by_cases hJ : a ∈ A J
  · -- the chain stays in `A J`, where the potential vanishes
    have h := K.iterate_le_of_closed (· ∈ A J) (hclosed J le_rfl) (F := phasePot A J lam)
      (F' := fun _ => 0) (fun b hb => by simp [phasePot, hb]) 1 a hJ
    rw [K.iterate_const] at h
    have h0 : phasePot A J lam a = 0 := by simp [phasePot, hJ]
    rw [h0, mul_zero]
    exact h
  · set m := phaseOf A J a with hm
    have hmJ : m < J := by
      rcases lt_or_eq_of_le (phaseOf_le A J a) with h | h
      · exact h
      · exact absurd (h ▸ mem_phaseOf (J := J) ha) hJ
    have ham : a ∈ A m := mem_phaseOf ha
    have hpot : phasePot A J lam a = lam ^ (J - m) := by simp [phasePot, hJ, hm]
    have hsplit : J - m = (J - (m + 1)) + 1 := by omega
    -- pointwise bound on `A m`, which the chain does not leave
    have hpt : ∀ b, b ∈ A m → phasePot A J lam b ≤
        lam ^ (J - (m + 1)) + lam ^ (J - m) * outside (A (m + 1)) b := by
      intro b hb
      have hpow0 : 0 ≤ lam ^ (J - (m + 1)) := pow_nonneg hlam0.le _
      have hout : 0 ≤ lam ^ (J - m) * outside (A (m + 1)) b :=
        mul_nonneg (pow_nonneg hlam0.le _) (outside_nonneg _ _)
      by_cases hbJ : b ∈ A J
      · simp only [phasePot, hbJ, if_true]
        linarith
      · simp only [phasePot, hbJ, if_false]
        have hbm : m ≤ phaseOf A J b := le_phaseOf hmJ.le hb
        by_cases hb1 : b ∈ A (m + 1)
        · have hbm1 : m + 1 ≤ phaseOf A J b := le_phaseOf hmJ hb1
          have := pow_le_pow_right₀ hlam (Nat.sub_le_sub_left hbm1 J)
          linarith
        · rw [outside_of_not_mem hb1, mul_one]
          have := pow_le_pow_right₀ hlam (Nat.sub_le_sub_left hbm J)
          linarith
    have hE := K.iterate_le_of_closed (· ∈ A m) (hclosed m hmJ.le) hpt 1 a ham
    have hlin : K.iterate 1 (fun b => lam ^ (J - (m + 1)) + lam ^ (J - m) *
        outside (A (m + 1)) b) a =
        lam ^ (J - (m + 1)) + lam ^ (J - m) * (1 - (K a).prob (· ∈ A (m + 1))) := by
      rw [K.iterate_add, K.iterate_const, K.iterate_mul]
      simp only [iterate_succ, iterate_zero]
      rw [apply_outside]
    rw [hlin] at hE
    have hprob : 1 - (K a).prob (· ∈ A (m + 1)) ≤ q := by linarith [hmove m hmJ a ham]
    have hmul := mul_le_mul_of_nonneg_left hprob (pow_nonneg hlam0.le (J - m))
    have hid : lam ^ (J - (m + 1)) = 1 / lam * lam ^ (J - m) := by
      rw [hsplit, pow_succ]
      field_simp
    rw [hpot]
    calc K.apply (phasePot A J lam) a = K.iterate 1 (phasePot A J lam) a := rfl
      _ ≤ lam ^ (J - (m + 1)) + lam ^ (J - m) * (1 - (K a).prob (· ∈ A (m + 1))) := hE
      _ ≤ 1 / lam * lam ^ (J - m) + lam ^ (J - m) * q := by rw [hid]; linarith
      _ = (q + 1 / lam) * lam ^ (J - m) := by ring

/-- **Phase calculus.** Let every set `A j` (`j ≤ J`) be closed under the chain, and let one step
from `A j` enter `A (j + 1)` with probability at least `1 - q` for `j < J`. Then from any state
of `A 0`, the chain is outside `A J` after `t` steps with probability at most
`(q + 1/λ)^t λ^J`, for every `λ ≥ 1`. -/
theorem iterate_outside_le_of_phases (K : Dynamics.Kernel α) (A : ℕ → Set α) (J : ℕ)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 1 ≤ lam)
    (hclosed : ∀ j ≤ J, ∀ a b, a ∈ A j → (K a).weight b ≠ 0 → b ∈ A j)
    (hmove : ∀ j < J, ∀ a ∈ A j, 1 - q ≤ (K a).prob (· ∈ A (j + 1)))
    (a : α) (ha : a ∈ A 0) (t : ℕ) :
    K.iterate t (outside (A J)) a ≤ (q + 1 / lam) ^ t * lam ^ J := by
  have hlam0 : 0 < lam := by linarith
  have hθ : 0 ≤ q + 1 / lam := by positivity
  have hit := K.iterate_le_pow_of_closed (· ∈ A 0) (hclosed 0 (Nat.zero_le J))
    (phasePot A J lam) hθ (fun b hb => apply_phasePot_le K A J hlam hclosed hmove b hb) t a ha
  calc K.iterate t (outside (A J)) a ≤ K.iterate t (phasePot A J lam) a :=
        K.iterate_mono t (outside_le_phasePot A J hlam) a
    _ ≤ (q + 1 / lam) ^ t * phasePot A J lam a := hit
    _ ≤ (q + 1 / lam) ^ t * lam ^ J :=
        mul_le_mul_of_nonneg_left (phasePot_le A J hlam a) (pow_nonneg hθ t)

end Dynamics.Kernel
