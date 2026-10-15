import Dynamics.Kernel

/-!
# Processes driven by independent uniform rounds

Many dynamics in this repository are given by a deterministic update
`step : S → R → S` applied to a sequence of i.i.d. uniform rounds `r : R`,
with expectations computed by `expList`. `ofStep step` is the corresponding
finite Markov kernel, and `iterate_ofStep` identifies its iterates with the
`expList` expectations, so results about kernels (for instance
`Dynamics.Kernel.nested_phases`) apply to such round-based processes.
The probability `missProb` of missing a target after `T` rounds composes over stages
(`missProb_comp`) and, for a target closed under every round, amplifies over consecutive blocks
(`missProb_amplify`).
-/

namespace Dynamics.Kernel
variable {S R : Type*} [Fintype S] [Fintype R] [Nonempty R]

/-- The Markov kernel of one uniformly random round of `step`. -/
noncomputable def ofStep (step : S → R → S) : Dynamics.Kernel S :=
  fun s => (Distribution.uniform R).map (step s)

lemma apply_ofStep (step : S → R → S) (f : S → ℝ) (s : S) :
    (ofStep step).apply f s = avg (fun r => f (step s r)) := by
  simp only [apply, ofStep, Distribution.map_expect, Distribution.uniform_expect]

/-- Every outcome of one round has positive probability. -/
lemma ofStep_weight_pos (step : S → R → S) (s : S) (r : R) :
    0 < (ofStep step s).weight (step s r) :=
  (Distribution.uniform R).map_weight_pos (step s) r (inv_pos.mpr card_cast_pos)

lemma prob_ofStep (step : S → R → S) (P : S → Prop) (s : S) :
    (ofStep step s).prob P = avg (fun r => by classical exact if P (step s r) then 1 else 0) := by
  classical
  simp only [Distribution.prob, ofStep, Distribution.map_expect, Distribution.uniform_expect]

/-- Iterating the kernel is averaging over `T` i.i.d. uniform rounds. -/
lemma iterate_ofStep (step : S → R → S) (T : ℕ) (f : S → ℝ) (s : S) :
    (ofStep step).iterate T f s = expList R T (fun l => f (l.foldl step s)) := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    rw [iterate_succ, apply_ofStep, expList_succ]
    congr 1
    funext r
    rw [ih]
    rfl

lemma event_ofStep (step : S → R → S) (P : S → Prop) (T : ℕ) (s : S) :
    (ofStep step).event P T s
      = expList R T (fun l => by classical exact if P (l.foldl step s) then 1 else 0) := by
  classical
  unfold event
  rw [iterate_ofStep]

end Dynamics.Kernel

namespace Dynamics
variable {S R : Type*} [Fintype R] [Nonempty R]

/-- **Escaping a moving target.** If a round-based process starts in `G 0`
and, for every `t < T`, one round from any state of `G t` misses `G (t + 1)`
with probability at most `p`, then after `T` rounds it lies outside `G T` with
probability at most `T p`. This is the union bound over rounds used by lower
bounds such as Theorem 4.2 of Becchetti et al. (SPAA 2014). -/
theorem expList_escape (step : S → R → S) {p : ℝ} (hp : 0 ≤ p) :
    ∀ (T : ℕ) (G : ℕ → Set S) (x : S), x ∈ G 0 →
      (∀ t < T, ∀ y ∈ G t,
        avg (fun r => by classical exact if step y r ∈ G (t + 1) then (0 : ℝ) else 1) ≤ p) →
      expList R T (fun l => by classical exact if l.foldl step x ∈ G T then (0 : ℝ) else 1)
        ≤ T * p := by
  classical
  intro T
  induction T with
  | zero =>
    intro G x hx _
    simp [hx]
  | succ T ih =>
    intro G x hx hG
    rw [expList_succ]
    have hpt (r : R) :
        expList R T (fun l => if (r :: l).foldl step x ∈ G (T + 1) then (0 : ℝ) else 1)
          ≤ T * p + (if step x r ∈ G 1 then (0 : ℝ) else 1) := by
      by_cases hr : step x r ∈ G 1
      · rw [if_pos hr, add_zero]
        exact ih (fun t => G (t + 1)) (step x r) hr
          (fun t ht y hy => hG (t + 1) (by omega) y hy)
      · rw [if_neg hr]
        have h1 : expList R T
            (fun l => if (r :: l).foldl step x ∈ G (T + 1) then (0 : ℝ) else 1) ≤ 1 := by
          calc _ ≤ expList R T (fun _ => (1 : ℝ)) :=
                expList_le_expList fun l => by split <;> norm_num
            _ = 1 := expList_const T 1
        have : (0 : ℝ) ≤ T * p := by positivity
        linarith
    calc avg (fun r => expList R T
            (fun l => if (r :: l).foldl step x ∈ G (T + 1) then (0 : ℝ) else 1))
        ≤ avg (fun r => T * p + (if step x r ∈ G 1 then (0 : ℝ) else 1)) := avg_le_avg hpt
      _ = T * p + avg (fun r => if step x r ∈ G 1 then (0 : ℝ) else 1) := by
          rw [avg_add, avg_const]
      _ ≤ T * p + p := by linarith [hG 0 (by omega) x hx]
      _ = ((T + 1 : ℕ) : ℝ) * p := by push_cast; ring

/-! ### Missing a target after i.i.d. rounds -/

omit [Nonempty R] in
/-- Probability that the process driven by `T` i.i.d. uniform rounds of `step`, started at `s`,
is outside `B` after `T` rounds. -/
noncomputable def missProb (step : S → R → S) (B : Set S) (T : ℕ) (s : S) : ℝ := by
  classical
  exact expList R T (fun l => if l.foldl step s ∈ B then 0 else 1)

omit [Nonempty R] in
/-- With no round, the process misses `B` exactly when it starts outside `B`. -/
lemma missProb_zero (step : S → R → S) (B : Set S) (s : S) :
    missProb step B 0 s = by classical exact if s ∈ B then 0 else 1 := rfl

omit [Nonempty R] in
/-- The first round is averaged out first. -/
lemma missProb_succ (step : S → R → S) (B : Set S) (T : ℕ) (s : S) :
    missProb step B (T + 1) s = avg (fun r => missProb step B T (step s r)) := rfl

omit [Nonempty R] in
/-- A missing probability is nonnegative. -/
lemma missProb_nonneg (step : S → R → S) (B : Set S) (T : ℕ) (s : S) :
    0 ≤ missProb step B T s := by
  classical
  unfold missProb
  exact expList_nonneg fun l => by split <;> norm_num

/-- A missing probability is at most `1`. -/
lemma missProb_le_one (step : S → R → S) (B : Set S) (T : ℕ) (s : S) :
    missProb step B T s ≤ 1 := by
  classical
  unfold missProb
  calc _ ≤ expList R T (fun _ => (1 : ℝ)) := expList_le_expList fun l => by split <;> norm_num
    _ = 1 := expList_const T 1

omit [Nonempty R] in
/-- Missing a smaller set is more likely. -/
lemma missProb_mono (step : S → R → S) {B B' : Set S} (h : B ⊆ B') (T : ℕ) (s : S) :
    missProb step B' T s ≤ missProb step B T s := by
  classical
  unfold missProb
  refine expList_le_expList fun l => ?_
  by_cases hB : l.foldl step s ∈ B
  · simp [hB, h hB]
  · rw [if_neg hB]
    split <;> norm_num

/-- **Composition of stages** (Markov property): if from every state of `B` the process misses
`D` after `T₂` rounds with probability at most `e`, then from `s` it misses `D` after `T₁ + T₂`
rounds with probability at most `missProb step B T₁ s + e`. -/
lemma missProb_comp (step : S → R → S) {B D : Set S} {T₁ T₂ : ℕ} {e : ℝ} (he : 0 ≤ e)
    (hD : ∀ y ∈ B, missProb step D T₂ y ≤ e) (s : S) :
    missProb step D (T₁ + T₂) s ≤ missProb step B T₁ s + e := by
  classical
  have key (l₁ : List R) :
      expList R T₂ (fun l₂ => if (l₁ ++ l₂).foldl step s ∈ D then (0 : ℝ) else 1)
        = missProb step D T₂ (l₁.foldl step s) := by
    simp only [missProb, List.foldl_append]
  have hpt (l₁ : List R) : missProb step D T₂ (l₁.foldl step s)
      ≤ (if l₁.foldl step s ∈ B then (0 : ℝ) else 1) + e := by
    by_cases hB : l₁.foldl step s ∈ B
    · rw [if_pos hB, zero_add]
      exact hD _ hB
    · rw [if_neg hB]
      linarith [missProb_le_one step D T₂ (l₁.foldl step s)]
  calc missProb step D (T₁ + T₂) s
      = expList R T₁ (fun l₁ => missProb step D T₂ (l₁.foldl step s)) := by
        rw [← funext key]
        exact expList_append T₁ T₂ _
    _ ≤ expList R T₁ (fun l₁ => (if l₁.foldl step s ∈ B then (0 : ℝ) else 1) + e) :=
        expList_le_expList hpt
    _ = missProb step B T₁ s + e := by
        rw [expList_add, expList_const]
        rfl

omit [Nonempty R] in
/-- A target closed under every round is never left. -/
lemma missProb_of_closed (step : S → R → S) {B : Set S} (hB : ∀ y ∈ B, ∀ r, step y r ∈ B)
    {y : S} (hy : y ∈ B) (T : ℕ) : missProb step B T y = 0 := by
  classical
  have hfold (l : List R) : ∀ z ∈ B, l.foldl step z ∈ B := by
    induction l with
    | nil => exact fun z hz => hz
    | cons r l ih => exact fun z hz => ih _ (hB z hz r)
  unfold missProb
  simp_rw [if_pos (hfold _ y hy)]
  exact expList_zero_fun T

/-- The probability of missing a target closed under every round does not increase with time. -/
lemma missProb_antitone (step : S → R → S) {B : Set S} (hB : ∀ y ∈ B, ∀ r, step y r ∈ B) (s : S)
    {T T' : ℕ} (h : T ≤ T') : missProb step B T' s ≤ missProb step B T s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := missProb_comp step (B := B) (D := B) (T₁ := T) (T₂ := k) le_rfl
    (fun y hy => (missProb_of_closed step hB hy k).le) s
  linarith

omit [Nonempty R] in
/-- **Amplification** (the `expList` form of `Dynamics.Kernel.event_amplify`): if a target closed
under every round is missed after `T` rounds with probability at most `p` from every state, then
it is missed after `k T` rounds with probability at most `p ^ k`, since each block of `T` rounds
fails independently of the previous ones. -/
lemma missProb_amplify (step : S → R → S) {B : Set S} (hB : ∀ y ∈ B, ∀ r, step y r ∈ B)
    {T : ℕ} {p : ℝ} (hp : ∀ y, missProb step B T y ≤ p) (k : ℕ) (s : S) :
    missProb step B (k * T) s ≤ p ^ k := by
  classical
  have hp0 : 0 ≤ p := (missProb_nonneg step B T s).trans (hp s)
  induction k with
  | zero =>
    rw [Nat.zero_mul, missProb_zero, pow_zero]
    split <;> norm_num
  | succ k ih =>
    -- the last block fails only if the first `k` blocks have failed, then w.p. at most `p`
    have hpt (l₁ : List R) : missProb step B T (l₁.foldl step s)
        ≤ p * (if l₁.foldl step s ∈ B then (0 : ℝ) else 1) := by
      by_cases hl : l₁.foldl step s ∈ B
      · rw [missProb_of_closed step hB hl, if_pos hl, mul_zero]
      · rw [if_neg hl, mul_one]
        exact hp _
    calc missProb step B ((k + 1) * T) s
        = expList R (k * T) (fun l₁ => missProb step B T (l₁.foldl step s)) := by
          have key (l₁ : List R) :
              expList R T (fun l₂ => if (l₁ ++ l₂).foldl step s ∈ B then (0 : ℝ) else 1)
                = missProb step B T (l₁.foldl step s) := by
            simp only [missProb, List.foldl_append]
          rw [Nat.succ_mul, ← funext key]
          exact expList_append _ _ _
      _ ≤ expList R (k * T) (fun l₁ => p * (if l₁.foldl step s ∈ B then (0 : ℝ) else 1)) :=
          expList_le_expList hpt
      _ = p * missProb step B (k * T) s := by
          rw [expList_const_mul]
          rfl
      _ ≤ p * p ^ k := mul_le_mul_of_nonneg_left ih hp0
      _ = p ^ (k + 1) := by ring

end Dynamics
