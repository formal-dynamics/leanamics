import Dynamics.Kernel

/-!
# Processes driven by independent uniform rounds

Many dynamics in this repository are given by a deterministic update
`step : S → R → S` applied to a sequence of i.i.d. uniform rounds `r : R`,
with expectations computed by `expList`. `ofStep step` is the corresponding
finite Markov kernel, and `iterate_ofStep` identifies its iterates with the
`expList` expectations, so results about kernels (for instance
`Dynamics.Kernel.nested_phases`) apply to such round-based processes.
-/

namespace Dynamics.Kernel
variable {S R : Type*} [Fintype S] [Fintype R] [Nonempty R]

/-- The Markov kernel of one uniformly random round of `step`. -/
noncomputable def ofStep (step : S → R → S) : Dynamics.Kernel S :=
  fun s => (Distribution.uniform R).map (step s)

lemma apply_ofStep (step : S → R → S) (f : S → ℝ) (s : S) :
    (ofStep step).apply f s = avg (fun r => f (step s r)) := by
  simp only [apply, ofStep, Distribution.map_expect, Distribution.uniform_expect]

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

end Dynamics
