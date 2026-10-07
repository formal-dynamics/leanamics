import Voter.Absorption
import Dynamics.OptionalStopping
import Dynamics.Stationary

/-! # Consensus probability (Theorem 2.1)

Eventual consensus probability is the supremum of increasing finite-time
probabilities. The proof bounds the discrepancy from invariant white mass by
the probability of nonconsensus, then passes to the limit.
-/
namespace Voter
open Dynamics Finset Filter Topology
variable {V C : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Indicator of a specified consensus color. -/
noncomputable def allColor (c : C) (s : Config V C) : ℝ := by
  classical
  exact if s = fun _ => c then 1 else 0

/-- Probability that all vertices have color `c` at time `n`. -/
noncomputable def colorProbability [Fintype C] (H : Kernel V) (c : C) (n : ℕ)
    (s : Config V C) : ℝ := (transition H).iterate n (allColor c) s

/-- Eventual probability, defined from the finite-time consensus probabilities. -/
noncomputable def eventualColor [Fintype C] (H : Kernel V) (c : C)
    (s : Config V C) : ℝ := ⨆ n, colorProbability H c n s

omit [DecidableEq V] [Nonempty V] in
lemma allColor_nonneg (c : C) (s : Config V C) : 0 ≤ allColor c s := by
  classical
  unfold allColor
  split <;> norm_num

omit [DecidableEq V] [Nonempty V] in
lemma allColor_le_one (c : C) (s : Config V C) : allColor c s ≤ 1 := by
  classical
  unfold allColor
  split <;> norm_num

omit [Nonempty V] in
lemma colorProbability_le_one [Fintype C] (H : Kernel V) (c : C) (n : ℕ)
    (s : Config V C) : colorProbability H c n s ≤ 1 := by
  simpa [colorProbability, Kernel.iterate_const] using
    (transition H).iterate_mono n (allColor_le_one c) s

omit [Nonempty V] in
lemma colorProbability_mono [Fintype C] (H : Kernel V) (c : C) (s : Config V C) :
    Monotone (fun n => colorProbability H c n s) := by
  classical
  have hstep (t : Config V C) : allColor c t ≤ (transition H).apply (allColor c) t := by
    by_cases ht : t = fun _ => c
    · subst t
      rw [transition_apply]
      change allColor c (fun _ => c) ≤
        (Distribution.independent H).expect (fun _ => allColor c (fun _ => c))
      rw [Distribution.expect_const]
    · rw [allColor, if_neg ht]
      exact (transition H t).expect_nonneg (allColor_nonneg c)
  apply monotone_nat_of_le_succ
  intro n
  change (transition H).iterate n (allColor c) s ≤ (transition H).iterate (n + 1) (allColor c) s
  rw [Kernel.iterate_add_time]
  exact (transition H).iterate_mono n hstep s

omit [Nonempty V] in
lemma colorProbability_tendsto [Fintype C] (H : Kernel V) (c : C) (s : Config V C) :
    Tendsto (fun n => colorProbability H c n s) atTop (𝓝 (eventualColor H c s)) :=
  tendsto_atTop_ciSup (colorProbability_mono H c s)
    ⟨1, by rintro _ ⟨n, rfl⟩; exact colorProbability_le_one H c n s⟩

omit [Nonempty V] in
/-- A constant configuration retains its color at every finite time. -/
lemma colorProbability_constant [Fintype C] (H : Kernel V) (c : C) (n : ℕ) :
    colorProbability H c n (fun _ => c) = 1 := by
  induction n with
  | zero => simp [colorProbability, allColor]
  | succ n ih =>
    change (transition H).apply ((transition H).iterate n (allColor c)) (fun _ => c) = 1
    rw [transition_constant]
    exact ih

omit [Nonempty V] in
/-- A constant configuration reaches its own consensus color with probability one. -/
lemma eventualColor_constant [Fintype C] (H : Kernel V) (c : C) :
    eventualColor H c (fun _ => c) = 1 := by
  simp [eventualColor, colorProbability_constant]

/-- Stationary white mass. -/
noncomputable def whiteMass (p : Distribution V) : Config V Bool → ℝ :=
  mass p (fun b => if b then 1 else 0)

omit [DecidableEq V] [Nonempty V] in
lemma whiteMass_nonneg (p : Distribution V) (s : Config V Bool) : 0 ≤ whiteMass p s :=
  p.expect_nonneg (fun i => by dsimp; split <;> norm_num)

omit [DecidableEq V] [Nonempty V] in
lemma whiteMass_le_one (p : Distribution V) (s : Config V Bool) : whiteMass p s ≤ 1 := by
  calc whiteMass p s ≤ p.expect (fun _ => 1) := p.expect_mono (fun i => by dsimp; split <;> norm_num)
       _ = 1 := p.expect_const 1

omit [DecidableEq V] [Nonempty V] in
/-- A constant configuration has white mass `1` if white, `0` if black. -/
lemma whiteMass_const (p : Distribution V) (c : Bool) :
    whiteMass p (fun _ => c) = if c then 1 else 0 :=
  p.expect_const _

omit [Nonempty V] in
/-- Finite-time consensus on a color is an event. -/
lemma colorProbability_eq_event [Fintype C] (H : Kernel V) (c : C) (n : ℕ) (s : Config V C) :
    colorProbability H c n s = (transition H).event (· = fun _ => c) n s := by
  unfold colorProbability allColor Kernel.event
  congr 1
  funext t
  congr

omit [DecidableEq V] in
lemma whiteMass_bounds (p : Distribution V) (s : Config V Bool) :
    allColor true s ≤ whiteMass p s ∧ whiteMass p s ≤ allColor true s + survival s := by
  classical
  constructor
  · by_cases hs : s = fun _ => true
    · subst s
      simp [allColor, whiteMass, mass]
    · simpa [allColor, hs] using whiteMass_nonneg p s
  · by_cases hs : ∃ c, s = fun _ => c
    · obtain ⟨c, rfl⟩ := hs
      cases c <;> simp [allColor, whiteMass, mass, funext_iff]
    · have hz : survival s = 1 := by simp [survival, hs]
      rw [hz]
      linarith [whiteMass_le_one p s, allColor_nonneg true s]

/-- The finite-time discrepancy is at most nonconsensus probability (Lemma 2.2). -/
lemma whiteProbability_error (H : Kernel V) (p : Distribution V) (hp : H.Stationary p)
    (n : ℕ) (s : Config V Bool) :
    0 ≤ whiteMass p s - colorProbability H true n s ∧
      whiteMass p s - colorProbability H true n s ≤ (transition H).iterate n survival s := by
  have hS (t : Config V Bool) (h1 : ¬ t = fun _ => true) (h2 : ¬ t = fun _ => false) :
      0 ≤ whiteMass p t - 0 ∧ whiteMass p t - 0 ≤ 1 := by
    have hb := whiteMass_bounds p t
    rw [show allColor true t = 0 by simp [allColor, h1], survival_eq, if_pos ⟨h1, h2⟩] at hb
    constructor <;> linarith [hb.1, hb.2]
  have h := (transition H).event_error_of_invariant (whiteMass p) (· = fun _ => true)
    (· = fun _ => false) 1 0 0 1 (fun _ ha => by simp [ha, whiteMass_const])
    (fun _ hb => by simp [hb, whiteMass_const]) hS s n
    (iterate_mass H p hp (fun b : Bool => if b then 1 else 0) n s)
  rw [← colorProbability_eq_event, ← iterate_survival] at h
  simpa using h

/-- Finite-time all-white probability converges to initial stationary white mass. -/
theorem whiteProbability_tendsto (G : SimpleGraph V) (hc : G.Connected) (hn : ¬ G.Colorable 2)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (p : Distribution V) (hp : H.Stationary p) (s : Config V Bool) :
    Tendsto (fun n => colorProbability H true n s) atTop (𝓝 (whiteMass p s)) := by
  have hz : Tendsto (fun n => whiteMass p s - colorProbability H true n s) atTop (𝓝 0) :=
    squeeze_zero (fun n => (whiteProbability_error H p hp n s).1)
      (fun n => (whiteProbability_error H p hp n s).2) (consensus_tendsto G hc hn H hsupport s)
  have hcst : Tendsto (fun _ : ℕ => whiteMass p s) atTop (𝓝 (whiteMass p s)) := tendsto_const_nhds
  simpa using hcst.sub hz

/-- **Hassin–Peleg Theorem 2.1.** Eventual all-white consensus probability is
exactly the stationary weight of the initially white vertices. -/
theorem consensus_probability (G : SimpleGraph V) (hc : G.Connected) (hn : ¬ G.Colorable 2)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (p : Distribution V) (hp : H.Stationary p) (s : Config V Bool) :
    eventualColor H true s = whiteMass p s :=
  tendsto_nhds_unique (colorProbability_tendsto H true s)
    (whiteProbability_tendsto G hc hn H hsupport p hp s)

end Voter
