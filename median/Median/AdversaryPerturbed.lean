import Dynamics.Rounds

/-! # Perturbed round-based processes

Generic tools behind the adversarial results of `Median/Adversary.lean`. A round-based process
`step : S → R → S`, driven by i.i.d. uniform rounds, is *perturbed within `Adm`* along a function
`P : List R → S` of the rounds played so far when `P [] = s` and, after every round `r`, the new
state `P (l ++ [r])` is related by `Adm` to the unperturbed `step (P l) r`. Since `P` may depend
on the whole list of rounds, this covers adaptive adversaries; the process is no longer a Markov
chain on `S`, but every bound below only needs one-round estimates that hold for *every*
admissible perturbation of the round.

* `Perturbed.shift`: the process seen after the rounds `l₀` is again perturbed;
* `expList_le_of_drift_perturbed` (**fixed-time drift**): if every perturbed round maps `φ` to at
  most `ρ φ + ε` in expectation, then after `T` rounds `𝔼 φ ≤ ρ ^ T φ + T ε`;
* `expList_path_perturbed` (**chains of moves**): if every perturbed round from `B i` misses
  `B (i + 1)` with probability at most `ε`, the whole path `P (l.take t) ∈ B t`, `t ≤ T`, fails
  with probability at most `T ε` (the perturbed, path form of `Dynamics.expList_escape`);
* `expList_le_of_length`, `expList_le_of_split`: `expList` only looks at lists of the right
  length, and splits into two phases.

None of them mentions the median rule; they are candidates for `Dynamics/`.
-/

namespace Median
open Dynamics

/-- Indicator of the failure of a proposition: `0` if it holds, `1` otherwise. -/
noncomputable def failInd (p : Prop) : ℝ := by
  classical
  exact if p then 0 else 1

lemma failInd_of {p : Prop} (h : p) : failInd p = 0 := by
  classical
  simp [failInd, h]

lemma failInd_of_not {p : Prop} (h : ¬ p) : failInd p = 1 := by
  classical
  simp [failInd, h]

lemma failInd_nonneg (p : Prop) : 0 ≤ failInd p := by
  classical
  unfold failInd
  split_ifs <;> norm_num

lemma failInd_le_one (p : Prop) : failInd p ≤ 1 := by
  classical
  unfold failInd
  split_ifs <;> norm_num

lemma failInd_mono {p q : Prop} (h : p → q) : failInd q ≤ failInd p := by
  by_cases hp : p
  · rw [failInd_of (h hp), failInd_of hp]
  · rw [failInd_of_not hp]
    exact failInd_le_one q

variable {S R : Type*} [Fintype R] [Nonempty R]

/-- `P` is a run of `step` from `s` perturbed within `Adm`: it starts at `s` and, after every
round `r`, the new state is related by `Adm` to the output of `step`. -/
def Perturbed (step : S → R → S) (Adm : S → S → Prop) (s : S) (P : List R → S) : Prop :=
  P [] = s ∧ ∀ l r, Adm (step (P l) r) (P (l ++ [r]))

omit [Fintype R] [Nonempty R] in
/-- After the rounds `l₀`, a perturbed run is again a perturbed run. -/
lemma Perturbed.shift {step : S → R → S} {Adm : S → S → Prop} {s : S} {P : List R → S}
    (hP : Perturbed step Adm s P) (l₀ : List R) :
    Perturbed step Adm (P l₀) (fun l => P (l₀ ++ l)) :=
  ⟨by simp, fun l r => by simpa [List.append_assoc] using hP.2 (l₀ ++ l) r⟩

omit [Fintype R] [Nonempty R] in
/-- The first round of a perturbed run is a perturbation of one round from its start. -/
lemma Perturbed.first {step : S → R → S} {Adm : S → S → Prop} {s : S} {P : List R → S}
    (hP : Perturbed step Adm s P) (r : R) : Adm (step s r) (P [r]) := by
  have h := hP.2 [] r
  rwa [hP.1] at h

/-- **Fixed-time drift for perturbed runs.** If every perturbed round maps the potential `φ` to
at most `ρ φ + ε` in expectation (`0 ≤ ρ ≤ 1`, `0 ≤ ε`), then after `T` rounds the expected
potential is at most `ρ ^ T φ + T ε`. -/
lemma expList_le_of_drift_perturbed (step : S → R → S) (Adm : S → S → Prop) (φ : S → ℝ)
    {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hε : 0 ≤ ε)
    (hφ : ∀ s (g : R → S), (∀ r, Adm (step s r) (g r)) → avg (fun r => φ (g r)) ≤ ρ * φ s + ε) :
    ∀ (T : ℕ) (s : S) (P : List R → S), Perturbed step Adm s P →
      expList R T (fun l => φ (P l)) ≤ ρ ^ T * φ s + T * ε := by
  intro T
  induction T with
  | zero =>
    intro s P hP
    simp [hP.1]
  | succ T ih =>
    intro s P hP
    rw [expList_succ]
    have h1 : ∀ r, expList R T (fun l => φ (P (r :: l))) ≤ ρ ^ T * φ (P [r]) + T * ε :=
      fun r => ih (P [r]) (fun l => P ([r] ++ l)) (hP.shift [r])
    have hρT : ρ ^ T ≤ 1 := pow_le_one₀ hρ0 hρ1
    have hρT0 : 0 ≤ ρ ^ T := pow_nonneg hρ0 T
    calc avg (fun r => expList R T fun l => φ (P (r :: l)))
        ≤ avg (fun r => ρ ^ T * φ (P [r]) + T * ε) := avg_le_avg h1
      _ = ρ ^ T * avg (fun r => φ (P [r])) + T * ε := by
          rw [avg_add, avg_const_mul, avg_const]
      _ ≤ ρ ^ T * (ρ * φ s + ε) + T * ε := by
          gcongr
          exact hφ s (fun r => P [r]) hP.first
      _ ≤ ρ ^ (T + 1) * φ s + ((T + 1 : ℕ) : ℝ) * ε := by
          have := mul_le_mul_of_nonneg_right hρT hε
          push_cast
          rw [pow_succ]
          nlinarith

/-- **Chains of moves for perturbed runs.** If, for every `i`, every perturbed round from a
state of `B i` misses `B (i + 1)` with probability at most `ε`, then a perturbed run from `B 0`
fails to follow `P (l.take t) ∈ B t` for all `t ≤ T` with probability at most `T ε`. -/
lemma expList_path_perturbed (step : S → R → S) (Adm : S → S → Prop) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (T : ℕ) (B : ℕ → Set S),
      (∀ i, ∀ s ∈ B i, ∀ g : R → S, (∀ r, Adm (step s r) (g r)) →
        avg (fun r => failInd (g r ∈ B (i + 1))) ≤ ε) →
      ∀ (s : S) (P : List R → S), Perturbed step Adm s P → s ∈ B 0 →
        expList R T (fun l => failInd (∀ t ≤ T, P (l.take t) ∈ B t)) ≤ T * ε := by
  intro T
  induction T with
  | zero =>
    intro B _ s P hP hs
    simp only [expList_zero, CharP.cast_eq_zero, zero_mul]
    refine le_of_eq (failInd_of fun t ht => ?_)
    rw [Nat.le_zero.mp ht, List.take_zero, hP.1]
    exact hs
  | succ T ih =>
    intro B hB s P hP hs
    rw [expList_succ]
    -- after the first round `r`, either the run left `B 1`, or the rest is a shorter chain
    have hr : ∀ r, expList R T (fun l => failInd (∀ t ≤ T + 1, P ((r :: l).take t) ∈ B t))
        ≤ T * ε + failInd (P [r] ∈ B 1) := by
      intro r
      by_cases h1 : P [r] ∈ B 1
      · rw [failInd_of h1, add_zero]
        refine le_trans (expList_le_expList fun l => failInd_mono ?_)
          (ih (fun i => B (i + 1)) (fun i => hB (i + 1)) (P [r]) (fun l => P ([r] ++ l))
            (hP.shift [r]) h1)
        intro h t ht
        rcases t with _ | t
        · rw [List.take_zero, hP.1]
          exact hs
        · exact h t (by omega)
      · rw [failInd_of_not h1]
        calc expList R T (fun l => failInd (∀ t ≤ T + 1, P ((r :: l).take t) ∈ B t))
            ≤ expList R T (fun _ => (1 : ℝ)) := expList_le_expList fun l => failInd_le_one _
          _ = 1 := expList_const _ _
          _ ≤ T * ε + 1 := le_add_of_nonneg_left (by positivity)
    calc avg (fun r => expList R T fun l => failInd (∀ t ≤ T + 1, P ((r :: l).take t) ∈ B t))
        ≤ avg (fun r => T * ε + failInd (P [r] ∈ B 1)) := avg_le_avg hr
      _ = T * ε + avg (fun r => failInd (P [r] ∈ B 1)) := by rw [avg_add, avg_const]
      _ ≤ T * ε + ε := by
          gcongr
          exact hB 0 s hs (fun r => P [r]) hP.first
      _ = ((T + 1 : ℕ) : ℝ) * ε := by push_cast; ring

omit [Nonempty R] in
/-- `expList R T` only evaluates its argument on lists of length `T`. -/
lemma expList_le_of_length {T : ℕ} {F G : List R → ℝ} (h : ∀ l, l.length = T → F l ≤ G l) :
    expList R T F ≤ expList R T G := by
  induction T generalizing F G with
  | zero => exact h [] rfl
  | succ T ih =>
    rw [expList_succ, expList_succ]
    exact avg_le_avg fun a => ih fun l hl => h (a :: l) (by simp [hl])

/-- **Two phases.** If, after any first phase `l₁` of `T₁` rounds, the expectation of `Φ` over
the second phase is at most `a + Ψ l₁`, then over both phases it is at most `a + 𝔼 Ψ`. -/
lemma expList_le_of_split {T₁ T₂ : ℕ} {Φ Ψ : List R → ℝ} {a : ℝ}
    (h : ∀ l₁, l₁.length = T₁ → expList R T₂ (fun l₂ => Φ (l₁ ++ l₂)) ≤ a + Ψ l₁) :
    expList R (T₁ + T₂) Φ ≤ a + expList R T₁ Ψ := by
  rw [expList_append]
  calc expList R T₁ (fun l₁ => expList R T₂ fun l₂ => Φ (l₁ ++ l₂))
      ≤ expList R T₁ (fun l₁ => a + Ψ l₁) := expList_le_of_length h
    _ = a + expList R T₁ Ψ := by rw [expList_add, expList_const]

end Median
