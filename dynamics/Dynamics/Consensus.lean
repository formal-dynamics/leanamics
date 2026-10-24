import Dynamics.Absorption
import Dynamics.OptionalStopping

/-!
# Consensus and fixation

Configurations are maps `s : V → C` (a colour, opinion or type per vertex). A consensus is a
constant configuration, and `nonConsensus` is the indicator of not being one: the survival
indicator for which the absorption theorem (`Kernel.finite_absorption`) is applied in the model
packages (`Voter.survival`, `Moran.unfixed`, `Undecided.notMono`).

* `Kernel.nonConsensus_step`: if consensus configurations are absorbing, `K nonConsensus ≤
  nonConsensus`, the absorption hypothesis of `finite_absorption`.
* `Kernel.iterate_nonConsensus_bool`: for two colours, finite-time non-consensus is the event of
  being neither all-`true` nor all-`false`.
* `Kernel.iSup_consensus_of_harmonic`: the gambler's ruin formula, fixation in all-`true` from
  a harmonic observable (the two-consensus case of `iSup_event_of_invariant`), and its
  normalized form `Kernel.iSup_consensus_of_invariant`.
-/

namespace Dynamics
open Filter Topology

variable {V C : Type*}

/-- Indicator of non-consensus: `0` on constant configurations, `1` otherwise. -/
noncomputable def nonConsensus (s : V → C) : ℝ := by
  classical
  exact if ∃ c, s = fun _ => c then 0 else 1

lemma nonConsensus_binary (s : V → C) : nonConsensus s = 0 ∨ nonConsensus s = 1 := by
  unfold nonConsensus
  split <;> simp

lemma nonConsensus_le_one (s : V → C) : nonConsensus s ≤ 1 := by
  rcases nonConsensus_binary s with h | h <;> simp [h]

@[simp] lemma nonConsensus_const (c : C) : nonConsensus (fun _ : V => c) = 0 := by
  unfold nonConsensus
  exact if_pos ⟨c, rfl⟩

lemma nonConsensus_of_not (s : V → C) (h : ¬ ∃ c, s = fun _ => c) : nonConsensus s = 1 := by
  unfold nonConsensus
  exact if_neg h

variable [Fintype V]

/-- For two colours, non-consensus is being neither all-`true` nor all-`false`. -/
lemma nonConsensus_bool (s : V → Bool) :
    nonConsensus s = if ¬ s = (fun _ => true) ∧ ¬ s = (fun _ => false) then 1 else 0 := by
  by_cases h : ∃ c, s = fun _ => c
  · obtain ⟨c, rfl⟩ := h
    rw [nonConsensus_const]
    cases c <;> simp
  · rw [nonConsensus_of_not s h, if_pos ⟨fun h' => h ⟨true, h'⟩, fun h' => h ⟨false, h'⟩⟩]

namespace Kernel
variable [DecidableEq V]

/-- If every consensus configuration is absorbing, the non-consensus probability does not
increase in one step. -/
lemma nonConsensus_step [Fintype C] (K : Kernel (V → C))
    (habs : ∀ c (f : (V → C) → ℝ), K.apply f (fun _ => c) = f (fun _ => c)) (s : V → C) :
    K.apply nonConsensus s ≤ nonConsensus s := by
  by_cases hs : ∃ c, s = fun _ => c
  · obtain ⟨c, rfl⟩ := hs
    rw [habs c]
  · rw [nonConsensus_of_not s hs, apply]
    calc (K s).expect nonConsensus ≤ (K s).expect (fun _ => 1) :=
          (K s).expect_mono nonConsensus_le_one
      _ = 1 := (K s).expect_const 1

/-- For two colours, finite-time non-consensus is an event. -/
lemma iterate_nonConsensus_bool (K : Kernel (V → Bool)) (n : ℕ) (s : V → Bool) :
    K.iterate n nonConsensus s =
      K.event (fun t => ¬ t = (fun _ => true) ∧ ¬ t = (fun _ => false)) n s := by
  rw [K.event_eq_iterate]
  exact congrFun (congrArg (K.iterate n) (funext nonConsensus_bool)) s

/-- **Gambler's ruin for two consensus configurations.** If `φ` is harmonic for `K` and takes
different values on all-`true` and all-`false`, all-`true` is absorbing, and the non-consensus
probability tends to zero, then the probability of fixation in all-`true` from `s` is
`(φ(s) − φ(all-false)) / (φ(all-true) − φ(all-false))`. For instance, a harmonic `q^k`, with `k`
the number of `true` vertices out of `n`, gives `(1 - q^k) / (1 - q^n)`, and a harmonic `k` gives
`k / n`. This is `iSup_event_of_invariant` for the two consensus configurations. -/
theorem iSup_consensus_of_harmonic (K : Kernel (V → Bool)) (φ : (V → Bool) → ℝ)
    (hinv : K.apply φ = φ) (hne : φ (fun _ => true) ≠ φ (fun _ => false))
    (habs : (K fun _ => true).prob (· = fun _ => true) = 1) (s : V → Bool)
    (hsurv : Tendsto (fun n => K.iterate n nonConsensus s) atTop (𝓝 0)) :
    ⨆ T, K.event (· = fun _ => true) T s =
      (φ s - φ (fun _ => false)) / (φ (fun _ => true) - φ (fun _ => false)) :=
  K.iSup_event_of_invariant φ (· = fun _ => true) (· = fun _ => false) _ _
    (fun _ ha => ha ▸ rfl) (fun _ hb => hb ▸ rfl) hne (fun _ ha => ha ▸ habs) s
    (fun T => congrFun (K.iterate_invariant hinv T) s)
    (by simpa only [iterate_nonConsensus_bool] using hsurv)

/-- **Fixation from an invariant.** If `ψ` is harmonic for `K`, equals `1` on all-`true` and `0`
on all-`false`, all-`true` is absorbing, and the non-consensus probability tends to zero, then
`ψ` is the probability of fixation in all-`true`. This is the normalized case of
`iSup_consensus_of_harmonic`. -/
theorem iSup_consensus_of_invariant (K : Kernel (V → Bool)) (ψ : (V → Bool) → ℝ)
    (hinv : K.apply ψ = ψ) (hone : ψ (fun _ => true) = 1) (hzero : ψ (fun _ => false) = 0)
    (habs : (K fun _ => true).prob (· = fun _ => true) = 1) (s : V → Bool)
    (hsurv : Tendsto (fun n => K.iterate n nonConsensus s) atTop (𝓝 0)) :
    ⨆ T, K.event (· = fun _ => true) T s = ψ s := by
  have h := K.iSup_consensus_of_harmonic ψ hinv (by rw [hone, hzero]; exact one_ne_zero) habs s
    hsurv
  rwa [hone, hzero, sub_zero, sub_zero, div_one] at h

end Kernel
end Dynamics
