import Voter.Main

/-! # Multiple colors by indicator projection (Section 2.3) -/
namespace Voter
open Dynamics Filter Topology
variable {V C D : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Transition expectations commute with arbitrary color projections. -/
lemma iterate_project [Fintype C] [Fintype D] (H : Kernel V) (g : C → D)
    (f : Config V D → ℝ) (n : ℕ) (s : Config V C) :
    (transition H).iterate n f (g ∘ s) =
      (transition H).iterate n (fun t => f (g ∘ t)) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Kernel.iterate_succ, Kernel.iterate_succ, transition_apply, transition_apply]
    unfold round
    congr 1
    funext r
    exact ih (step s r)

/-- Boolean indicator projection for one color. -/
noncomputable def colorIndicator (c : C) (x : C) : Bool := by
  classical
  exact decide (x = c)

lemma allColor_project (c : C) (s : Config V C) :
    allColor true (colorIndicator c ∘ s) = allColor c s := by
  classical
  have he : (colorIndicator c ∘ s = fun _ => true) ↔ (s = fun _ => c) := by
    simp [funext_iff, colorIndicator]
  simp only [allColor, he]

lemma colorProbability_project [Fintype C] (H : Kernel V) (c : C) (n : ℕ)
    (s : Config V C) :
    colorProbability H true n (colorIndicator c ∘ s) = colorProbability H c n s := by
  unfold colorProbability
  rw [iterate_project]
  simp_rw [allColor_project]

lemma eventualColor_project [Fintype C] (H : Kernel V) (c : C) (s : Config V C) :
    eventualColor H true (colorIndicator c ∘ s) = eventualColor H c s := by
  unfold eventualColor
  exact iSup_congr fun n => colorProbability_project H c n s

/-- **Section 2.3.** Consensus in any specified color has its initial stationary mass. -/
theorem color_consensus_probability [Fintype C]
    (G : SimpleGraph V) (hc : G.Connected) (hn : ¬ G.Colorable 2)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (p : Distribution V) (hp : H.Stationary p) (s : Config V C) (c : C) :
    eventualColor H c s = p.prob (fun i => s i = c) := by
  classical
  rw [← eventualColor_project, consensus_probability G hc hn H hsupport p hp]
  simp [whiteMass, mass, colorIndicator, Distribution.prob]

/-- The eventual probabilities over all colors sum to one. -/
theorem sum_color_consensus_probability [Fintype C]
    (G : SimpleGraph V) (hc : G.Connected) (hn : ¬ G.Colorable 2)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (p : Distribution V) (hp : H.Stationary p) (s : Config V C) :
    ∑ c, eventualColor H c s = 1 := by
  classical
  simp_rw [color_consensus_probability G hc hn H hsupport p hp s]
  simp only [Distribution.prob, Distribution.expect, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simpa using p.sum_one

end Voter
