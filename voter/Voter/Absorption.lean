import Voter.Graph
import Dynamics.Consensus

/-! # Almost-sure consensus from graph propagation -/
namespace Voter
open Finset Dynamics Filter Topology
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Indicator of nonconsensus (`Dynamics.nonConsensus` for two colours). -/
noncomputable abbrev survival (s : Config V Bool) : ℝ := nonConsensus s

omit [DecidableEq V] in
/-- Nonconsensus indicates the configurations that are neither all-white nor all-black. -/
lemma survival_eq (s : Config V Bool) :
    survival s = if ¬ s = (fun _ => true) ∧ ¬ s = (fun _ => false) then 1 else 0 :=
  nonConsensus_bool s

/-- Finite-time nonconsensus as an event. -/
lemma iterate_survival (K : Kernel (Config V Bool)) (n : ℕ) (s : Config V Bool) :
    K.iterate n survival s =
      K.event (fun t => ¬ t = (fun _ => true) ∧ ¬ t = (fun _ => false)) n s :=
  K.iterate_nonConsensus_bool n s

/-- Consensus configurations are absorbing. -/
lemma transition_constant {C : Type*} [Fintype C] (H : Kernel V) (c : C) (f : Config V C → ℝ) :
    (transition H).apply f (fun _ => c) = f (fun _ => c) := by
  rw [transition_apply]
  unfold round
  simp only [step_constant]
  exact (Distribution.independent H).expect_const _

/-- Every graph-allowed round has positive probability. -/
lemma possible_positive (G : SimpleGraph V) (H : Kernel V)
    (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    {s t : Config V Bool} (h : Possible G s t) : 0 < (transition H s).weight t := by
  obtain ⟨r, hr, rfl⟩ := h
  exact (Distribution.independent H).map_weight_pos (step s) r
    (prod_pos fun i _ => hsupport i (r i) (hr i))

/-- Nonconsensus probability tends to zero (Lemma 2.1). -/
theorem consensus_tendsto (G : SimpleGraph V) (hc : G.Connected) (hn : ¬ G.Colorable 2)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (s : Config V Bool) :
    Tendsto (fun n => (transition H).iterate n survival s) atTop (𝓝 0) := by
  have neighbors (i : V) : ∃ j, G.Adj i j := by
    obtain ⟨a, b, hab, _⟩ := monochromatic_edge G hn (fun _ => false)
    haveI : Nontrivial V := ⟨⟨a, b, hab.ne⟩⟩
    exact hc.preconnected.exists_adj_of_nontrivial i
  apply (transition H).finite_absorption survival nonConsensus_binary
    ((transition H).nonConsensus_step (transition_constant H))
  intro t
  obtain ⟨c, hpath⟩ := possible_consensus G hc hn neighbors t
  exact (transition H).exists_iterate_lt_one_of_reachable nonConsensus_le_one
    (Relation.ReflTransGen.mono (fun _ _ => possible_positive G H hsupport) _ _ hpath)
    (nonConsensus_const c)

end Voter
