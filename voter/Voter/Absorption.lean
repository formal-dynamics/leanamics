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

/-- A round of positive probability for the kernel `H`: every vertex samples a vertex in the
support of its row, and all vertices copy simultaneously. -/
def KernelPossible {C : Type*} (H : Kernel V) (s t : Config V C) : Prop :=
  ∃ r : V → V, (∀ i, 0 < (H i).weight (r i)) ∧ step s r = t

omit [DecidableEq V] in
/-- If `H` charges every edge of `G`, every possible graph round is a round in the kernel
support. -/
lemma kernelPossible_of_possible {C : Type*} {G : SimpleGraph V} {H : Kernel V}
    (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j) {s t : Config V C}
    (h : Possible G s t) : KernelPossible H s t :=
  let ⟨r, hr, hst⟩ := h
  ⟨r, fun i => hsupport i (r i) (hr i), hst⟩

/-- Every round in the kernel support has positive probability. -/
lemma kernelPossible_positive (H : Kernel V) {s t : Config V Bool}
    (h : KernelPossible H s t) : 0 < (transition H s).weight t := by
  obtain ⟨r, hr, rfl⟩ := h
  exact (Distribution.independent H).map_weight_pos (step s) r (prod_pos fun i _ => hr i)

/-- Every graph-allowed round has positive probability. -/
lemma possible_positive (G : SimpleGraph V) (H : Kernel V)
    (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    {s t : Config V Bool} (h : Possible G s t) : 0 < (transition H s).weight t :=
  kernelPossible_positive H (kernelPossible_of_possible hsupport h)

/-- A chain of rounds in the kernel support reaching consensus makes the nonconsensus
probability drop below one at some finite time. -/
lemma reachable_success_of_kernelPossible (H : Kernel V) {s : Config V Bool} {c : Bool}
    (h : Relation.ReflTransGen (KernelPossible H) s (fun _ => c)) :
    ∃ n, (transition H).iterate n survival s < 1 :=
  (transition H).exists_iterate_lt_one_of_reachable nonConsensus_le_one
    (Relation.ReflTransGen.mono (fun _ _ => kernelPossible_positive H) _ _ h)
    (nonConsensus_const c)

/-- If every configuration reaches consensus through rounds in the kernel support, the
nonconsensus probability tends to zero: the probabilistic half of Lemma 2.1, shared by
`consensus_tendsto` and `consensus_tendsto_of_selfLoop`. -/
lemma consensus_tendsto_of_kernelPossible (H : Kernel V)
    (hreach : ∀ t : Config V Bool, ∃ c, Relation.ReflTransGen (KernelPossible H) t (fun _ => c))
    (s : Config V Bool) :
    Tendsto (fun n => (transition H).iterate n survival s) atTop (𝓝 0) := by
  apply (transition H).finite_absorption survival nonConsensus_binary
    ((transition H).nonConsensus_step (transition_constant H))
  intro t
  obtain ⟨c, hpath⟩ := hreach t
  exact reachable_success_of_kernelPossible H hpath

/-- Nonconsensus probability tends to zero (Lemma 2.1). -/
theorem consensus_tendsto (G : SimpleGraph V) (hc : G.Connected) (hn : ¬ G.Colorable 2)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (s : Config V Bool) :
    Tendsto (fun n => (transition H).iterate n survival s) atTop (𝓝 0) := by
  have neighbors (i : V) : ∃ j, G.Adj i j := by
    obtain ⟨a, b, hab, _⟩ := monochromatic_edge G hn (fun _ => false)
    haveI : Nontrivial V := ⟨⟨a, b, hab.ne⟩⟩
    exact hc.preconnected.exists_adj_of_nontrivial i
  refine consensus_tendsto_of_kernelPossible H (fun t => ?_) s
  obtain ⟨c, hpath⟩ := possible_consensus G hc hn neighbors t
  exact ⟨c, Relation.ReflTransGen.mono (fun _ _ => kernelPossible_of_possible hsupport) _ _ hpath⟩

end Voter
