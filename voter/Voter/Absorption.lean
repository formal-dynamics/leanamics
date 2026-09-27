import Voter.Graph
import Dynamics.Absorption

/-! # Almost-sure consensus from graph propagation -/
namespace Voter
open Finset Dynamics Filter Topology
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Indicator of nonconsensus. -/
noncomputable def survival (s : Config V Bool) : ℝ := by
  classical
  exact if ∃ c, s = fun _ => c then 0 else 1

omit [DecidableEq V] in
lemma survival_binary (s : Config V Bool) : survival s = 0 ∨ survival s = 1 := by
  classical
  unfold survival
  split <;> simp

omit [DecidableEq V] in
@[simp] lemma survival_constant (c : Bool) : survival (fun _ : V => c) = 0 := by
  unfold survival
  exact if_pos ⟨c, rfl⟩

omit [DecidableEq V] in
lemma survival_nonneg (s : Config V Bool) : 0 ≤ survival s := by
  rcases survival_binary s with h | h <;> simp [h]

omit [DecidableEq V] in
lemma survival_le_one (s : Config V Bool) : survival s ≤ 1 := by
  rcases survival_binary s with h | h <;> simp [h]

/-- Consensus configurations are absorbing. -/
lemma transition_constant {C : Type*} [Fintype C] (H : Kernel V) (c : C) (f : Config V C → ℝ) :
    (transition H).apply f (fun _ => c) = f (fun _ => c) := by
  rw [transition_apply]
  unfold round
  simp only [step_constant]
  exact (Distribution.independent H).expect_const _

lemma survival_step (H : Kernel V) (s : Config V Bool) :
    (transition H).apply survival s ≤ survival s := by
  classical
  by_cases hs : ∃ c, s = fun _ => c
  · obtain ⟨c, rfl⟩ := hs
    simp [transition_constant]
  · rw [survival, if_neg hs]
    calc (transition H).apply survival s ≤ (transition H s).expect (fun _ => 1) :=
          (transition H s).expect_mono survival_le_one
         _ = 1 := (transition H s).expect_const 1

/-- Every graph-allowed round has positive probability. -/
lemma possible_positive (G : SimpleGraph V) (H : Kernel V)
    (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    {s t : Config V Bool} (h : Possible G s t) : 0 < (transition H s).weight t := by
  classical
  obtain ⟨r, hr, rfl⟩ := h
  dsimp only [transition, Distribution.map]
  apply lt_of_lt_of_le ?_ (single_le_sum (fun a _ => ?_) (mem_univ r))
  · simp only
    exact prod_pos fun i _ => hsupport i (r i) (hr i)
  · split
    · exact (Distribution.independent H).nonneg _
    · rfl

/-- A positive transition to a state with success probability makes success possible here. -/
lemma expect_lt_one {α : Type*} [Fintype α] (p : Distribution α) (f : α → ℝ)
    (hf : ∀ a, f a ≤ 1) (b : α) (hb : 0 < p.weight b) (hfb : f b < 1) :
    p.expect f < 1 := by
  calc p.expect f < p.expect (fun _ => 1) :=
        sum_lt_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a) (p.nonneg a))
          ⟨b, mem_univ b, mul_lt_mul_of_pos_left hfb hb⟩
       _ = 1 := p.expect_const 1

lemma reachable_success (G : SimpleGraph V) (H : Kernel V)
    (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    {s : Config V Bool} {c : Bool}
    (h : Relation.ReflTransGen (Possible G) s (fun _ => c)) :
    ∃ n, (transition H).iterate n survival s < 1 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, by simp⟩
  | @head s t hst htail ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, expect_lt_one (transition H s) ((transition H).iterate n survival) ?_ t
      (possible_positive G H hsupport hst) hn⟩
    intro u
    simpa [Kernel.iterate_const] using
      (transition H).iterate_mono n survival_le_one u

/-- Nonconsensus probability tends to zero (Lemma 2.1). -/
theorem consensus_tendsto (G : SimpleGraph V) (hc : G.Connected) (hn : ¬ G.Colorable 2)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (s : Config V Bool) :
    Tendsto (fun n => (transition H).iterate n survival s) atTop (𝓝 0) := by
  have neighbors (i : V) : ∃ j, G.Adj i j := by
    obtain ⟨a, b, hab, _⟩ := monochromatic_edge G hn (fun _ => false)
    haveI : Nontrivial V := ⟨⟨a, b, hab.ne⟩⟩
    exact hc.preconnected.exists_adj_of_nontrivial i
  apply (transition H).finite_absorption survival survival_binary (survival_step H)
  intro t
  obtain ⟨c, hpath⟩ := possible_consensus G hc hn neighbors t
  exact reachable_success G H hsupport hpath

end Voter
