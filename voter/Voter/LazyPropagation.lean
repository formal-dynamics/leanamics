import Voter.Absorption

/-! # Propagation through the kernel support (Lemma 2.1 with a self-loop)

The propagation half of Lemma 2.1 (`Voter.Graph`) only uses rounds in which every vertex copies
a graph neighbour, so it needs a monochromatic edge to start, hence a nonbipartite graph. Here a
round is possible when every vertex samples a vertex of positive weight in its row of the
kernel. Self-loops are then allowed, and a vertex that keeps its own colour with positive
probability is a monochromatic region on its own: this is the Remark on p. 254 of Hassin and
Peleg. The probabilistic half (`Voter.Absorption`) carries over unchanged.
-/

namespace Voter
open Finset Dynamics Filter Topology
variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- A round of positive probability for the kernel `H`: every vertex samples a vertex in the
support of its row, and all vertices copy simultaneously. -/
def KernelPossible (H : Kernel V) (s t : Config V C) : Prop :=
  ∃ r : V → V, (∀ i, 0 < (H i).weight (r i)) ∧ step s r = t

/-- Every finite distribution charges some point. -/
lemma exists_weight_pos {α : Type*} [Fintype α] (p : Distribution α) : ∃ a, 0 < p.weight a := by
  obtain ⟨a, -, ha⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := p.weight)
    (by rw [p.sum_one]; exact one_ne_zero)
  exact ⟨a, lt_of_le_of_ne (p.nonneg a) (Ne.symm ha)⟩

/-- Every round in the kernel support has positive probability. -/
lemma kernelPossible_positive (H : Kernel V) {s t : Config V Bool}
    (h : KernelPossible H s t) : 0 < (transition H s).weight t := by
  classical
  obtain ⟨r, hr, rfl⟩ := h
  dsimp only [transition, Distribution.map]
  apply lt_of_lt_of_le ?_ (single_le_sum (fun a _ => ?_) (mem_univ r))
  · simp only
    exact prod_pos fun i _ => hr i
  · split
    · exact (Distribution.independent H).nonneg _
    · rfl

/-- A chain of rounds in the kernel support reaching consensus makes the nonconsensus
probability drop below one at some finite time. -/
lemma reachable_success_of_kernelPossible (H : Kernel V) {s : Config V Bool} {c : Bool}
    (h : Relation.ReflTransGen (KernelPossible H) s (fun _ => c)) :
    ∃ n, (transition H).iterate n survival s < 1 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, by simp⟩
  | @head s t hst htail ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, expect_lt_one (transition H s) ((transition H).iterate n survival) ?_ t
      (kernelPossible_positive H hst) hn⟩
    intro u
    simpa [Kernel.iterate_const] using
      (transition H).iterate_mono n survival_le_one u

/-- **Lemma 2.1, propagation through the kernel support.** On a connected graph whose edges are
charged by `H`, a monochromatic region in which every vertex charges a vertex of the region
grows to consensus along a finite chain of rounds in the kernel support. -/
lemma propagate_kernel_region (G : SimpleGraph V) (hc : G.Connected) (H : Kernel V)
    (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j) (s : Config V C) (S : Finset V) (c : C)
    (hne : S.Nonempty) (hcolor : ∀ i ∈ S, s i = c)
    (hinternal : ∀ i ∈ S, ∃ j ∈ S, 0 < (H i).weight j) :
    Relation.ReflTransGen (KernelPossible H) s (fun _ => c) := by
  classical
  generalize hd : (univ \ S).card = d
  induction d using Nat.strong_induction_on generalizing s S with
  | h d ih =>
    by_cases hfull : S = univ
    · have hs : s = fun _ => c := funext fun i => hcolor i (hfull ▸ mem_univ i)
      rw [hs]
    · obtain ⟨i, hi, j, hj, hij⟩ := boundary_edge G hc S hne hfull
      have hr : ∀ v, ∃ u, 0 < (H v).weight u ∧ (v ∈ insert j S → u ∈ S) := by
        intro v
        by_cases hv : v ∈ S
        · obtain ⟨u, hu, hvu⟩ := hinternal v hv
          exact ⟨u, hvu, fun _ => hu⟩
        · by_cases hvj : v = j
          · subst v
            exact ⟨i, hsupport j i hij.symm, fun _ => hi⟩
          · obtain ⟨u, hu⟩ := exists_weight_pos (H v)
            exact ⟨u, hu, fun habs => False.elim (by simp [hv, hvj] at habs)⟩
      choose r hr using hr
      have hsmaller : (univ \ insert j S).card < d := by
        rw [← hd]
        apply card_lt_card
        apply ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset_sdiff_right (u := univ) (subset_insert j S), ?_⟩
        intro heq
        have hjmem : j ∈ univ \ S := by simp [hj]
        rw [← heq] at hjmem
        simp at hjmem
      have hnext := ih _ hsmaller (step s r) (insert j S) (by simp)
        (fun v hv => hcolor (r v) ((hr v).2 hv))
        (by
          intro v hv
          rcases mem_insert.mp hv with rfl | hv
          · exact ⟨i, mem_insert_of_mem hi, hsupport _ i hij.symm⟩
          · obtain ⟨u, hu, hvu⟩ := hinternal v hv
            exact ⟨u, mem_insert_of_mem hu, hvu⟩) rfl
      exact (Relation.ReflTransGen.single ⟨r, fun v => (hr v).1, rfl⟩).trans hnext

/-- **Remark on p. 254, possibility half.** If `v` keeps its colour with positive probability,
every configuration can reach consensus in the colour of `v` through rounds in the kernel
support, on any connected graph whose edges are charged by `H`. -/
lemma kernelPossible_consensus_of_selfLoop (G : SimpleGraph V) (hc : G.Connected)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    {v : V} (hv : 0 < (H v).weight v) (s : Config V C) :
    Relation.ReflTransGen (KernelPossible H) s (fun _ => s v) := by
  refine propagate_kernel_region G hc H hsupport s {v} (s v) (singleton_nonempty v) ?_ ?_
  · intro i hi
    rw [mem_singleton.mp hi]
  · intro i hi
    rw [mem_singleton.mp hi]
    exact ⟨v, mem_singleton_self v, hv⟩

/-- **Lemma 2.1 with the Remark on p. 254.** With a self-loop of positive weight, nonconsensus
probability tends to zero on every connected graph whose edges are charged by `H`, bipartite
or not. -/
theorem consensus_tendsto_of_selfLoop (G : SimpleGraph V) (hc : G.Connected)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (hloop : ∃ v, 0 < (H v).weight v) (s : Config V Bool) :
    Tendsto (fun n => (transition H).iterate n survival s) atTop (𝓝 0) := by
  obtain ⟨v, hv⟩ := hloop
  apply (transition H).finite_absorption survival survival_binary (survival_step H)
  intro t
  exact reachable_success_of_kernelPossible H
    (kernelPossible_consensus_of_selfLoop G hc H hsupport hv t)

end Voter
