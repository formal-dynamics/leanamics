import Voter.Model

/-! # Monochromatic-edge propagation (Lemma 2.1)

The graph argument concerns possible rounds, independently of numerical weights.
A monochromatic edge supplies a color that can be kept while its region grows.
-/
namespace Voter
open Finset Dynamics
variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- A possible simultaneous copying round on a graph. -/
def Possible (G : SimpleGraph V) (s t : Config V C) : Prop :=
  ∃ r : V → V, (∀ i, G.Adj i (r i)) ∧ step s r = t

/-- A nonbipartite graph has a monochromatic edge in every Boolean configuration. -/
lemma monochromatic_edge (G : SimpleGraph V) (hn : ¬ G.Colorable 2) (s : Config V Bool) :
    ∃ i j, G.Adj i j ∧ s i = s j := by
  by_contra h
  push_neg at h
  apply hn
  have hc : G.Coloring Bool := SimpleGraph.Coloring.mk s (fun hij => h _ _ hij)
  simpa using hc.colorable

/-- Every nonempty proper vertex set in a connected graph has an edge leaving it. -/
lemma boundary_edge (G : SimpleGraph V) (hc : G.Connected) (S : Finset V)
    (hne : S.Nonempty) (hproper : S ≠ univ) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ G.Adj i j := by
  by_contra h
  push_neg at h
  have hclosed {i j : V} (hi : i ∈ S) (hij : G.Adj i j) : j ∈ S := by
    by_contra hj
    exact h i hi j hj hij
  obtain ⟨i, hi⟩ := hne
  apply hproper
  apply eq_univ_of_forall
  intro j
  obtain ⟨w⟩ := hc.preconnected i j
  induction w with
  | nil => exact hi
  | @cons u v w huv tail ih => exact ih (hclosed hi huv)

/-- A monochromatic region with an internal neighbor at each vertex can grow to
consensus along a finite sequence of possible rounds. -/
lemma propagate_region (G : SimpleGraph V) (hc : G.Connected)
    (neighbors : ∀ i, ∃ j, G.Adj i j) (s : Config V C) (S : Finset V) (c : C)
    (hne : S.Nonempty) (hcolor : ∀ i ∈ S, s i = c)
    (hinternal : ∀ i ∈ S, ∃ j ∈ S, G.Adj i j) :
    Relation.ReflTransGen (Possible G) s (fun _ => c) := by
  classical
  generalize hd : (univ \ S).card = d
  induction d using Nat.strong_induction_on generalizing s S with
  | h d ih =>
    by_cases hfull : S = univ
    · have hs : s = fun _ => c := funext fun i => hcolor i (hfull ▸ mem_univ i)
      rw [hs]
    · obtain ⟨i, hi, j, hj, hij⟩ := boundary_edge G hc S hne hfull
      have hr : ∀ v, ∃ u, G.Adj v u ∧ (v ∈ insert j S → u ∈ S) := by
        intro v
        by_cases hv : v ∈ S
        · obtain ⟨u, hu, hvu⟩ := hinternal v hv
          exact ⟨u, hvu, fun _ => hu⟩
        · by_cases hvj : v = j
          · subst v
            exact ⟨i, hij.symm, fun _ => hi⟩
          · obtain ⟨u, hu⟩ := neighbors v
            exact ⟨u, hu, fun habs => False.elim (by simpa [hv, hvj] using habs)⟩
      choose r hr using hr
      have hsmaller : (univ \ insert j S).card < d := by
        rw [← hd]
        apply card_lt_card
        apply ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset_sdiff_right (u := univ) (subset_insert j S), ?_⟩
        intro heq
        have hjmem : j ∈ univ \ S := by simp [hj]
        rw [← heq] at hjmem
        simpa using hjmem
      have hnext := ih _ hsmaller (step s r) (insert j S) (by simp)
        (fun v hv => hcolor (r v) ((hr v).2 hv))
        (by
          intro v hv
          rcases mem_insert.mp hv with rfl | hv
          · exact ⟨i, mem_insert_of_mem hi, hij.symm⟩
          · obtain ⟨u, hu, hvu⟩ := hinternal v hv
            exact ⟨u, mem_insert_of_mem hu, hvu⟩) rfl
      exact (Relation.ReflTransGen.single ⟨r, fun v => (hr v).1, rfl⟩).trans hnext

/-- Every Boolean configuration can reach consensus on a connected nonbipartite graph. -/
theorem possible_consensus (G : SimpleGraph V) (hc : G.Connected)
    (hn : ¬ G.Colorable 2) (neighbors : ∀ i, ∃ j, G.Adj i j) (s : Config V Bool) :
    ∃ c, Relation.ReflTransGen (Possible G) s (fun _ => c) := by
  obtain ⟨i, j, hij, hs⟩ := monochromatic_edge G hn s
  refine ⟨s i, propagate_region G hc neighbors s {i, j} (s i) (by simp) ?_ ?_⟩
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · rfl
    · exact hs.symm
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨j, by simp, hij⟩
    · exact ⟨i, by simp, hij.symm⟩

end Voter
