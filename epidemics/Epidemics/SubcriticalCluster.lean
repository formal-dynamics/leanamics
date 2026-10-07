import Epidemics.ReedFrost

/-! # Clusters of a set of vertices (EPI-2)

The *reachable set* `reachSet H D` of a finite set `D` of vertices: the vertices joined to `D` by a
path in `H`. For a single vertex it is the vertex set of its connected component, measured in
Mathlib by `(H.connectedComponentMk s).supp.ncard`; for the initial set `I₀` of a Reed–Frost
epidemic in the percolated graph it is the final outbreak (EPI-1).

This file collects the pathwise facts used by the subcritical percolation proofs:
* how the reachable set behaves when `D` is closed under `H`, when a neighbour is added to `D`, and
  when `H` loses edges whose endpoints lie in `D`;
* the distance between two vertices of a component is smaller than its size;
* small components force a small final outbreak and an early end of the Reed–Frost epidemic.
-/

namespace Epidemics
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices joined to some vertex of `D` by a path in `H`. -/
noncomputable def reachSet (H : SimpleGraph V) (D : Finset V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ u ∈ D, H.Reachable u v

lemma mem_reachSet {H : SimpleGraph V} {D : Finset V} {v : V} :
    v ∈ reachSet H D ↔ ∃ u ∈ D, H.Reachable u v := by
  unfold reachSet
  simp

lemma subset_reachSet (H : SimpleGraph V) (D : Finset V) : D ⊆ reachSet H D :=
  fun v hv => mem_reachSet.mpr ⟨v, hv, Reachable.refl v⟩

omit [Fintype V] [DecidableEq V] in
/-- A walk starting in a set closed under the edges of `H` stays in it. -/
lemma mem_of_walk {H : SimpleGraph V} {D : Finset V} (h : ∀ u ∈ D, ∀ v, H.Adj u v → v ∈ D) :
    ∀ {u v : V}, H.Walk u v → u ∈ D → v ∈ D
  | _, _, .nil, hu => hu
  | _, _, .cons hadj p, hu => mem_of_walk h p (h _ hu _ hadj)

/-- A set closed under the edges of `H` is its own reachable set. -/
lemma reachSet_eq_self {H : SimpleGraph V} {D : Finset V}
    (h : ∀ u ∈ D, ∀ v, H.Adj u v → v ∈ D) : reachSet H D = D := by
  refine Subset.antisymm (fun v hv => ?_) (subset_reachSet H D)
  obtain ⟨u, hu, ⟨p⟩⟩ := mem_reachSet.mp hv
  exact mem_of_walk h p hu

/-- Adding a neighbour of `D` to `D` does not change the reachable set. -/
lemma reachSet_insert {H : SimpleGraph V} {D : Finset V} {w x : V} (hw : w ∈ D)
    (hwx : H.Adj w x) : reachSet H (insert x D) = reachSet H D := by
  ext v
  simp only [mem_reachSet, mem_insert]
  constructor
  · rintro ⟨u, rfl | hu, hr⟩
    · exact ⟨w, hw, hwx.reachable.trans hr⟩
    · exact ⟨u, hu, hr⟩
  · rintro ⟨u, hu, hr⟩
    exact ⟨u, Or.inr hu, hr⟩

omit [Fintype V] [DecidableEq V] in
/-- A walk of `H` either survives in a subgraph `H'` that only misses edges ending in `S`, or
its end is reached in `H'` from a vertex of `S`. -/
lemma reachable_or_of_walk {H H' : SimpleGraph V} {S : Finset V} (hle : H' ≤ H)
    (hS : ∀ u v, H.Adj u v → ¬H'.Adj u v → v ∈ S) :
    ∀ {u v : V}, H.Walk u v → H'.Reachable u v ∨ ∃ u' ∈ S, H'.Reachable u' v
  | _, _, .nil => Or.inl (Reachable.refl _)
  | u, _, @Walk.cons _ _ _ y _ hadj p => by
    rcases reachable_or_of_walk hle hS p with h | h
    · by_cases h' : H'.Adj u y
      · exact Or.inl (h'.reachable.trans h)
      · exact Or.inr ⟨y, hS _ _ hadj h', h⟩
    · exact Or.inr h

/-- Deleting edges of `H` whose endpoints lie in `S` does not change the reachable set of `S`. -/
lemma reachSet_eq_of_le {H H' : SimpleGraph V} {S : Finset V} (hle : H' ≤ H)
    (hS : ∀ u v, H.Adj u v → ¬H'.Adj u v → v ∈ S) : reachSet H' S = reachSet H S := by
  ext v
  simp only [mem_reachSet]
  constructor
  · rintro ⟨u, hu, hr⟩
    exact ⟨u, hu, hr.mono hle⟩
  · rintro ⟨u, hu, ⟨p⟩⟩
    rcases reachable_or_of_walk hle hS p with h | h
    · exact ⟨u, hu, h⟩
    · exact h

/-- The component of `s` has as many vertices as the reachable set of `{s}`. -/
lemma ncard_supp_eq_card_reachSet (H : SimpleGraph V) (s : V) :
    (H.connectedComponentMk s).supp.ncard = (reachSet H {s}).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, mem_coe, mem_reachSet,
    mem_singleton, exists_eq_left]
  exact ⟨Reachable.symm, Reachable.symm⟩

/-- Two vertices of a component are at distance smaller than its number of vertices. -/
lemma dist_lt_ncard_supp {H : SimpleGraph V} {u v : V} (h : H.Reachable u v) :
    H.dist u v < (H.connectedComponentMk u).supp.ncard := by
  obtain ⟨p, hp, hlen⟩ := h.exists_path_of_dist
  rw [ncard_supp_eq_card_reachSet, ← hlen]
  have hsub : p.support.toFinset ⊆ reachSet H {u} := by
    intro y hy
    rw [List.mem_toFinset] at hy
    exact mem_reachSet.mpr ⟨u, mem_singleton_self u, (p.takeUntil y hy).reachable⟩
  calc p.length < p.support.length := by rw [Walk.length_support]; omega
    _ = p.support.toFinset.card := (List.toFinset_card_of_nodup hp.support_nodup).symm
    _ ≤ _ := card_le_card hsub

/-- The reachable set of `I₀` has at most `|I₀|` times the largest component size. -/
lemma card_reachSet_le (H : SimpleGraph V) (I₀ : Finset V) {L : ℝ}
    (h : ∀ u, ((H.connectedComponentMk u).supp.ncard : ℝ) ≤ L) :
    ((reachSet H I₀).card : ℝ) ≤ I₀.card * L := by
  have hsub : reachSet H I₀ ⊆ I₀.biUnion fun u => reachSet H {u} := by
    intro v hv
    obtain ⟨u, hu, hr⟩ := mem_reachSet.mp hv
    exact mem_biUnion.mpr ⟨u, hu, mem_reachSet.mpr ⟨u, mem_singleton_self u, hr⟩⟩
  calc ((reachSet H I₀).card : ℝ) ≤ ((I₀.biUnion fun u => reachSet H {u}).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ u ∈ I₀, ((reachSet H {u}).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _u ∈ I₀, L := sum_le_sum fun u _ => by rw [← ncard_supp_eq_card_reachSet]; exact h u
    _ = I₀.card * L := by rw [sum_const, nsmul_eq_mul]

/-- **Final size from component sizes**: if every component of the percolated graph has at most
`L` vertices, the Reed–Frost epidemic from `I₀` infects at most `|I₀| L` nodes. -/
lemma card_recovered_le (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool)
    (I₀ : Finset V) {L : ℝ} (h : ∀ u, (((perc G ω).connectedComponentMk u).supp.ncard : ℝ) ≤ L) :
    ((run G ω I₀ (Fintype.card V)).recovered.card : ℝ) ≤ I₀.card * L := by
  have heq : (run G ω I₀ (Fintype.card V)).recovered = reachSet (perc G ω) I₀ := by
    ext v
    rw [final_recovered_iff, mem_reachSet]
  rw [heq]
  exact card_reachSet_le _ I₀ h

/-- **Duration from component sizes**: if every component of the percolated graph has at most `k`
vertices, nobody is infected in round `k` of the Reed–Frost epidemic. -/
lemma infected_eq_empty_of_ncard_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (I₀ : Finset V) {k : ℕ}
    (h : ∀ u, ((perc G ω).connectedComponentMk u).supp.ncard ≤ k) :
    (run G ω I₀ k).infected = ∅ := by
  refine extinct_of_dist_lt G ω I₀ k fun v hv => ?_
  obtain ⟨u, hu, hr⟩ := (setDist_ne_top_iff (perc G ω) I₀).mp hv
  have hle : setDist (perc G ω) I₀ v ≤ (perc G ω).edist u v := by
    simpa [setDist] using biInf_le (s := (↑I₀ : Set V)) (fun w => (perc G ω).edist w v) hu
  rw [← hr.coe_dist_eq_edist] at hle
  exact hle.trans_lt (ENat.coe_lt_coe.mpr ((dist_lt_ncard_supp hr).trans_le (h u)))

end Epidemics
