import Voter.MeetingTime

/-! # The bipartite double cover of a graph (VOT-6, plain walk)

Hassin–Peleg, proof of Lemma 2.4 (uniform case, no self-loops): the graph `G̃` on two copies
`V × {0, 1}` of the vertex set, with an edge between `(a, i)` and `(b, j)` exactly when `a ∼ b`
in `G` and `i ≠ j`. This is the bipartite double cover (tensor product `G × K₂`).

* A uniform-neighbour step of `G̃` from `(x, i)` is a uniform-neighbour step of `G` from `x`
  together with a flip of the layer (`uniformNeighbor_doubleCover_expect`).
* `G̃` is connected when `G` is connected and nonbipartite (`doubleCover_connected`): a walk
  of `G` lifts to `G̃`, flipping the layer at every step, and an odd closed walk corrects
  the parity of the endpoint layer.
* The hitting times of `G̃` (the lazy-normalised `hitting` of `Voter/MeetingHitting.lean`,
  i.e. twice the plain hitting times) are invariant under swapping the two layers
  (`hitting_doubleCover_flip`), since swapping is a graph automorphism and the hitting-time
  system has a unique solution (`hitting_unique`).
* Under a plain uniform-neighbour step away from the target, the lazy-normalised hitting time
  drops by `2` (`uniformNeighbor_expect_hitting`).
-/

namespace Voter
open Dynamics Finset Matrix

variable {V : Type*}

/-- The bipartite double cover `G × K₂` of `G` (Hassin–Peleg's graph `G̃` in the proof of
Lemma 2.4, uniform case): vertices `(a, i)` with `i` a layer, and `(a, i) ∼ (b, j)` iff
`a ∼ b` in `G` and `i ≠ j`. -/
def doubleCover (G : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj p q := G.Adj p.1 q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (doubleCover G).Adj :=
  fun p q => decidable_of_iff (G.Adj p.1 q.1 ∧ p.2 ≠ q.2) Iff.rfl

/-- Adjacency in the double cover. -/
@[simp] lemma doubleCover_adj (G : SimpleGraph V) {p q : V × Bool} :
    (doubleCover G).Adj p q ↔ G.Adj p.1 q.1 ∧ p.2 ≠ q.2 :=
  Iff.rfl

variable {G : SimpleGraph V}

/-- **Connectivity of the double cover.** If `G` is connected and nonbipartite (not
2-colourable), then its bipartite double cover is connected. This is where the
nonbipartiteness hypothesis of Hassin–Peleg (§2.1, Lemma 2.4) enters. -/
lemma doubleCover_connected (hc : G.Connected) (hnb : ¬ G.Colorable 2) :
    (doubleCover G).Connected := by
  sorry

variable [Fintype V] [DecidableRel G.Adj]

/-- Degrees in the double cover are the degrees in `G`. -/
lemma doubleCover_degree (x : V) (i : Bool) : (doubleCover G).degree (x, i) = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun q _ => q.1) ?_ ?_ ?_
  · intro q hq
    simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj] at hq ⊢
    exact hq.1
  · intro q₁ h₁ q₂ h₂ h
    simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj] at h₁ h₂
    ext
    · exact h
    · cases i <;> cases h₁q : q₁.2 <;> cases h₂q : q₂.2 <;> simp_all
  · intro a ha
    refine ⟨(a, !i), ?_, rfl⟩
    simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj] at ha ⊢
    exact ⟨ha, by cases i <;> simp⟩

/-- The double cover has positive degrees when `G` does. -/
lemma doubleCover_degree_pos (hd : ∀ i, 0 < G.degree i) (p : V × Bool) :
    0 < (doubleCover G).degree p := by
  obtain ⟨x, i⟩ := p
  rw [doubleCover_degree]
  exact hd x

/-- The volume of the double cover is twice the volume of `G`. -/
lemma volume_doubleCover : volume (doubleCover G) = 2 * volume G := by
  unfold volume
  rw [Fintype.sum_prod_type]
  simp only [doubleCover_degree, Fintype.sum_bool, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

variable [DecidableEq V]

/-- **Uniqueness of hitting times.** The hitting-time system `h y = 0`, `(L h) x = 2 d_x` for
`x ≠ y` of `Voter/MeetingHitting.lean` has exactly one solution, `hitting G hc y`. -/
lemma hitting_unique (hc : G.Connected) {y : V} {h : V → ℝ} (hy : h y = 0)
    (hlap : ∀ x, x ≠ y → (G.lapMatrix ℝ *ᵥ h) x = 2 * G.degree x) :
    h = hitting G hc y := by
  sorry

/-- **Layer symmetry.** Hitting times of the double cover are invariant under swapping the
two layers of both the start and the target. -/
lemma hitting_doubleCover_flip (hc' : (doubleCover G).Connected) (x y : V) (i j : Bool) :
    hitting (doubleCover G) hc' (y, !j) (x, !i) = hitting (doubleCover G) hc' (y, j) (x, i) := by
  sorry

/-- A plain uniform-neighbour step away from the target lowers the (lazy-normalised) hitting
time by `2` in expectation: `hitting` is twice the hitting time of the plain walk. -/
lemma uniformNeighbor_expect_hitting (hd : ∀ i, 0 < G.degree i) (hc : G.Connected) {x y : V}
    (hxy : x ≠ y) :
    (uniformNeighbor G hd x).expect (hitting G hc y) = hitting G hc y x - 2 := by
  sorry

/-- A uniform-neighbour step of the double cover from `(x, i)` is a uniform-neighbour step of
`G` from `x` followed by a flip of the layer. -/
lemma uniformNeighbor_doubleCover_expect (hd : ∀ i, 0 < G.degree i)
    (hd' : ∀ p, 0 < (doubleCover G).degree p) (x : V) (i : Bool) (f : V × Bool → ℝ) :
    (uniformNeighbor (doubleCover G) hd' (x, i)).expect f =
      (uniformNeighbor G hd x).expect fun a => f (a, !i) := by
  sorry

end Voter
