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

lemma bool_not_ne_iff {a b : Bool} : (Bool.not a ≠ Bool.not b) ↔ (a ≠ b) := by
  cases a <;> cases b <;> decide

lemma bool_ne_not_iff {a b : Bool} : (a ≠ Bool.not b) ↔ (Bool.not a ≠ b) := by
  cases a <;> cases b <;> decide

/-- Swapping the two layers is an automorphism of the double cover. -/
def doubleCoverFlip (G : SimpleGraph V) : doubleCover G →g doubleCover G where
  toFun p := (p.1, !p.2)
  map_rel' := by
    intro p q h
    exact ⟨h.1, bool_not_ne_iff.mpr h.2⟩

@[simp] lemma doubleCoverFlip_apply (p : V × Bool) :
    doubleCoverFlip G p = (p.1, !p.2) := rfl

/-- A walk of `G` lifts to the double cover, flipping the layer at every step. -/
lemma doubleCover_reachable_of_walk {u v : V} (p : G.Walk u v) (i : Bool) :
    ∃ j : Bool, (doubleCover G).Reachable (u, i) (v, j) := by
  induction p generalizing i with
  | nil => exact ⟨i, SimpleGraph.Reachable.refl _⟩
  | @cons u v w huv tail ih =>
    obtain ⟨j, hj⟩ := ih (!i)
    have he : (doubleCover G).Adj (u, i) (v, !i) := ⟨huv, by cases i <;> simp⟩
    exact ⟨j, (SimpleGraph.Adj.reachable he).trans hj⟩

/-- Reachability is preserved by swapping both layers. -/
lemma doubleCover_reachable_flip {a b : V} {i j : Bool}
    (h : (doubleCover G).Reachable (a, i) (b, j)) :
    (doubleCover G).Reachable (a, !i) (b, !j) := by
  simpa using SimpleGraph.Reachable.map (doubleCoverFlip G) h

/-- **Connectivity of the double cover.** If `G` is connected and nonbipartite (not
2-colourable), then its bipartite double cover is connected. This is where the
nonbipartiteness hypothesis of Hassin–Peleg (§2.1, Lemma 2.4) enters. -/
lemma doubleCover_connected (hc : G.Connected) (hnb : ¬ G.Colorable 2) :
    (doubleCover G).Connected := by
  obtain ⟨x₀⟩ := hc.nonempty
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨(x₀, false), ?_⟩
  intro q
  obtain ⟨v, j⟩ := q
  by_contra hmiss
  -- the missed vertex forces the two layers of `x₀` to lie in different components
  have hnotx : ¬ (doubleCover G).Reachable (x₀, false) (x₀, true) := by
    intro hx
    obtain ⟨p⟩ := hc x₀ v
    obtain ⟨k, hk⟩ := doubleCover_reachable_of_walk p false
    have hkne : k ≠ j := by
      intro hkj
      exact hmiss (hkj ▸ hk)
    have hk' : k = !j := by
      cases k <;> cases j
      · exact (hkne rfl).elim
      · rfl
      · rfl
      · exact (hkne rfl).elim
    have hother : (doubleCover G).Reachable (x₀, false) (v, !j) := hk' ▸ hk
    have hback : (doubleCover G).Reachable (x₀, true) (v, j) := by
      simpa [Bool.not_false, Bool.not_not] using doubleCover_reachable_flip hother
    exact hmiss (hx.trans hback)
  -- exactly one layer of every vertex is reachable from `(x₀, false)`
  have hexact (w : V) :
      ((doubleCover G).Reachable (x₀, false) (w, false) ∨
        (doubleCover G).Reachable (x₀, false) (w, true)) ∧
      ¬ ((doubleCover G).Reachable (x₀, false) (w, false) ∧
        (doubleCover G).Reachable (x₀, false) (w, true)) := by
    obtain ⟨p⟩ := hc x₀ w
    obtain ⟨k, hk⟩ := doubleCover_reachable_of_walk p false
    refine ⟨?_, ?_⟩
    · cases k
      · exact Or.inl hk
      · exact Or.inr hk
    · intro ⟨hf, ht⟩
      have hflip : (doubleCover G).Reachable (x₀, true) (w, false) := by
        simpa [Bool.not_false, Bool.not_true] using doubleCover_reachable_flip ht
      exact hnotx (hflip.trans hf.symm).symm
  -- the reachable layer is a proper 2-colouring
  classical
  let c : V → Bool := fun w => decide ((doubleCover G).Reachable (x₀, false) (w, false))
  have hc_iff (w : V) : c w = true ↔ (doubleCover G).Reachable (x₀, false) (w, false) := by
    simp [c]
  have hvalid {v w : V} (hvw : G.Adj v w) : c v ≠ c w := by
    intro hcw
    cases hcv : c v
    · have hv : ¬ (doubleCover G).Reachable (x₀, false) (v, false) := by
        intro hv
        exact Bool.false_ne_true (hcv.symm.trans ((hc_iff v).mpr hv))
      have hw : ¬ (doubleCover G).Reachable (x₀, false) (w, false) := by
        intro hw
        exact Bool.false_ne_true ((hcw.symm.trans hcv).symm.trans ((hc_iff w).mpr hw))
      have hvtrue := Or.resolve_left (hexact v).1 hv
      have he : (doubleCover G).Adj (v, true) (w, false) := ⟨hvw, by simp⟩
      exact hw (hvtrue.trans (SimpleGraph.Adj.reachable he))
    · have hv := (hc_iff v).mp hcv
      have hw := (hc_iff w).mp (hcw.symm.trans hcv)
      have he : (doubleCover G).Adj (v, false) (w, true) := ⟨hvw, by simp⟩
      exact (hexact w).2 ⟨hw, hv.trans (SimpleGraph.Adj.reachable he)⟩
  exact hnb (by simpa using (SimpleGraph.Coloring.mk c hvalid).colorable)

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
  set d : V → ℝ := h - hitting G hc y with hd_def
  have hd0 : d y = 0 := by simp [hd_def, hy, hitting_self]
  have hdlap (x : V) (hx : x ≠ y) : (G.lapMatrix ℝ *ᵥ d) x = 0 := by
    rw [mulVec_sub, Pi.sub_apply, hlap x hx, hitting_lapMatrix_of_ne hc hx, sub_self]
  funext x
  have hle : d x ≤ 0 :=
    le_zero_of_lapMatrix_le G hc (by simp [hd0]) (fun z hz => (hdlap z hz).le) x
  have hge : -d x ≤ 0 :=
    le_zero_of_lapMatrix_le G hc (u := -d) (by rw [Pi.neg_apply, hd0]; simp)
      (fun z hz => by rw [mulVec_neg, Pi.neg_apply, hdlap z hz, neg_zero]) x
  have : d x = 0 := le_antisymm hle (neg_nonpos.mp hge)
  rw [hd_def, Pi.sub_apply, sub_eq_zero] at this
  exact this

/-- **Layer symmetry.** Hitting times of the double cover are invariant under swapping the
two layers of both the start and the target. -/
lemma hitting_doubleCover_flip (hc' : (doubleCover G).Connected) (x y : V) (i j : Bool) :
    hitting (doubleCover G) hc' (y, !j) (x, !i) = hitting (doubleCover G) hc' (y, j) (x, i) := by
  let σ : V × Bool → V × Bool := fun p => (p.1, !p.2)
  let hσ : V × Bool → ℝ := fun p => hitting (doubleCover G) hc' (y, j) (σ p)
  have hσσ (p : V × Bool) : σ (σ p) = p := by
    cases p with
    | mk a b => cases b <;> rfl
  have hy : hσ (y, !j) = 0 := by
    simp [hσ, σ, hitting_self]
  have hlap (p : V × Bool) (hp : p ≠ (y, !j)) :
      ((doubleCover G).lapMatrix ℝ *ᵥ hσ) p = 2 * (doubleCover G).degree p := by
    have hpσ : σ p ≠ (y, j) := by
      intro h
      apply hp
      have := congrArg σ h
      simpa [σ, hσσ] using this
    have hdeg : (doubleCover G).degree p = (doubleCover G).degree (σ p) := by
      obtain ⟨a, k⟩ := p
      rw [doubleCover_degree, doubleCover_degree]
    have hsum : ∑ q ∈ (doubleCover G).neighborFinset p, hσ q =
        ∑ q ∈ (doubleCover G).neighborFinset (σ p), hitting (doubleCover G) hc' (y, j) q := by
      refine Finset.sum_nbij' σ σ ?_ ?_ ?_ ?_ ?_
      · intro q hq
        simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj, σ] at hq ⊢
        exact ⟨hq.1, bool_not_ne_iff.mpr hq.2⟩
      · intro q hq
        simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj, σ] at hq ⊢
        exact ⟨hq.1, bool_ne_not_iff.mpr hq.2⟩
      · intro q _
        exact hσσ q
      · intro q _
        exact hσσ q
      · intro q _
        rfl
    rw [SimpleGraph.lapMatrix_mulVec_apply, hsum, hdeg]
    rw [← SimpleGraph.lapMatrix_mulVec_apply]
    exact hitting_lapMatrix_of_ne hc' hpσ
  have huniq := hitting_unique hc' hy hlap
  have := congr_fun huniq (x, !i)
  simpa [hσ, σ] using this.symm

omit [DecidableEq V] in
/-- Expectation under uniform neighbour sampling is the average over the neighbours. -/
lemma uniformNeighbor_expect (hd : ∀ i, 0 < G.degree i) (x : V) (f : V → ℝ) :
    (uniformNeighbor G hd x).expect f =
      (∑ w ∈ G.neighborFinset x, f w) / G.degree x := by
  simp only [Distribution.expect, uniformNeighbor]
  have h (j : V) :
      (if G.Adj x j then (G.degree x : ℝ)⁻¹ else 0) * f j =
        if G.Adj x j then f j / G.degree x else 0 := by
    by_cases hj : G.Adj x j
    · simp [hj, div_eq_mul_inv, mul_comm]
    · simp [hj]
  simp_rw [h]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj x) = G.neighborFinset x := by
    ext j
    simp
  rw [he, ← Finset.sum_div]

/-- A plain uniform-neighbour step away from the target lowers the (lazy-normalised) hitting
time by `2` in expectation: `hitting` is twice the hitting time of the plain walk. -/
lemma uniformNeighbor_expect_hitting (hd : ∀ i, 0 < G.degree i) (hc : G.Connected) {x y : V}
    (hxy : x ≠ y) :
    (uniformNeighbor G hd x).expect (hitting G hc y) = hitting G hc y x - 2 := by
  have hlap := hitting_lapMatrix_of_ne hc hxy
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hlap
  have hS : ∑ w ∈ G.neighborFinset x, hitting G hc y w =
      G.degree x * hitting G hc y x - 2 * G.degree x := by linarith
  have hdx : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast (hd x).ne'
  rw [uniformNeighbor_expect hd, hS]
  field_simp

omit [DecidableEq V] in
/-- A uniform-neighbour step of the double cover from `(x, i)` is a uniform-neighbour step of
`G` from `x` followed by a flip of the layer. -/
lemma uniformNeighbor_doubleCover_expect (hd : ∀ i, 0 < G.degree i)
    (hd' : ∀ p, 0 < (doubleCover G).degree p) (x : V) (i : Bool) (f : V × Bool → ℝ) :
    (uniformNeighbor (doubleCover G) hd' (x, i)).expect f =
      (uniformNeighbor G hd x).expect fun a => f (a, !i) := by
  rw [uniformNeighbor_expect hd' (x, i), uniformNeighbor_expect hd x, doubleCover_degree]
  refine congrArg (fun s : ℝ => s / (G.degree x : ℝ)) ?_
  refine Finset.sum_nbij' (fun q : V × Bool => q.1) (fun a => (a, !i)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj] at hq ⊢
    exact hq.1
  · intro a ha
    simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj] at ha ⊢
    exact ⟨ha, by cases i <;> simp⟩
  · intro q hq
    simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj] at hq
    ext
    · rfl
    · cases i <;> cases hq2 : q.2 <;> simp_all
  · intro a _
    rfl
  · intro q hq
    simp only [SimpleGraph.mem_neighborFinset, doubleCover_adj] at hq
    obtain ⟨a, b⟩ := q
    have hb : b = !i := by cases i <;> cases b <;> simp_all
    simp [hb]

end Voter
