import Crn.GraphMajorityBasic

/-!
# The 4-state ambassador protocol computes majority on every connected graph (CRN-4)

The ambassador protocol of [MNRS14, §4] has the states `(color, ambassador) : Bool × Bool`
(`true` is red `r`, `false` is green `g`; the second component says whether the vertex holds an
ambassador). An input `x` starts in `(x, true)` and the output is the color. On an encounter:

* two ambassadors of different colors annihilate (both vertices keep their colors);
* an ambassador meeting a vertex without ambassador moves there and paints it with its color;
* nothing else changes.

The protocol is symmetric (`ambassador_symm`): it does not distinguish initiator and responder.
Its transition table is Figure 1 of [MNRS14] (`ambassador_table`).

**Theorem 2 of [MNRS14]** (`ambassador_graphStablyComputes`): on every connected graph, if
there is initially a majority, the ambassador protocol stably computes it. The proof pins:

* the invariants: the number of ambassadors of each color never increases
  (`ambCount_interact_le`) and their difference never changes (`ambCount_sub_interact`); it
  starts at the input counts (`ambCount_input`);
* annihilation is always reachable while both colors have ambassadors
  (`exists_reaches_annihilate`, the step `𝒞_{k,ℓ} → 𝒞_{k−1,ℓ−1}` of the proof);
* once all ambassadors have color `b` and there is one, the all-`b` coloring is reachable
  (`exists_reaches_allColor`);
* a configuration in which every vertex has color `b` is output-stable with output `b`
  (`graphOutputStable_of_allColor`).

The tie case is excluded exactly as in the paper (domain `HasMajority`); without it the
protocol can get stuck in a configuration with both colors and no ambassadors
(`ambassador_tie_stuck`).

## References

* [MNRS14] G. B. Mertzios, S. E. Nikoletseas, C. L. Raptopoulos, P. G. Spirakis, *Determining
  majority in networks with local interactions and very small local memory*, ICALP 2014;
  arXiv:1404.7671.
-/

namespace Crn

open Finset

/-- The states of the ambassador protocol [MNRS14, §4]: a color (`true` red, `false` green) and
whether the vertex holds an ambassador. -/
abbrev AmbState := Bool × Bool

/-- The transition function of the ambassador protocol [MNRS14, §4, Figure 1], on the states of
(initiator, responder). -/
def ambassadorδ : AmbState × AmbState → AmbState × AmbState
  | ((c₁, true), (c₂, true)) =>
    if c₁ = c₂ then ((c₁, true), (c₂, true)) else ((c₁, false), (c₂, false))
  | ((c₁, true), (_, false)) => ((c₁, false), (c₁, true))
  | ((_, false), (c₂, true)) => ((c₂, true), (c₂, false))
  | ((c₁, false), (c₂, false)) => ((c₁, false), (c₂, false))

/-- The 4-state ambassador protocol [MNRS14, §4]: input `x ↦ (x, true)` (every vertex starts
with an ambassador of its own color), output the color. -/
def ambassador : Protocol Bool AmbState where
  input x := (x, true)
  output s := s.1
  δ := ambassadorδ

/-- The ambassador protocol has 4 states. -/
theorem card_ambState : Fintype.card AmbState = 4 := rfl

/-- The ten nontrivial entries of the transition table [MNRS14, Figure 1], with `r = true`,
`g = false`; all other entries leave both states unchanged (`ambassador_table_rest`). -/
theorem ambassador_table :
    ambassadorδ ((false, false), (false, true)) = ((false, true), (false, false)) ∧
    ambassadorδ ((false, false), (true, true)) = ((true, true), (true, false)) ∧
    ambassadorδ ((false, true), (false, false)) = ((false, false), (false, true)) ∧
    ambassadorδ ((false, true), (true, false)) = ((false, false), (false, true)) ∧
    ambassadorδ ((false, true), (true, true)) = ((false, false), (true, false)) ∧
    ambassadorδ ((true, false), (false, true)) = ((false, true), (false, false)) ∧
    ambassadorδ ((true, false), (true, true)) = ((true, true), (true, false)) ∧
    ambassadorδ ((true, true), (false, false)) = ((true, false), (true, true)) ∧
    ambassadorδ ((true, true), (false, true)) = ((true, false), (false, false)) ∧
    ambassadorδ ((true, true), (true, false)) = ((true, false), (true, true)) := by
  decide

/-- The entries "−" of [MNRS14, Figure 1]: the remaining six pairs are unchanged. -/
theorem ambassador_table_rest :
    ∀ p : AmbState × AmbState, (p.1.2 = false ∧ p.2.2 = false) ∨ p.1 = p.2 →
      ambassadorδ p = p := by
  decide

/-- The ambassador protocol is symmetric [MNRS14, §2 and §4]. -/
theorem ambassador_symm (p q : AmbState) :
    ambassadorδ (q, p) = ((ambassadorδ (p, q)).2, (ambassadorδ (p, q)).1) := by
  revert p q
  decide

variable {n : ℕ}

/-- The number of ambassadors of color `b` in the configuration `c` (the indices `k, ℓ` of the
classes `𝒞_{k,ℓ}` in the proof of [MNRS14, Theorem 2]). -/
def ambCount (b : Bool) (c : Fin n → AmbState) : ℕ :=
  (univ.filter fun v => c v = (b, true)).card

/-- Initially every vertex holds an ambassador of its input color. -/
theorem ambCount_input (b : Bool) (ι : Fin n → Bool) :
    ambCount b (ambassador.input ∘ ι) = (counts ι).1 b := by
  simp [ambCount, counts_val, ambassador]

/-- The indicator of an ambassador of color `b` in the state `s`. -/
def ambInd (b : Bool) (s : AmbState) : ℕ :=
  if s = (b, true) then 1 else 0

/-- The number of ambassadors of color `b` is the sum of their indicators over the vertices. -/
theorem ambCount_eq_sum (b : Bool) (c : Fin n → AmbState) :
    ambCount b c = ∑ v, ambInd b (c v) := by
  rw [ambCount, card_filter]
  rfl

/-- Summing the indicators over an encounter `e`: only the two agents of `e` change. -/
theorem ambCount_interact_add (b : Bool) (c : Fin n → AmbState) (e : AgentPair n) :
    ambCount b (ambassador.interact c e) + (ambInd b (c e.1.1) + ambInd b (c e.1.2)) =
      ambCount b c + (ambInd b (ambassadorδ (c e.1.1, c e.1.2)).1 +
        ambInd b (ambassadorδ (c e.1.1, c e.1.2)).2) := by
  rw [ambCount_eq_sum, ambCount_eq_sum,
    sum_add_pair e.2 (fun w => ambInd b (c w)) (fun w => ambInd b (ambassador.interact c e w))
      fun w h1 h2 => by rw [Protocol.interact_of_ne _ _ _ h1 h2]]
  simp only [Protocol.interact_fst, Protocol.interact_snd]
  rfl

/-- No transition creates an ambassador of color `b`. -/
theorem ambInd_δ_le (b : Bool) (p q : AmbState) :
    ambInd b (ambassadorδ (p, q)).1 + ambInd b (ambassadorδ (p, q)).2 ≤
      ambInd b p + ambInd b q := by
  revert b p q
  decide

/-- Every transition removes as many red as green ambassadors. -/
theorem ambInd_δ_sub (p q : AmbState) :
    ambInd true (ambassadorδ (p, q)).1 + ambInd true (ambassadorδ (p, q)).2 + ambInd false p +
        ambInd false q =
      ambInd true p + ambInd true q + ambInd false (ambassadorδ (p, q)).1 +
        ambInd false (ambassadorδ (p, q)).2 := by
  revert p q
  decide

/-- **Invariant** [MNRS14, proof of Theorem 2]: no encounter creates an ambassador. -/
theorem ambCount_interact_le (b : Bool) (c : Fin n → AmbState) (e : AgentPair n) :
    ambCount b (ambassador.interact c e) ≤ ambCount b c := by
  have h := ambCount_interact_add b c e
  have := ambInd_δ_le b (c e.1.1) (c e.1.2)
  omega

/-- **Invariant** [MNRS14, proof of Theorem 2: "whenever ambassadors disappear, they disappear
in pairs, i.e. one from each color"]: the difference between the numbers of red and green
ambassadors never changes. -/
theorem ambCount_sub_interact (c : Fin n → AmbState) (e : AgentPair n) :
    (ambCount true (ambassador.interact c e) : ℤ) - ambCount false (ambassador.interact c e) =
      (ambCount true c : ℤ) - ambCount false c := by
  have ht := ambCount_interact_add true c e
  have hf := ambCount_interact_add false c e
  have := ambInd_δ_sub (c e.1.1) (c e.1.2)
  omega

/-- Counting the agents whose state satisfies `p` when only the agents `u ≠ x` change. -/
lemma card_filter_add_pair (p : AmbState → Prop) [DecidablePred p] {c c' : Fin n → AmbState}
    {u x : Fin n} (hux : u ≠ x) (h : ∀ w, w ≠ u → w ≠ x → c' w = c w) :
    (univ.filter fun v => p (c' v)).card +
        ((if p (c u) then 1 else 0) + if p (c x) then 1 else 0) =
      (univ.filter fun v => p (c v)).card +
        ((if p (c' u) then 1 else 0) + if p (c' x) then 1 else 0) := by
  simp only [card_filter]
  exact sum_add_pair hux (fun v => if p (c v) then 1 else 0) (fun v => if p (c' v) then 1 else 0)
    fun w h1 h2 => by simp only [h w h1 h2]

/-- There are no ambassadors of color `b` iff no vertex is in the state `(b, true)`. -/
lemma ambCount_eq_zero_iff {b : Bool} {c : Fin n → AmbState} :
    ambCount b c = 0 ↔ ∀ v, c v ≠ (b, true) := by
  simp [ambCount, filter_eq_empty_iff]

/-- **Move** [MNRS14, §4]: an ambassador of color `b` meeting a vertex without ambassador moves
there and paints it with its color `b`. -/
lemma interact_move {c : Fin n → AmbState} {e : AgentPair n} {b : Bool}
    (hu : c e.1.1 = (b, true)) (hx : (c e.1.2).2 = false) :
    ambassador.interact c e e.1.1 = (b, false) ∧ ambassador.interact c e e.1.2 = (b, true) := by
  obtain ⟨y, hy⟩ : ∃ y, c e.1.2 = (y, false) := ⟨_, Prod.ext rfl hx⟩
  rw [Protocol.interact_fst, Protocol.interact_snd, hu, hy]
  cases b <;> cases y <;> exact ⟨rfl, rfl⟩

/-- A move changes no ambassador count. -/
lemma ambCount_interact_move {c : Fin n → AmbState} {e : AgentPair n} {b : Bool}
    (hu : c e.1.1 = (b, true)) (hx : (c e.1.2).2 = false) (b' : Bool) :
    ambCount b' (ambassador.interact c e) = ambCount b' c := by
  obtain ⟨h1, h2⟩ := interact_move hu hx
  obtain ⟨y, hy⟩ : ∃ y, c e.1.2 = (y, false) := ⟨_, Prod.ext rfl hx⟩
  have k := card_filter_add_pair (· = (b', true)) (c := c) (c' := ambassador.interact c e) e.2
    fun w h1 h2 => Protocol.interact_of_ne _ _ _ h1 h2
  rw [h1, h2, hu, hy] at k
  simp at k
  exact k

/-- **Annihilation** [MNRS14, §4]: two ambassadors of different colors meet; both disappear. -/
lemma ambCount_interact_annihilate {c : Fin n → AmbState} {e : AgentPair n}
    (hu : c e.1.1 = (true, true)) (hx : c e.1.2 = (false, true)) :
    ambCount true (ambassador.interact c e) + 1 = ambCount true c ∧
      ambCount false (ambassador.interact c e) + 1 = ambCount false c := by
  have h1 : ambassador.interact c e e.1.1 = (true, false) := by
    rw [Protocol.interact_fst, hu, hx]; rfl
  have h2 : ambassador.interact c e e.1.2 = (false, false) := by
    rw [Protocol.interact_snd, hu, hx]; rfl
  have k := fun b => card_filter_add_pair (· = (b, true)) (c := c)
    (c' := ambassador.interact c e) e.2 fun w h1 h2 => Protocol.interact_of_ne _ _ _ h1 h2
  have kt := k true
  have kf := k false
  rw [h1, h2, hu, hx] at kt kf
  simp at kt kf
  exact ⟨kt, kf⟩

/-- On a connected graph, every vertex `u ≠ w` has a neighbour closer to `w`. -/
lemma exists_adj_dist_lt {G : SimpleGraph (Fin n)} (hG : G.Connected) {u w : Fin n}
    (h : u ≠ w) : ∃ x, G.Adj u x ∧ G.dist x w < G.dist u w := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u w
  cases p with
  | nil => exact absurd rfl h
  | cons hadj q =>
    refine ⟨_, hadj, ?_⟩
    rw [← hp, SimpleGraph.Walk.length_cons]
    exact Nat.lt_succ_of_le (SimpleGraph.dist_le q)

/-- Annihilation is reachable, by induction on the distance `k` from a red ambassador at `u` to a
green ambassador at `w`: the red ambassador walks towards `w` along a shortest path (moving to
free vertices, or handing over to a red ambassador it meets) until it meets a green one. -/
lemma exists_reaches_annihilate_of_dist {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {w : Fin n} (k : ℕ) :
    ∀ (c : Fin n → AmbState) (u : Fin n), G.dist u w = k → c u = (true, true) →
      c w = (false, true) →
      ∃ c', ambassador.GraphReaches G c c' ∧ ambCount true c' + 1 = ambCount true c ∧
        ambCount false c' + 1 = ambCount false c := by
  refine Nat.strong_induction_on k ?_
  intro k ih c u hk hu hw
  have huw : u ≠ w := by
    rintro rfl
    rw [hu] at hw
    cases hw
  obtain ⟨x, hux, hx⟩ := exists_adj_dist_lt hG huw
  let e := dartPair (⟨(u, x), hux⟩ : G.Dart)
  have hstep : ambassador.GraphStep G c (ambassador.interact c e) := ⟨_, rfl⟩
  have hu' : c e.1.1 = (true, true) := hu
  by_cases hx2 : (c x).2 = false
  · have hx' : (c e.1.2).2 = false := hx2
    have hxw : x ≠ w := by
      rintro rfl
      rw [hw] at hx2
      cases hx2
    obtain ⟨c', hr, ht, hf⟩ := ih _ (hk ▸ hx) (ambassador.interact c e) x rfl
      (interact_move hu' hx').2 (by rw [Protocol.interact_of_ne _ _ _ huw.symm hxw.symm, hw])
    refine ⟨c', .head hstep hr, ?_, ?_⟩
    · rw [ht, ambCount_interact_move hu' hx']
    · rw [hf, ambCount_interact_move hu' hx']
  · by_cases hx1 : (c x).1 = true
    · exact ih _ (hk ▸ hx) c x rfl (Prod.ext hx1 (by simpa using hx2)) hw
    · have hx' : c e.1.2 = (false, true) :=
        show c x = (false, true) from Prod.ext (by simpa using hx1) (by simpa using hx2)
      exact ⟨_, .single hstep, ambCount_interact_annihilate hu' hx'⟩

/-- Spreading the color `b` by one vertex, by induction on the distance `k` from an ambassador
of color `b` at `u` to a vertex `w` of color `!b`, in the absence of ambassadors of color `!b`:
the ambassador walks towards `w` along a shortest path (handing over to the ambassadors of color
`b` it meets) until it paints a vertex of color `!b`. -/
lemma exists_reaches_spread_of_dist {G : SimpleGraph (Fin n)} (hG : G.Connected) {b : Bool}
    {w : Fin n} (k : ℕ) :
    ∀ (c : Fin n → AmbState) (u : Fin n), G.dist u w = k → c u = (b, true) →
      ambCount (!b) c = 0 → (c w).1 = !b →
      ∃ c', ambassador.GraphReaches G c c' ∧ ambCount (!b) c' = 0 ∧ 0 < ambCount b c' ∧
        (univ.filter fun v => (c' v).1 = !b).card < (univ.filter fun v => (c v).1 = !b).card := by
  refine Nat.strong_induction_on k ?_
  intro k ih c u hk hu hnb hw
  have huw : u ≠ w := by
    rintro rfl
    rw [hu] at hw
    exact Bool.eq_not_self b |>.mp hw
  obtain ⟨x, hux, hx⟩ := exists_adj_dist_lt hG huw
  let e := dartPair (⟨(u, x), hux⟩ : G.Dart)
  have hstep : ambassador.GraphStep G c (ambassador.interact c e) := ⟨_, rfl⟩
  have hu' : c e.1.1 = (b, true) := hu
  by_cases hx2 : (c x).2 = false
  · have hx' : (c e.1.2).2 = false := hx2
    have hcount := ambCount_interact_move hu' hx'
    have hpos : 0 < ambCount b (ambassador.interact c e) := by
      rw [hcount, ambCount]
      exact card_pos.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, hu⟩⟩
    have k := card_filter_add_pair (fun s : AmbState => s.1 = !b) (c := c)
      (c' := ambassador.interact c e) e.2 fun w h1 h2 => Protocol.interact_of_ne _ _ _ h1 h2
    rw [(interact_move hu' hx').1, (interact_move hu' hx').2, hu'] at k
    simp only [Bool.eq_not_self, if_false] at k
    by_cases hx1 : (c x).1 = b
    · have hxw : x ≠ w := by
        rintro rfl
        rw [hx1] at hw
        exact Bool.eq_not_self b |>.mp hw
      obtain ⟨c', hr, h0, hpos', hlt⟩ := ih _ (hk ▸ hx) (ambassador.interact c e) x rfl
        (interact_move hu' hx').2 (by rw [hcount]; exact hnb)
        (by rw [Protocol.interact_of_ne _ _ _ huw.symm hxw.symm, hw])
      refine ⟨c', .head hstep hr, h0, hpos', ?_⟩
      have hx1' : ¬ (c e.1.2).1 = !b := by
        change ¬ (c x).1 = !b
        rw [hx1]
        exact (Bool.eq_not_self b).not.mpr id
      rw [if_neg hx1'] at k
      omega
    · have hx1' : (c e.1.2).1 = !b := Bool.eq_not.mpr hx1
      rw [if_pos hx1'] at k
      refine ⟨_, .single hstep, by rw [hcount]; exact hnb, hpos, ?_⟩
      omega
  · have hcx : c x = (b, true) := by
      refine Prod.ext ?_ (by simpa using hx2)
      by_contra hx1
      exact ambCount_eq_zero_iff.mp hnb x (Prod.ext (Bool.eq_not.mpr hx1) (by simpa using hx2))
    exact ih _ (hk ▸ hx) c x rfl hcx hnb hw

/-- **Annihilation is reachable** [MNRS14, proof of Theorem 2: every configuration of `𝒞_{k,ℓ}`
with `k, ℓ ≥ 1` can lead to `𝒞_{k−1,ℓ−1}`]: on a connected graph, while both colors have an
ambassador, a configuration with one ambassador fewer of each color is reachable. -/
theorem exists_reaches_annihilate {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {c : Fin n → AmbState} (hr : 0 < ambCount true c) (hg : 0 < ambCount false c) :
    ∃ c', ambassador.GraphReaches G c c' ∧ ambCount true c' + 1 = ambCount true c ∧
      ambCount false c' + 1 = ambCount false c := by
  obtain ⟨u, hu⟩ := card_pos.mp hr
  obtain ⟨w, hw⟩ := card_pos.mp hg
  exact exists_reaches_annihilate_of_dist hG _ c u rfl (mem_filter.mp hu).2 (mem_filter.mp hw).2

/-- **Spreading is reachable** [MNRS14, proof of Theorem 2: from `𝒞_{k−ℓ,0}` "there exists a
chain of transitions that lead to a configuration where all vertices are colored with the color
of the initial majority"]: on a connected graph, if there is an ambassador of color `b` and none
of the other color, the configuration in which every vertex has color `b` is reachable. -/
theorem exists_reaches_allColor {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {c : Fin n → AmbState} {b : Bool} (hb : 0 < ambCount b c) (hnb : ambCount (!b) c = 0) :
    ∃ c', ambassador.GraphReaches G c c' ∧ ∀ v, (c' v).1 = b := by
  -- strong induction on the number of vertices of color `!b`
  suffices H : ∀ (m : ℕ) (c : Fin n → AmbState),
      (univ.filter fun v => (c v).1 = !b).card = m → 0 < ambCount b c → ambCount (!b) c = 0 →
        ∃ c', ambassador.GraphReaches G c c' ∧ ∀ v, (c' v).1 = b from H _ c rfl hb hnb
  intro m
  refine Nat.strong_induction_on m ?_
  intro m ih c hm hb hnb
  by_cases hall : ∀ v, (c v).1 = b
  · exact ⟨c, .refl, hall⟩
  · obtain ⟨w, hw⟩ := not_forall.mp hall
    obtain ⟨u, hu⟩ := card_pos.mp hb
    obtain ⟨c₁, h₁, h₁0, h₁pos, hlt⟩ := exists_reaches_spread_of_dist hG _ c u rfl
      (mem_filter.mp hu).2 hnb (Bool.eq_not.mpr hw)
    obtain ⟨c', h₂, hc'⟩ := ih _ (hm ▸ hlt) c₁ rfl h₁pos h₁0
    exact ⟨c', h₁.trans h₂, hc'⟩

/-- An encounter of two vertices of color `b` keeps both of color `b`. -/
theorem ambassadorδ_color (b : Bool) (p q : AmbState) (hp : p.1 = b) (hq : q.1 = b) :
    (ambassadorδ (p, q)).1.1 = b ∧ (ambassadorδ (p, q)).2.1 = b := by
  revert b p q
  decide

/-- A configuration in which every vertex has color `b` is output-stable with output `b`, on
every interaction graph: encounters of two vertices of color `b` keep color `b`. -/
theorem graphOutputStable_of_allColor (G : SimpleGraph (Fin n)) {c : Fin n → AmbState}
    {b : Bool} (h : ∀ v, (c v).1 = b) : ambassador.GraphOutputStable G b c := by
  intro c' hr
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
    obtain ⟨d, rfl⟩ := hs
    intro v
    have hδ := ambassadorδ_color b _ _ (ih (dartPair d).1.1) (ih (dartPair d).1.2)
    rw [Protocol.interact_apply]
    split_ifs
    · exact hδ.2
    · exact hδ.1
    · exact ih v

/-- The difference between the numbers of red and green ambassadors is invariant along
reachability on any interaction graph (`ambCount_sub_interact`). -/
theorem ambCount_sub_reaches {G : SimpleGraph (Fin n)} {c c' : Fin n → AmbState}
    (h : ambassador.GraphReaches G c c') :
    (ambCount true c' : ℤ) - ambCount false c' = (ambCount true c : ℤ) - ambCount false c := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨d, rfl⟩ := hs
    rw [ambCount_sub_interact, ih]

/-- Iterated annihilation [MNRS14, proof of Theorem 2: `𝒞_{k,ℓ} → ⋯ → 𝒞_{k−ℓ,0}`]: on a
connected graph, a configuration in which some color has no ambassador is reachable. -/
theorem exists_reaches_ambCount_eq_zero {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (c : Fin n → AmbState) :
    ∃ c', ambassador.GraphReaches G c c' ∧ (ambCount true c' = 0 ∨ ambCount false c' = 0) := by
  induction h : ambCount false c generalizing c with
  | zero => exact ⟨c, Relation.ReflTransGen.refl, Or.inr h⟩
  | succ k ih =>
    rcases Nat.eq_zero_or_pos (ambCount true c) with h0 | h0
    · exact ⟨c, Relation.ReflTransGen.refl, Or.inl h0⟩
    · obtain ⟨c₁, h₁, -, hf⟩ := exists_reaches_annihilate hG h0 (by omega)
      obtain ⟨c₂, h₂, h₂'⟩ := ih c₁ (by omega)
      exact ⟨c₂, h₁.trans h₂, h₂'⟩

/-- **[MNRS14, Theorem 2].** Given any connected graph, if there exists initially a majority,
the 4-state ambassador protocol stably computes the initial majority value. -/
theorem ambassador_graphStablyComputes : ambassador.GraphStablyComputes HasMajority majority := by
  intro n G hG ι hι c hc
  obtain ⟨c', hcc', h0⟩ := exists_reaches_ambCount_eq_zero hG c
  have hd := ambCount_sub_reaches (hc.trans hcc')
  rw [ambCount_input, ambCount_input] at hd
  have key : ∃ b, b = majority (counts ι).1 ∧ 0 < ambCount b c' ∧ ambCount (!b) c' = 0 := by
    unfold HasMajority at hι
    rcases h0 with h0 | h0
    · exact ⟨false, by simp [majority]; omega, by omega, h0⟩
    · exact ⟨true, by simp [majority]; omega, by omega, h0⟩
  obtain ⟨b, rfl, hb, hnb⟩ := key
  obtain ⟨d, hd', hall⟩ := exists_reaches_allColor hG hb hnb
  exact ⟨d, hcc'.trans hd', graphOutputStable_of_allColor G hall⟩

/-- [MNRS14, Theorem 2] on the complete graph of every nonempty population (the standard
population of `Protocol.StablyComputes`). -/
theorem ambassador_stablyComputesOnGraph_top (n : ℕ) (hn : 0 < n) :
    ambassador.StablyComputesOnGraph (⊤ : SimpleGraph (Fin n)) HasMajority majority :=
  ambassador_graphStablyComputes.top n hn

/-- A configuration without ambassadors is a fixed point on every interaction graph: every
encounter of two vertices without ambassador leaves both unchanged (`ambassador_table_rest`). -/
theorem graphReaches_eq_of_noAmb {G : SimpleGraph (Fin n)} {c d : Fin n → AmbState}
    (hc : ∀ v, (c v).2 = false) (h : ambassador.GraphReaches G c d) : d = c := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨e, rfl⟩ := hs
    subst ih
    exact Protocol.interact_eq_self _ _ _ (ambassador_table_rest _ (Or.inl ⟨hc _, hc _⟩))

/-- **The tie case is excluded** (as in [MNRS14, Theorem 2]): on the complete graph of two
agents with one red and one green input, the protocol reaches a configuration (both
ambassadors annihilated, both colors present) from which no output-stable configuration is
reachable. -/
theorem ambassador_tie_stuck :
    ∃ ι : Fin 2 → Bool, (counts ι).1 true = (counts ι).1 false ∧
      ∃ c, ambassador.GraphReaches (⊤ : SimpleGraph (Fin 2)) (ambassador.input ∘ ι) c ∧
        ∀ d, ambassador.GraphReaches (⊤ : SimpleGraph (Fin 2)) c d →
          ∀ b, ¬ ambassador.GraphOutputStable (⊤ : SimpleGraph (Fin 2)) b d := by
  refine ⟨![true, false], by decide, ![(true, false), (false, false)], ?_, ?_⟩
  · refine Relation.ReflTransGen.single ⟨⟨((0 : Fin 2), (1 : Fin 2)), by simp⟩, ?_⟩
    decide
  · intro d hd b hb
    rw [graphReaches_eq_of_noAmb (by decide) hd] at hb
    have h0 := hb _ Relation.ReflTransGen.refl 0
    have h1 := hb _ Relation.ReflTransGen.refl 1
    exact absurd (h0.trans h1.symm) (by decide)

end Crn
