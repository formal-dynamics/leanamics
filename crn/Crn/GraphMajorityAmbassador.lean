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
  sorry

/-- **Invariant** [MNRS14, proof of Theorem 2]: no encounter creates an ambassador. -/
theorem ambCount_interact_le (b : Bool) (c : Fin n → AmbState) (e : AgentPair n) :
    ambCount b (ambassador.interact c e) ≤ ambCount b c := by
  sorry

/-- **Invariant** [MNRS14, proof of Theorem 2: "whenever ambassadors disappear, they disappear
in pairs, i.e. one from each color"]: the difference between the numbers of red and green
ambassadors never changes. -/
theorem ambCount_sub_interact (c : Fin n → AmbState) (e : AgentPair n) :
    (ambCount true (ambassador.interact c e) : ℤ) - ambCount false (ambassador.interact c e) =
      (ambCount true c : ℤ) - ambCount false c := by
  sorry

/-- **Annihilation is reachable** [MNRS14, proof of Theorem 2: every configuration of `𝒞_{k,ℓ}`
with `k, ℓ ≥ 1` can lead to `𝒞_{k−1,ℓ−1}`]: on a connected graph, while both colors have an
ambassador, a configuration with one ambassador fewer of each color is reachable. -/
theorem exists_reaches_annihilate {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {c : Fin n → AmbState} (hr : 0 < ambCount true c) (hg : 0 < ambCount false c) :
    ∃ c', ambassador.GraphReaches G c c' ∧ ambCount true c' + 1 = ambCount true c ∧
      ambCount false c' + 1 = ambCount false c := by
  sorry

/-- **Spreading is reachable** [MNRS14, proof of Theorem 2: from `𝒞_{k−ℓ,0}` "there exists a
chain of transitions that lead to a configuration where all vertices are colored with the color
of the initial majority"]: on a connected graph, if there is an ambassador of color `b` and none
of the other color, the configuration in which every vertex has color `b` is reachable. -/
theorem exists_reaches_allColor {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {c : Fin n → AmbState} {b : Bool} (hb : 0 < ambCount b c) (hnb : ambCount (!b) c = 0) :
    ∃ c', ambassador.GraphReaches G c c' ∧ ∀ v, (c' v).1 = b := by
  sorry

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

/-- **[MNRS14, Theorem 2].** Given any connected graph, if there exists initially a majority,
the 4-state ambassador protocol stably computes the initial majority value. -/
theorem ambassador_graphStablyComputes : ambassador.GraphStablyComputes HasMajority majority := by
  sorry

/-- [MNRS14, Theorem 2] on the complete graph of every nonempty population (the standard
population of `Protocol.StablyComputes`). -/
theorem ambassador_stablyComputesOnGraph_top (n : ℕ) (hn : 0 < n) :
    ambassador.StablyComputesOnGraph (⊤ : SimpleGraph (Fin n)) HasMajority majority :=
  ambassador_graphStablyComputes.top n hn

/-- **The tie case is excluded** (as in [MNRS14, Theorem 2]): on the complete graph of two
agents with one red and one green input, the protocol reaches a configuration (both
ambassadors annihilated, both colors present) from which no output-stable configuration is
reachable. -/
theorem ambassador_tie_stuck :
    ∃ ι : Fin 2 → Bool, (counts ι).1 true = (counts ι).1 false ∧
      ∃ c, ambassador.GraphReaches (⊤ : SimpleGraph (Fin 2)) (ambassador.input ∘ ι) c ∧
        ∀ d, ambassador.GraphReaches (⊤ : SimpleGraph (Fin 2)) c d →
          ∀ b, ¬ ambassador.GraphOutputStable (⊤ : SimpleGraph (Fin 2)) b d := by
  sorry

end Crn
