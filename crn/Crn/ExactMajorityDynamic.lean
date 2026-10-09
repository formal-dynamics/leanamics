import Crn.ExactMajorityStatic

/-!
# Dynamic exact majority with ties (CRN-5, [GHMSS16, Section 3])

The protocol `P₂` of [GHMSS16, Section 3]. Every agent `a` carries a colour `c_a ∈ {-1, 0, 1}`,
which an external force may change, and a state among the strong states `[-2], …, [2]` and the
weak states `⟨-1⟩, ⟨0⟩, ⟨1⟩`, with weight `w([z]) = z`, `w(⟨x⟩) = 0` (Fig. 3). Interactions
(the rules of the text of Section 3): `[1]`, `[-1]` and `[2]`, `[-2]` annihilate into `[0], [0]`;
`[2]`, `[-1]` become `[1], [0]` and `[-2]`, `[1]` become `[-1], [0]`; a strong state of positive
(negative) weight turns weak states and `[0]` into `⟨1⟩` (`⟨-1⟩`); `[0]` turns weak states into
`⟨0⟩`. The interaction table does not read the colours. When the force changes `c_a` to
`c_a + Δ`, the state becomes `[w(s_a) + Δ]` (`DynState.recolour`, Fig. 3).

The colours are therefore kept outside the protocol: a configuration of `P₂` is `c : Fin n →
DynState`, and the colours `col : Fin n → SignType` are linked to it by the two invariants of
Section 3 (`DynInv`). For the relative majority protocol of Section 5, `P₂` runs separately in
groups of agents (agents with the same label prefix); `GStep grp` is a step between two agents of
the same group, and `DynInv grp` holds group by group. With one group, `GStep` is `Step`.

Main statements:
* `DynInv.gstep`, `DynInv.recolour` (Lemma 4): the invariants are preserved by interactions and by
  the external force.
* `DynState.absWeight_sum_gstep_le` (Lemma 5, first part), `DynState.exists_greaches_noOpposite`
  (Lemma 5, second part).
* `DynInv.exists_stable` (the conclusion of Section 3): from every configuration satisfying the
  invariants, interactions alone reach a configuration from which every agent forever outputs the
  sign of the colour sum of its group.
* `dynamicMajority_stabilizes` (Section 3 in protocol form): after any finite sequence of
  interactions and colour changes, the protocol stabilizes on the sign of the final colour sum.
* `dynamicMajority_stablyComputes`: without the force, `P₂` stably computes the sign of
  `#1 - #(-1)`.

The table of Fig. 4 differs from the text in five entries. Four are harmless (`[±2]` meeting
`[∓1]` gives `⟨±1⟩` instead of `[0]`, of the same weight). The entry for `[1]` meeting `[0]`,
`(⟨1⟩, [1])`, needs a minor correction: it moves the weight to the `[0]` agent and breaks
Invariant 2 (an agent of colour `-1` in state `[0]` would get `[1]`, and a later change of its
colour to `1` would require the state `[3]`); the text's `([1], ⟨1⟩)` is used.
-/

namespace Crn

open Finset

/-- The eight states of the dynamic majority protocol [GHMSS16, Fig. 3]: strong `[-2], …, [2]`
and weak `⟨x⟩`, `x ∈ {-1, 0, 1}`. -/
inductive DynState
  /-- `[-2]`. -/
  | neg2
  /-- `[-1]`. -/
  | neg1
  /-- `[0]`. -/
  | zero
  /-- `[1]`. -/
  | pos1
  /-- `[2]`. -/
  | pos2
  /-- The weak state `⟨x⟩`. -/
  | weak (x : SignType)
  deriving DecidableEq, Fintype

namespace DynState

/-- The weight [GHMSS16, Fig. 3]: `w([z]) = z`, `w(⟨x⟩) = 0`. -/
def weight : DynState → ℤ
  | neg2 => -2
  | neg1 => -1
  | zero => 0
  | pos1 => 1
  | pos2 => 2
  | weak _ => 0

/-- Weak states. -/
def isWeak : DynState → Bool
  | weak _ => true
  | _ => false

/-- The output (the reported sign of the colour sum) [GHMSS16, Section 3]: the sign of `z` in
`[z]`, and `x` in `⟨x⟩`. -/
def out : DynState → SignType
  | neg2 => -1
  | neg1 => -1
  | zero => 0
  | pos1 => 1
  | pos2 => 1
  | weak x => x

/-- The strong state of weight `z`, for `-2 ≤ z ≤ 2` (clamped outside this range). -/
def ofWeight (z : ℤ) : DynState :=
  if z ≤ -2 then neg2 else if z = -1 then neg1 else if z = 0 then zero
  else if z = 1 then pos1 else pos2

/-- The new state of an agent in state `a` meeting an agent in state `b`, outside annihilations
[GHMSS16, Section 3]: a weak state, or `[0]` meeting a strong state of nonzero weight, becomes
the weak state of the sign of the strong state `b` (its output); otherwise nothing changes. -/
def recruit (a b : DynState) : DynState :=
  if !b.isWeak && (a.isWeak || (a == zero && b.weight != 0)) then weak b.out else a

/-- The transition function of [GHMSS16, Section 3] (the text; Fig. 4 with its entry for `[1]`
meeting `[0]` corrected): opposite strong states annihilate (`[1], [-1]` and `[2], [-2]` into
`[0], [0]`, `[2], [-1]` into `[1], [0]`, `[-2], [1]` into `[-1], [0]`), all other encounters
recruit (`recruit`). -/
def δ : DynState × DynState → DynState × DynState
  | (pos1, neg1) => (zero, zero)
  | (neg1, pos1) => (zero, zero)
  | (pos2, neg2) => (zero, zero)
  | (neg2, pos2) => (zero, zero)
  | (pos2, neg1) => (pos1, zero)
  | (neg1, pos2) => (zero, pos1)
  | (neg2, pos1) => (neg1, zero)
  | (pos1, neg2) => (zero, neg1)
  | (a, b) => (recruit a b, recruit b a)

/-- The state change forced by a colour change `c → c'` [GHMSS16, Fig. 3]: `s ↦ [w(s) + c' - c]`
if `c ≠ c'`, nothing otherwise. -/
def recolour (c c' : SignType) (s : DynState) : DynState :=
  if c = c' then s else ofWeight (s.weight + c' - c)

/-- `ofWeight` is the strong state of weight `z` on `[-2, 2]`. -/
theorem weight_ofWeight {z : ℤ} (h₁ : -2 ≤ z) (h₂ : z ≤ 2) : (ofWeight z).weight = z := by
  unfold ofWeight
  split_ifs <;> simp [weight] <;> omega

/-- Interactions preserve the total weight of the two agents [GHMSS16, proof of Lemma 4]. -/
theorem δ_weight (a b : DynState) :
    (δ (a, b)).1.weight + (δ (a, b)).2.weight = a.weight + b.weight := by
  revert a b; decide

end DynState

/-- The dynamic majority protocol `P₂` [GHMSS16, Section 3] without the external force: input
colour `x ↦ [x]`. Its `Bool` output (more `1`s than `-1`s) is not used; the outputs are
`DynState.out`. -/
def dynamicMajority : Protocol SignType DynState where
  input x := DynState.ofWeight x
  output s := decide (s.out = 1)
  δ := DynState.δ

/-- Eight states. -/
theorem card_dynState : Fintype.card DynState = 8 := rfl

namespace Protocol

variable {X Q G : Type*} {n : ℕ}

/-- A step between two agents of the same group (`grp` assigns a group to every agent). -/
def GStep (P : Protocol X Q) (grp : Fin n → G) (c d : Fin n → Q) : Prop :=
  ∃ e : AgentPair n, grp e.1.1 = grp e.1.2 ∧ d = P.interact c e

/-- Reachability by steps inside groups. -/
def GReaches (P : Protocol X Q) (grp : Fin n → G) : (Fin n → Q) → (Fin n → Q) → Prop :=
  Relation.ReflTransGen (P.GStep grp)

/-- With a single group, steps inside groups are all steps. -/
theorem gReaches_const_iff (P : Protocol X Q) (g : G) {c d : Fin n → Q} :
    P.GReaches (fun _ => g) c d ↔ P.Reaches c d := by
  have : P.GStep (fun _ : Fin n => g) = P.Step := by
    funext c d
    exact propext ⟨fun ⟨e, _, he⟩ => ⟨e, he⟩, fun ⟨e, he⟩ => ⟨e, rfl, he⟩⟩
  rw [GReaches, this, Reaches]

end Protocol

variable {G : Type*} [DecidableEq G] {n : ℕ}

/-- The invariants of [GHMSS16, Section 3] for the colours `col` and the states `c`, group by
group: (1) in every group the colour sum equals the weight sum; (2) `|w(s_a) - c_a| ≤ 1` for every
agent; and (3) every group contains a strong state. (3) is not stated in the paper but used in the
tie case of its final argument (an agent in state `[0]` must remain); it holds initially and is
preserved. -/
structure DynInv (grp : Fin n → G) (col : Fin n → SignType) (c : Fin n → DynState) : Prop where
  /-- Invariant 1, in every group. -/
  sum_eq : ∀ v, ∑ u ∈ univ.filter (fun u => grp u = grp v), ((col u : SignType) : ℤ) =
    ∑ u ∈ univ.filter (fun u => grp u = grp v), (c u).weight
  /-- Invariant 2. -/
  close : ∀ v, |(c v).weight - ((col v : SignType) : ℤ)| ≤ 1
  /-- Every group contains a strong state. -/
  strong : ∀ v, ∃ u, grp u = grp v ∧ (c u).isWeak = false

/-- The initial configuration `[c_a]` satisfies the invariants. -/
theorem DynInv.input (grp : Fin n → G) (col : Fin n → SignType) :
    DynInv grp col (fun v => DynState.ofWeight (col v)) := by
  have hw : ∀ x : SignType, (DynState.ofWeight x).weight = x := by decide
  have hs : ∀ x : SignType, (DynState.ofWeight x).isWeak = false := by decide
  refine ⟨fun v => ?_, fun v => ?_, fun v => ⟨v, rfl, hs _⟩⟩
  · simp only [hw]
  · simp [hw]

/-- **[GHMSS16, Lemma 4]**, interactions. Steps inside groups preserve the invariants (the colours
do not change). -/
theorem DynInv.gstep {grp : Fin n → G} {col : Fin n → SignType} {c d : Fin n → DynState}
    (hc : DynInv grp col c) (h : dynamicMajority.GStep grp c d) : DynInv grp col d := by
  sorry

/-- **[GHMSS16, Lemma 4]**, the external force. Changing the colour of agent `v` to `x` and its
state by `DynState.recolour` preserves the invariants. -/
theorem DynInv.recolour {grp : Fin n → G} {col : Fin n → SignType} {c : Fin n → DynState}
    (hc : DynInv grp col c) (v : Fin n) (x : SignType) :
    DynInv grp (Function.update col v x)
      (Function.update c v (DynState.recolour (col v) x (c v))) := by
  sorry

namespace DynState

/-- **[GHMSS16, Lemma 5]**, first part. `R = ∑ |w|` does not increase along interactions. -/
theorem absWeight_sum_gstep_le {grp : Fin n → G} {c d : Fin n → DynState}
    (h : dynamicMajority.GStep grp c d) : ∑ v, |(d v).weight| ≤ ∑ v, |(c v).weight| := by
  sorry

/-- **[GHMSS16, Lemma 5]**, second part. Interactions inside groups reach a configuration in
which no two agents of the same group have weights of opposite signs. -/
theorem exists_greaches_noOpposite (grp : Fin n → G) (c : Fin n → DynState) :
    ∃ d, dynamicMajority.GReaches grp c d ∧
      ∀ u v, grp u = grp v → 0 ≤ (d u).weight * (d v).weight := by
  sorry

end DynState

/-- **[GHMSS16, Section 3, after Lemma 5]** Stabilization of the dynamic majority protocol. From a
configuration satisfying the invariants, interactions inside groups reach a configuration from
which, along every further execution inside groups, every agent outputs the sign of the colour sum
of its group (`1`: more `1`s, `-1`: more `-1`s, `0`: a tie). -/
theorem DynInv.exists_stable {grp : Fin n → G} {col : Fin n → SignType} {c : Fin n → DynState}
    (hc : DynInv grp col c) :
    ∃ d, dynamicMajority.GReaches grp c d ∧
      ∀ e, dynamicMajority.GReaches grp d e → ∀ v, (e v).out =
        SignType.sign (∑ u ∈ univ.filter (fun u => grp u = grp v), ((col u : SignType) : ℤ)) := by
  sorry

/-- An interaction of `P₂` (the colours are unchanged) or a colour change of one agent by the
external force (with the state change of Fig. 3), on pairs (colours, states). -/
def DynExtStep (p q : (Fin n → SignType) × (Fin n → DynState)) : Prop :=
  (q.1 = p.1 ∧ dynamicMajority.Step p.2 q.2) ∨
    ∃ v x, q = (Function.update p.1 v x,
      Function.update p.2 v (DynState.recolour (p.1 v) x (p.2 v)))

/-- **[GHMSS16, Section 3]** The dynamic majority protocol with the external force. Start from the
colours `ι` in the states `[ι a]`, and let interactions and colour changes alternate arbitrarily,
reaching the colours `col` and the states `c`. If the force stops there, the protocol reaches a
configuration that is output-stable with the sign of the final colour sum at every agent. -/
theorem dynamicMajority_stabilizes (hn : 0 < n) {ι col : Fin n → SignType}
    {c : Fin n → DynState}
    (h : Relation.ReflTransGen DynExtStep (ι, dynamicMajority.input ∘ ι) (col, c)) :
    ∃ d, dynamicMajority.Reaches c d ∧
      dynamicMajority.OutputStableAt DynState.out
        (fun _ => SignType.sign (∑ v, ((col v : SignType) : ℤ))) d := by
  sorry

/-- Without the external force, the dynamic majority protocol stably computes the sign of
`#1 - #(-1)`, like the static one. -/
theorem dynamicMajority_stablyComputes :
    dynamicMajority.StablyComputesWith DynState.out
      fun x => SignType.sign ((x 1 : ℤ) - x (-1)) := by
  sorry

end Crn
