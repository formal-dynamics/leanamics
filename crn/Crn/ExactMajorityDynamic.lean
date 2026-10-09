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

namespace DynState

/-- `R = ∑ |w|` does not increase in an encounter [GHMSS16, proof of Lemma 5]. -/
theorem absWeight_δ_le (a b : DynState) :
    |(δ (a, b)).1.weight| + |(δ (a, b)).2.weight| ≤ |a.weight| + |b.weight| := by
  revert a b; decide

/-- `R` decreases in an encounter of opposite weights. -/
theorem natAbs_δ_lt (a b : DynState) (h : a.weight * b.weight < 0) :
    (δ (a, b)).1.weight.natAbs + (δ (a, b)).2.weight.natAbs <
      a.weight.natAbs + b.weight.natAbs := by
  revert a b; decide

/-- Invariant 2 of the initiator is preserved by an encounter [GHMSS16, proof of Lemma 4]: its
weight does not change sign and does not grow in absolute value. -/
theorem close_δ_fst (x : SignType) (a b : DynState) (h : |a.weight - x| ≤ 1) :
    |(δ (a, b)).1.weight - x| ≤ 1 := by
  revert x a b; decide

/-- Invariant 2 of the responder is preserved by an encounter. -/
theorem close_δ_snd (x : SignType) (a b : DynState) (h : |b.weight - x| ≤ 1) :
    |(δ (a, b)).2.weight - x| ≤ 1 := by
  revert x a b; decide

/-- An encounter never removes the last strong state. -/
theorem δ_strong (a b : DynState) (h : a.isWeak = false ∨ b.isWeak = false) :
    (δ (a, b)).1.isWeak = false ∨ (δ (a, b)).2.isWeak = false := by
  revert a b; decide

/-- The states reporting `s` are closed under encounters. -/
theorem δ_out (s : SignType) (a b : DynState) (ha : a.out = s) (hb : b.out = s) :
    (δ (a, b)).1.out = s ∧ (δ (a, b)).2.out = s := by
  revert s a b; decide

/-- A strong state `a` of weight sign `s` recruits every state of weight `0` or of sign `s` that
does not report `s` into `⟨s⟩`, and keeps its state. -/
theorem δ_recruit (s : SignType) (a b : DynState) (ha : a.isWeak = false)
    (has : SignType.sign a.weight = s) (hb : b.weight = 0 ∨ SignType.sign b.weight = s)
    (hbs : b.out ≠ s) : δ (a, b) = (a, weak s) := by
  revert s a b; decide

/-- A strong state reports the sign of its weight. -/
theorem out_of_isWeak_eq_false (a : DynState) (ha : a.isWeak = false) :
    a.out = SignType.sign a.weight := by
  revert a; decide

/-- A state of nonzero weight is strong. -/
theorem isWeak_of_weight_ne_zero (a : DynState) (h : a.weight ≠ 0) : a.isWeak = false := by
  revert a; decide

/-- The colour change is trivial if the colour does not change. -/
theorem recolour_self (x : SignType) (a : DynState) : recolour x x a = a := if_pos rfl

/-- `ofWeight` is strong. -/
theorem isWeak_ofWeight (z : ℤ) : (ofWeight z).isWeak = false := by
  unfold ofWeight
  split_ifs <;> rfl

end DynState

/-- Sums over a group across an encounter inside a group: if the encounter preserves
`F a + F b`, the sum of `F` over every group is preserved. -/
theorem sum_group_interact {X Q M : Type*} [AddCancelCommMonoid M] (P : Protocol X Q)
    (F : Q → M) (hF : ∀ a b, F (P.δ (a, b)).1 + F (P.δ (a, b)).2 = F a + F b)
    {grp : Fin n → G} (c : Fin n → Q) (e : AgentPair n) (he : grp e.1.1 = grp e.1.2) (g : G) :
    ∑ u ∈ univ.filter (fun u => grp u = g), F (P.interact c e u) =
      ∑ u ∈ univ.filter (fun u => grp u = g), F (c u) := by
  rw [sum_filter, sum_filter]
  have h := sum_add_pair e.2 (fun u => if grp u = g then F (c u) else 0)
    (fun u => if grp u = g then F (P.interact c e u) else 0)
    (fun w h1 h2 => by simp only [P.interact_of_ne c e h1 h2])
  simp only [P.interact_fst, P.interact_snd] at h
  by_cases hg : grp e.1.1 = g
  · simp only [if_pos hg, if_pos (he.symm.trans hg), hF] at h
    exact add_right_cancel h
  · simp only [if_neg hg, if_neg fun h' => hg (he.trans h')] at h
    exact add_right_cancel h

/-- A sum of a function that differs from another one only at `v`. -/
theorem sum_eq_add_of_eq_off {M : Type*} [AddCommGroup M] (s : Finset (Fin n))
    {F F' : Fin n → M} (v : Fin n) (h : ∀ u, u ≠ v → F' u = F u) :
    ∑ u ∈ s, F' u = ∑ u ∈ s, F u + if v ∈ s then F' v - F v else 0 := by
  by_cases hv : v ∈ s
  · rw [if_pos hv, ← add_sum_erase s F' hv, ← add_sum_erase s F hv,
      sum_congr rfl fun u hu => h u (ne_of_mem_erase hu)]
    abel
  · rw [if_neg hv, add_zero]
    exact sum_congr rfl fun u hu => h u fun h' => hv (h' ▸ hu)

/-- **[GHMSS16, Lemma 4]**, interactions. Steps inside groups preserve the invariants (the colours
do not change). -/
theorem DynInv.gstep {grp : Fin n → G} {col : Fin n → SignType} {c d : Fin n → DynState}
    (hc : DynInv grp col c) (h : dynamicMajority.GStep grp c d) : DynInv grp col d := by
  obtain ⟨e, he, rfl⟩ := h
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [hc.sum_eq v, sum_group_interact dynamicMajority DynState.weight DynState.δ_weight c e he]
  · rw [Protocol.interact_apply]
    split_ifs with h2 h1
    · subst h2
      exact DynState.close_δ_snd _ _ _ (hc.close _)
    · subst h1
      exact DynState.close_δ_fst _ _ _ (hc.close _)
    · exact hc.close v
  · obtain ⟨u, hu, hu'⟩ := hc.strong v
    by_cases h1 : u = e.1.1 ∨ u = e.1.2
    · have hg : grp e.1.1 = grp v ∧ grp e.1.2 = grp v := by
        rcases h1 with rfl | rfl
        · exact ⟨hu, he.symm.trans hu⟩
        · exact ⟨he.trans hu, hu⟩
      have hs : (c e.1.1).isWeak = false ∨ (c e.1.2).isWeak = false := by
        rcases h1 with rfl | rfl
        · exact Or.inl hu'
        · exact Or.inr hu'
      rcases DynState.δ_strong _ _ hs with h | h
      · exact ⟨e.1.1, hg.1, by rw [Protocol.interact_fst]; exact h⟩
      · exact ⟨e.1.2, hg.2, by rw [Protocol.interact_snd]; exact h⟩
    · obtain ⟨h1, h2⟩ := not_or.1 h1
      exact ⟨u, hu, by rw [Protocol.interact_of_ne _ _ _ h1 h2]; exact hu'⟩

/-- **[GHMSS16, Lemma 4]**, the external force. Changing the colour of agent `v` to `x` and its
state by `DynState.recolour` preserves the invariants. -/
theorem DynInv.recolour {grp : Fin n → G} {col : Fin n → SignType} {c : Fin n → DynState}
    (hc : DynInv grp col c) (v : Fin n) (x : SignType) :
    DynInv grp (Function.update col v x)
      (Function.update c v (DynState.recolour (col v) x (c v))) := by
  by_cases hx : col v = x
  · have h1 : DynState.recolour (col v) x (c v) = c v := if_pos hx
    rw [h1, Function.update_eq_self, ← hx, Function.update_eq_self]
    exact hc
  have h1 : DynState.recolour (col v) x (c v) = DynState.ofWeight ((c v).weight + x - col v) :=
    if_neg hx
  have hcl := abs_le.1 (hc.close v)
  have hx1 : ∀ y : SignType, -1 ≤ (y : ℤ) ∧ (y : ℤ) ≤ 1 := by decide
  have hw : (DynState.ofWeight ((c v).weight + x - col v)).weight = (c v).weight + x - col v :=
    DynState.weight_ofWeight (by linarith [hx1 x]) (by linarith [hx1 x])
  rw [h1]
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
  · have hcol : ∀ w, w ≠ v →
        ((Function.update col v x w : SignType) : ℤ) = ((col w : SignType) : ℤ) := fun w hw =>
      by rw [Function.update_of_ne hw]
    have hst : ∀ w, w ≠ v →
        (Function.update c v (DynState.ofWeight ((c v).weight + x - col v)) w).weight =
          (c w).weight := fun w hw => by rw [Function.update_of_ne hw]
    rw [sum_eq_add_of_eq_off _ v hcol, sum_eq_add_of_eq_off _ v hst, hc.sum_eq u,
      Function.update_self, Function.update_self, hw]
    congr 1
    split_ifs <;> ring
  · by_cases hu : u = v
    · subst hu
      rw [Function.update_self, Function.update_self, hw,
        show (c u).weight + x - col u - x = (c u).weight - col u by ring]
      exact hc.close u
    · rw [Function.update_of_ne hu, Function.update_of_ne hu]
      exact hc.close u
  · obtain ⟨w, hw1, hw2⟩ := hc.strong u
    by_cases hwv : w = v
    · exact ⟨v, hwv ▸ hw1, by rw [Function.update_self]; exact DynState.isWeak_ofWeight _⟩
    · exact ⟨w, hw1, by rw [Function.update_of_ne hwv]; exact hw2⟩

namespace DynState

omit [DecidableEq G] in
/-- **[GHMSS16, Lemma 5]**, first part. `R = ∑ |w|` does not increase along interactions. -/
theorem absWeight_sum_gstep_le {grp : Fin n → G} {c d : Fin n → DynState}
    (h : dynamicMajority.GStep grp c d) : ∑ v, |(d v).weight| ≤ ∑ v, |(c v).weight| := by
  obtain ⟨e, -, rfl⟩ := h
  have h1 := dynamicMajority.sum_interact (fun s => |s.weight|) c e
  have h2 := absWeight_δ_le (c e.1.1) (c e.1.2)
  simp only [show dynamicMajority.δ = δ from rfl] at h1
  linarith

/-- **[GHMSS16, Lemma 5]**, second part. Interactions inside groups reach a configuration in
which no two agents of the same group have weights of opposite signs. -/
theorem exists_greaches_noOpposite (grp : Fin n → G) (c : Fin n → DynState) :
    ∃ d, dynamicMajority.GReaches grp c d ∧
      ∀ u v, grp u = grp v → 0 ≤ (d u).weight * (d v).weight := by
  refine (exists_reflTransGen_of_measure (r := dynamicMajority.GStep grp) (fun _ => True)
    (fun d => ∀ u v, grp u = grp v → 0 ≤ (d u).weight * (d v).weight)
    (fun d => ∑ v, (d v).weight.natAbs) (fun d _ => ?_) trivial).imp
    fun d hd => ⟨hd.1, hd.2.2⟩
  by_cases hG : ∀ u v, grp u = grp v → 0 ≤ (d u).weight * (d v).weight
  · exact Or.inl hG
  right
  push Not at hG
  obtain ⟨u, v, huv, hlt⟩ := hG
  have hne : u ≠ v := fun h => by subst h; exact absurd hlt (not_lt.2 (mul_self_nonneg _))
  refine ⟨dynamicMajority.interact d ⟨(u, v), hne⟩, ⟨⟨(u, v), hne⟩, huv, rfl⟩, trivial, ?_⟩
  have h1 := dynamicMajority.sum_interact (fun s => s.weight.natAbs) d ⟨(u, v), hne⟩
  have h2 := natAbs_δ_lt (d u) (d v) hlt
  dsimp only at h1
  simp only [show dynamicMajority.δ = δ from rfl] at h1
  omega

end DynState

/-- The invariants hold along every execution inside groups. -/
theorem DynInv.greaches {grp : Fin n → G} {col : Fin n → SignType} {c d : Fin n → DynState}
    (hc : DynInv grp col c) (h : dynamicMajority.GReaches grp c d) : DynInv grp col d := by
  induction h with
  | refl => exact hc
  | tail _ hst ih => exact ih.gstep hst

/-- **[GHMSS16, Section 3, after Lemma 5]** Stabilization of the dynamic majority protocol. From a
configuration satisfying the invariants, interactions inside groups reach a configuration from
which, along every further execution inside groups, every agent outputs the sign of the colour sum
of its group (`1`: more `1`s, `-1`: more `-1`s, `0`: a tie). -/
theorem DynInv.exists_stable {grp : Fin n → G} {col : Fin n → SignType} {c : Fin n → DynState}
    (hc : DynInv grp col c) :
    ∃ d, dynamicMajority.GReaches grp c d ∧
      ∀ e, dynamicMajority.GReaches grp d e → ∀ v, (e v).out =
        SignType.sign (∑ u ∈ univ.filter (fun u => grp u = grp v), ((col u : SignType) : ℤ)) := by
  obtain ⟨d, hcd, hno⟩ := DynState.exists_greaches_noOpposite grp c
  have hd := hc.greaches hcd
  obtain ⟨s, hs_def⟩ : ∃ s : Fin n → SignType, s = fun v => SignType.sign
      (∑ u ∈ univ.filter (fun u => grp u = grp v), ((col u : SignType) : ℤ)) := ⟨_, rfl⟩
  have hs : ∀ u v, grp u = grp v → s u = s v := fun u v h => by rw [hs_def]; dsimp only; rw [h]
  have hsd : ∀ v, s v = SignType.sign (∑ u ∈ univ.filter (fun u => grp u = grp v),
      (d u).weight) := fun v => by rw [hs_def]; dsimp only; rw [hd.sum_eq v]
  -- in every group, the nonzero weights have the sign of the colour sum
  have hallow : ∀ u, (d u).weight = 0 ∨ SignType.sign (d u).weight = s u := by
    intro u
    by_cases h0 : (d u).weight = 0
    · exact Or.inl h0
    right
    have hmem : u ∈ univ.filter (fun w => grp w = grp u) := by simp
    rw [hsd u]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hle : ∀ w ∈ univ.filter (fun w => grp w = grp u), 0 ≤ -(d w).weight := by
        intro w hw
        have := hno u w (mem_filter.1 hw).2.symm
        nlinarith
      have := single_le_sum hle hmem
      rw [sum_neg_distrib] at this
      rw [sign_neg hneg, sign_neg (by linarith)]
    · have hle : ∀ w ∈ univ.filter (fun w => grp w = grp u), 0 ≤ (d w).weight := by
        intro w hw
        have := hno u w (mem_filter.1 hw).2.symm
        nlinarith
      have := single_le_sum hle hmem
      rw [sign_pos hpos, sign_pos (by linarith)]
  -- in every group, a strong agent of weight sign the sign of the colour sum
  have hlead : ∀ v, ∃ r, grp r = grp v ∧ (d r).isWeak = false ∧
      SignType.sign (d r).weight = s v := by
    intro v
    by_cases hS : ∑ u ∈ univ.filter (fun u => grp u = grp v), (d u).weight = 0
    · obtain ⟨r, hr, hr'⟩ := hd.strong v
      refine ⟨r, hr, hr', ?_⟩
      rw [← hs r v hr]
      rcases hallow r with h | h
      · rw [h, hs r v hr, hsd v, hS]
      · exact h
    · obtain ⟨r, hr, hr'⟩ := exists_ne_zero_of_sum_ne_zero hS
      have hgr := (mem_filter.1 hr).2
      exact ⟨r, hgr, DynState.isWeak_of_weight_ne_zero _ hr',
        (hs r v hgr) ▸ (hallow r).resolve_left hr'⟩
  -- recruitment inside every group
  have hstep : ∀ c : Fin n → DynState,
      ((∀ u, (c u).weight = 0 ∨ SignType.sign (c u).weight = s u) ∧
        ∀ v, ∃ r, grp r = grp v ∧ (c r).isWeak = false ∧ SignType.sign (c r).weight = s v) →
      ∀ v, ¬ (c v).out = s v → ∃ c', dynamicMajority.GStep grp c c' ∧
        ((∀ u, (c' u).weight = 0 ∨ SignType.sign (c' u).weight = s u) ∧
          ∀ v, ∃ r, grp r = grp v ∧ (c' r).isWeak = false ∧
            SignType.sign (c' r).weight = s v) ∧
        (c' v).out = s v ∧ ∀ w, (c w).out = s w → (c' w).out = s w := by
    rintro c ⟨hok, hld⟩ v hv
    obtain ⟨r, hrg, hrw, hrs⟩ := hld v
    have hrv : r ≠ v := fun h => hv (by
      rw [← h, DynState.out_of_isWeak_eq_false _ hrw, hrs, h])
    have happ : ∀ w, dynamicMajority.interact c ⟨(r, v), hrv⟩ w =
        if w = v then .weak (s v) else c w := fun w => by
      rw [Protocol.interact_apply]
      dsimp only
      rw [show dynamicMajority.δ = DynState.δ from rfl,
        DynState.δ_recruit (s v) (c r) (c v) hrw hrs (hok v) hv]
      split_ifs with h1 h2
      · rfl
      · rw [h2]
      · rfl
    refine ⟨dynamicMajority.interact c ⟨(r, v), hrv⟩, ⟨⟨(r, v), hrv⟩, hrg, rfl⟩,
      ⟨fun u => ?_, fun v' => ?_⟩, ?_, fun w hw => ?_⟩
    · rw [happ]
      split_ifs
      · exact Or.inl rfl
      · exact hok u
    · obtain ⟨r', hr'g, hr'w, hr's⟩ := hld v'
      have hr'v : r' ≠ v := fun h => by
        subst h
        exact hv (by rw [DynState.out_of_isWeak_eq_false _ hr'w, hr's, hs _ _ hr'g])
      exact ⟨r', hr'g, by rw [happ, if_neg hr'v]; exact hr'w, by rw [happ, if_neg hr'v]; exact hr's⟩
    · rw [happ, if_pos rfl]
      rfl
    · rw [happ]
      split_ifs with h
      · subst h
        rfl
      · exact hw
  obtain ⟨f, hdf, -, hf⟩ := exists_recruit (r := dynamicMajority.GStep grp) _
    (fun v q => q.out = s v) hstep ⟨hallow, hlead⟩
  -- the configurations in which every agent reports `s` are closed under steps inside groups
  have hclosed : ∀ c' e', (∀ v, (c' v).out = s v) → dynamicMajority.GStep grp c' e' →
      ∀ v, (e' v).out = s v := by
    rintro c' _ hc' ⟨e, he, rfl⟩ w
    have hse : s e.1.1 = s e.1.2 := hs _ _ he
    have h1 : (c' e.1.1).out = s e.1.2 := by rw [← hse]; exact hc' _
    have h2 : (c' e.1.2).out = s e.1.1 := by rw [hse]; exact hc' _
    rw [Protocol.interact_apply]
    split_ifs with hw2 hw1
    · rw [hw2]
      exact (DynState.δ_out _ _ _ h1 (hc' _)).2
    · rw [hw1]
      exact (DynState.δ_out _ _ _ (hc' _) h2).1
    · exact hc' w
  refine ⟨f, Relation.ReflTransGen.trans hcd hdf, fun e he v => ?_⟩
  have : ∀ v, (e v).out = s v := by
    clear v
    induction he with
    | refl => exact hf
    | tail _ hst ih => exact hclosed _ _ ih hst
  rw [this v, hs_def]

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
  -- `0 < n` is not needed: for the empty population the statement is trivial
  have _ := hn
  have key : ∀ p : (Fin n → SignType) × (Fin n → DynState),
      Relation.ReflTransGen DynExtStep (ι, dynamicMajority.input ∘ ι) p →
      DynInv (fun _ : Fin n => ()) p.1 p.2 := by
    intro p hp
    induction hp with
    | refl => exact DynInv.input _ ι
    | tail _ hst ih =>
      rcases hst with ⟨h1, e, he⟩ | ⟨v, x, rfl⟩
      · rw [h1]
        exact ih.gstep ⟨e, rfl, he⟩
      · exact ih.recolour v x
  obtain ⟨d, hd, hst⟩ := (key _ h).exists_stable
  refine ⟨d, (Protocol.gReaches_const_iff _ ()).1 hd, fun e he v => ?_⟩
  rw [hst e ((Protocol.gReaches_const_iff _ ()).2 he) v, filter_true_of_mem fun _ _ => rfl]

/-- Without the external force, the dynamic majority protocol stably computes the sign of
`#1 - #(-1)`, like the static one. -/
theorem dynamicMajority_stablyComputes :
    dynamicMajority.StablyComputesWith DynState.out
      fun x => SignType.sign ((x 1 : ℤ) - x (-1)) := by
  intro n hn ι c hc
  obtain ⟨d, hd, hst⟩ := dynamicMajority_stabilizes hn
    (Relation.ReflTransGen.lift (fun c => (ι, c)) (fun _ _ hab => Or.inl ⟨rfl, hab⟩) _ _ hc)
  refine ⟨d, hd, fun e he v => ?_⟩
  rw [hst e he v, sum_signType_eq_counts]

end Crn
