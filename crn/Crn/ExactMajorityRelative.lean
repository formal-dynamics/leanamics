import Crn.ExactMajorityAbsolute

/-!
# Relative majority (plurality) with `O(k)`-bit states (CRN-5, [GHMSS16, Section 5])

Algorithm Relative-Majority [GHMSS16, Section 5.1]. Colours are `k`-bit labels; the winner is the
most frequent label, ties broken in favour of the lexicographically largest label (bit `0` first,
`-1 < 1`, i.e. `false < true`: `IsPlurality`). Stages `i = k-1, …, 0`: in stage `i`, the agents
whose labels share the prefix `l[0..i-1]` form a group, and a copy `P₂(i)` of the dynamic
majority protocol runs inside each group, with colour `c[i] = l[i]` (as `±1`) for the agents whose
label won all stages `> i` (the winner of the group of prefix `l[0..i]`) and `c[i] = 0` for the
others. An agent wins stage `i` if `c[i] = -1` and `P₂(i)` outputs `-1`, or `c[i] = 1` and `P₂(i)`
outputs `0` or `1` (a tie goes to the larger label, `wins`).

Formalization: the protocol is the `k`-fold iteration of `Protocol.drive`
(`ExactMajorityCompose.lean`). Level `0` keeps the label; level `m + 1` drives `P₂(k-1-m)` by level
`m` through the colour `stageColour` (computed from the label and from whether the agent won the
stages `k-1, …, k-m`), in the groups of the prefixes of length `k-1-m`. The colours `c[i]` are
derived from the states rather than stored, so a change propagates through all lower stages within
the same encounter, as described in [GHMSS16, Section 5.1, Stabilisation Stage 2]. At the end
(level `k`), every agent knows whether its own colour is the winner (`RelState.won`): the protocol
marks the agents of the winning colour [GHMSS16, Section 5].

Main statements:
* `duel_wins_iff` (one stage of the proof of Theorem 7): the duel of stage `i` between the group
  winners of the prefixes `p·(-1)` and `p·1` selects the winner of the group of prefix `p`.
* `relativeMajority_level_stablyMarks` (the induction of the proof of Theorem 7).
* `relativeMajority_stablyMarks` (Theorem 7).
* `card_relState` (Theorem 7, space): `2^k · 8^k = 2^(4k)` states, i.e. `4k` bits.
-/

namespace Crn

open Finset

variable {k : ℕ}

/-- The states of level `m` of Relative-Majority: the label and the states of `P₂` at the stages
`k-1, …, k-m` (the last one outermost). -/
def RelState (k : ℕ) : ℕ → Type
  | 0 => Label k
  | m + 1 => RelState k m × DynState

/-- Finitely many states. -/
instance RelState.instFintype (k : ℕ) : ∀ m, Fintype (RelState k m)
  | 0 => inferInstanceAs (Fintype (Label k))
  | m + 1 => @instFintypeProd (RelState k m) DynState (RelState.instFintype k m) _

/-- Decidable equality of states. -/
instance RelState.instDecidableEq (k : ℕ) : ∀ m, DecidableEq (RelState k m)
  | 0 => inferInstanceAs (DecidableEq (Label k))
  | m + 1 => @instDecidableEqProd (RelState k m) DynState (RelState.instDecidableEq k m) _

/-- The bit `i` of a label (`false` for `i ≥ k`). -/
def bitAt (L : Label k) (i : ℕ) : Bool := if h : i < k then L ⟨i, h⟩ else false

/-- The prefix `L[0..j-1]` of a label, padded with `false`: two labels have the same prefix of
length `j` iff their `prefixMask`s agree. -/
def prefixMask (L : Label k) (j : ℕ) : Label k := fun t => if t.val < j then L t else false

/-- Whether an agent with colour `c` for a stage, whose `P₂` reports `o`, wins the stage
[GHMSS16, Section 5.1, Stabilisation Stage 2]: `c = -1` and `o = -1`, or `c = 1` and
`o ∈ {0, 1}` (a tie goes to the lexicographically larger label). -/
def wins (c o : SignType) : Bool := (c == -1 && o == -1) || (c == 1 && o != -1)

/-- The label of an agent. -/
def RelState.label : ∀ {m : ℕ}, RelState k m → Label k
  | 0, L => L
  | m + 1, q => RelState.label (m := m) (q : RelState k m × DynState).1

/-- Whether the agent's label won all stages so far (`true` at level `0`; at level `m + 1`, it won
the stages before and wins stage `k-1-m` against the report of its `P₂(k-1-m)`). -/
def RelState.won : ∀ {m : ℕ}, RelState k m → Bool
  | 0, _ => true
  | m + 1, q =>
    wins (if RelState.won (m := m) (q : RelState k m × DynState).1 then
        bitSign (bitAt (RelState.label (m := m) (q : RelState k m × DynState).1) (k - 1 - m))
      else 0) (q : RelState k m × DynState).2.out

/-- The colour `c[k-1-m]` of an agent at level `m` [GHMSS16, Section 5, memory organisation (2)]:
its bit `l[k-1-m]` as `±1` if it won all stages so far, `0` otherwise. -/
def stageColour {m : ℕ} (q : RelState k m) : SignType :=
  if q.won then bitSign (bitAt q.label (k - 1 - m)) else 0

/-- Level `m` of Relative-Majority: the label alone at level `0`; at level `m + 1`, the dynamic
majority protocol `P₂(k-1-m)` driven by level `m` through `stageColour`, inside the groups of the
prefixes of length `k-1-m` [GHMSS16, Section 5.1]. -/
def relativeMajorityLevel (k : ℕ) : ∀ m, Protocol (Label k) (RelState k m)
  | 0 => { input := id, output := fun _ => true, δ := id }
  | m + 1 => (relativeMajorityLevel k m).drive stageColour fun q => prefixMask q.label (k - 1 - m)

/-- Algorithm Relative-Majority [GHMSS16, Section 5.1]: all `k` stages. -/
def relativeMajority (k : ℕ) : Protocol (Label k) (RelState k k) := relativeMajorityLevel k k

/-- `L` wins its group of prefix length `j`: among the labels with the same prefix `L[0..j-1]`, `L`
is the most frequent, ties broken by the lexicographic order. -/
def IsGroupWinner (x : Label k → ℕ) (j : ℕ) (L : Label k) : Prop :=
  ∀ L', prefixMask L' j = prefixMask L j → x L' < x L ∨ (x L' = x L ∧ toLex L' ≤ toLex L)

/-- `L` is the relative majority (plurality) colour [GHMSS16, Section 5]: the most frequent
colour, the lexicographically largest one among several most frequent colours. -/
def IsPlurality (x : Label k → ℕ) (L : Label k) : Prop :=
  ∀ L', x L' < x L ∨ (x L' = x L ∧ toLex L' ≤ toLex L)

noncomputable instance (x : Label k → ℕ) (j : ℕ) : DecidablePred (IsGroupWinner x j) :=
  fun _ => Classical.propDecidable _

noncomputable instance (x : Label k → ℕ) : DecidablePred (IsPlurality x) :=
  fun _ => Classical.propDecidable _

/-- The colour at stage `i` of an agent with label `L` once the stages `> i` are stable: `L[i]` as
`±1` if `L` won its group of prefix length `i + 1`, `0` otherwise. -/
noncomputable def duelColour (x : Label k → ℕ) (i : ℕ) (L : Label k) : SignType :=
  if IsGroupWinner x (i + 1) L then bitSign (bitAt L i) else 0

/-- **[GHMSS16, proof of Theorem 7], one stage.** In the group of the prefix `L[0..i-1]`, the
sum of the stage-`i` colours is `#W₁ - #W₋₁`, `W_{±1}` the winners of the subgroups of prefixes
`L[0..i-1]·(±1)`; the agent with label `L` wins the duel iff `L` wins its group of prefix length
`i`. -/
theorem duel_wins_iff (x : Label k → ℕ) {i : ℕ} (hi : i < k) (L : Label k) :
    wins (duelColour x i L) (SignType.sign (∑ j ∈ univ.filter
      (fun j => prefixMask j i = prefixMask L i), (x j : ℤ) * ((duelColour x i j : SignType) : ℤ)))
      = decide (IsGroupWinner x i L) := by
  sorry

/-- The winner of the group of prefix length `0` is the plurality colour. -/
theorem isGroupWinner_zero_iff (x : Label k → ℕ) (L : Label k) :
    IsGroupWinner x 0 L ↔ IsPlurality x L := by
  have h : ∀ L' : Label k, prefixMask L' 0 = fun _ => false := fun L' => by
    funext t; simp [prefixMask]
  simp only [IsGroupWinner, IsPlurality, h, forall_const]

/-- **[GHMSS16, proof of Theorem 7], the induction on stages.** For `m ≤ k`, level `m` stably
marks every agent with its label and with whether its label wins its group of prefix length
`k - m` (i.e. the stages `k-1, …, k-m` have stabilized). -/
theorem relativeMajority_level_stablyMarks {m : ℕ} (hm : m ≤ k) :
    (relativeMajorityLevel k m).StablyMarks (fun q => (q.label, q.won))
      fun x L => (L, decide (IsGroupWinner x (k - m) L)) := by
  sorry

/-- **[GHMSS16, Theorem 7]** Algorithm Relative-Majority stably marks the agents of the
relative majority colour: eventually and forever, an agent outputs `true` iff its colour is the
most frequent one (the lexicographically largest among several most frequent ones). -/
theorem relativeMajority_stablyMarks :
    (relativeMajority k).StablyMarks RelState.won fun x L => decide (IsPlurality x L) := by
  sorry

/-- Level `m` has `2^k · 8^m` states. -/
theorem card_relState_level (m : ℕ) : Fintype.card (RelState k m) = 2 ^ k * 8 ^ m := by
  induction m with
  | zero =>
    change Fintype.card (Label k) = _
    simp [Label]
  | succ m ih =>
    change Fintype.card (RelState k m × DynState) = _
    rw [Fintype.card_prod, ih, card_dynState, pow_succ, mul_assoc]

/-- **[GHMSS16, Theorem 7, space]** Relative-Majority has `2^k · 8^k = 2^(4k)` states (label and
`k` states of `P₂`): `4k` bits. -/
theorem card_relState :
    Fintype.card (RelState k k) = 2 ^ k * 8 ^ k ∧ 2 ^ k * 8 ^ k = 2 ^ (4 * k) := by
  refine ⟨card_relState_level k, ?_⟩
  rw [← mul_pow, pow_mul]
  norm_num

end Crn
