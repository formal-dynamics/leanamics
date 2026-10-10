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

/-- The ranking key of a label: its count first, then the label itself in lex order. -/
def winKey (x : Label k → ℕ) (L : Label k) : ℕ ×ₗ Lex (Label k) := toLex (x L, toLex L)

theorem beats_iff_winKey (x : Label k → ℕ) (L' L : Label k) :
    (x L' < x L ∨ (x L' = x L ∧ toLex L' ≤ toLex L)) ↔ winKey x L' ≤ winKey x L := by
  rw [winKey, winKey, Prod.Lex.toLex_le_toLex]

theorem winKey_injective (x : Label k → ℕ) : Function.Injective (winKey x) := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  simpa [winKey] using this

theorem isGroupWinner_iff (x : Label k → ℕ) (j : ℕ) (L : Label k) :
    IsGroupWinner x j L ↔ ∀ L', prefixMask L' j = prefixMask L j → winKey x L' ≤ winKey x L := by
  simp only [IsGroupWinner, beats_iff_winKey]

theorem prefixMask_mono {A B : Label k} {j j' : ℕ} (hjj : j ≤ j')
    (h : prefixMask A j' = prefixMask B j') : prefixMask A j = prefixMask B j := by
  funext t
  have := congrFun h t
  simp only [prefixMask] at this ⊢
  split_ifs at this ⊢ <;> first | rfl | omega

theorem prefixMask_succ_iff {i : ℕ} (hi : i < k) (A B : Label k) :
    prefixMask A (i + 1) = prefixMask B (i + 1) ↔
      prefixMask A i = prefixMask B i ∧ A ⟨i, hi⟩ = B ⟨i, hi⟩ := by
  constructor
  · intro h
    refine ⟨prefixMask_mono (Nat.le_succ i) h, ?_⟩
    simpa [prefixMask] using congrFun h ⟨i, hi⟩
  · rintro ⟨h, hb⟩
    funext t
    have := congrFun h t
    simp only [prefixMask] at this ⊢
    by_cases ht : t.val < i
    · simpa [ht, Nat.lt_succ_of_lt ht] using this
    · by_cases ht' : t.val = i
      · have : t = ⟨i, hi⟩ := Fin.ext ht'
        subst this
        simp [hb]
      · have : ¬ t.val < i + 1 := by omega
        simp [this]

theorem prefixMask_update {i : ℕ} (hi : i < k) (L : Label k) (b : Bool) :
    prefixMask (Function.update L ⟨i, hi⟩ b) i = prefixMask L i := by
  funext t
  simp only [prefixMask]
  split_ifs with ht
  · rw [Function.update_of_ne]
    rintro rfl
    simp at ht
  · rfl

theorem exists_groupWinner (x : Label k → ℕ) (j : ℕ) (L₀ : Label k) :
    ∃ W, prefixMask W j = prefixMask L₀ j ∧ IsGroupWinner x j W := by
  obtain ⟨W, hW, hmax⟩ := (univ.filter (fun L => prefixMask L j = prefixMask L₀ j)).exists_max_image
    (winKey x) ⟨L₀, by simp⟩
  simp only [mem_filter, mem_univ, true_and] at hW hmax
  exact ⟨W, hW, (isGroupWinner_iff x j W).2 fun L' hL' => hmax L' (hL'.trans hW)⟩

theorem exists_groupWinner_bit (x : Label k → ℕ) {i : ℕ} (hi : i < k) (L : Label k) (b : Bool) :
    ∃ W, prefixMask W i = prefixMask L i ∧ W ⟨i, hi⟩ = b ∧ IsGroupWinner x (i + 1) W := by
  obtain ⟨W, hW, hwin⟩ := exists_groupWinner x (i + 1) (Function.update L ⟨i, hi⟩ b)
  obtain ⟨h1, h2⟩ := (prefixMask_succ_iff hi _ _).1 hW
  exact ⟨W, h1.trans (prefixMask_update hi L b), by simpa using h2, hwin⟩

theorem groupWinner_unique (x : Label k → ℕ) {j : ℕ} {W W' : Label k} (h : IsGroupWinner x j W)
    (h' : IsGroupWinner x j W') (hp : prefixMask W j = prefixMask W' j) : W = W' :=
  winKey_injective x (le_antisymm ((isGroupWinner_iff x j W').1 h' W hp)
    ((isGroupWinner_iff x j W).1 h W' hp.symm))

theorem isGroupWinner_succ (x : Label k → ℕ) {i : ℕ} {L : Label k} (h : IsGroupWinner x i L) :
    IsGroupWinner x (i + 1) L :=
  fun L' hL' => h L' (prefixMask_mono (Nat.le_succ i) hL')

theorem toLex_lt_of_bit {i : ℕ} (hi : i < k) {A B : Label k} (hp : prefixMask A i = prefixMask B i)
    (hA : A ⟨i, hi⟩ = false) (hB : B ⟨i, hi⟩ = true) : toLex A < toLex B := by
  refine ⟨⟨i, hi⟩, fun t ht => ?_, ?_⟩
  · have := congrFun hp t
    have ht' : t.val < i := ht
    simpa [prefixMask, ht'] using this
  · simp [hA, hB]

theorem duelColour_of_winner (x : Label k → ℕ) {i : ℕ} (hi : i < k) {W : Label k}
    (hW : IsGroupWinner x (i + 1) W) : duelColour x i W = bitSign (W ⟨i, hi⟩) := by
  simp [duelColour, hW, bitAt, hi]

theorem wins_zero (o : SignType) : wins 0 o = false := by revert o; decide

theorem wins_one (o : SignType) : wins 1 o = decide (o ≠ -1) := by revert o; decide

theorem wins_neg_one (o : SignType) : wins (-1) o = decide (o = -1) := by revert o; decide

theorem duel_sum_eq (x : Label k → ℕ) {i : ℕ} (hi : i < k) {Wp Wm L : Label k}
    (hp : IsGroupWinner x (i + 1) Wp) (hm : IsGroupWinner x (i + 1) Wm)
    (hpb : Wp ⟨i, hi⟩ = true) (hmb : Wm ⟨i, hi⟩ = false)
    (hpL : prefixMask Wp i = prefixMask L i) (hmL : prefixMask Wm i = prefixMask L i) :
    ∑ j ∈ univ.filter (fun j => prefixMask j i = prefixMask L i),
      (x j : ℤ) * ((duelColour x i j : SignType) : ℤ) = x Wp - x Wm := by
  rw [Finset.sum_eq_add_of_mem Wp Wm (by simp [hpL]) (by simp [hmL])
    (fun h => by simp [h, hmb] at hpb) ?_]
  · simp [duelColour_of_winner x hi hp, duelColour_of_winner x hi hm, hpb, hmb, bitSign]
    ring
  · intro c hc hne
    simp only [mem_filter, mem_univ, true_and] at hc
    by_cases hcw : IsGroupWinner x (i + 1) c
    · exfalso
      cases hb : c ⟨i, hi⟩
      · exact hne.2 (groupWinner_unique x hcw hm
          ((prefixMask_succ_iff hi c Wm).2 ⟨hc.trans hmL.symm, hb.trans hmb.symm⟩))
      · exact hne.1 (groupWinner_unique x hcw hp
          ((prefixMask_succ_iff hi c Wp).2 ⟨hc.trans hpL.symm, hb.trans hpb.symm⟩))
    · simp [duelColour, hcw]

/-- **[GHMSS16, proof of Theorem 7], one stage.** In the group of the prefix `L[0..i-1]`, the
sum of the stage-`i` colours is `#W₁ - #W₋₁`, `W_{±1}` the winners of the subgroups of prefixes
`L[0..i-1]·(±1)`; the agent with label `L` wins the duel iff `L` wins its group of prefix length
`i`. -/
theorem duel_wins_iff (x : Label k → ℕ) {i : ℕ} (hi : i < k) (L : Label k) :
    wins (duelColour x i L) (SignType.sign (∑ j ∈ univ.filter
      (fun j => prefixMask j i = prefixMask L i), (x j : ℤ) * ((duelColour x i j : SignType) : ℤ)))
      = decide (IsGroupWinner x i L) := by
  by_cases hL : IsGroupWinner x (i + 1) L
  · cases hb : L ⟨i, hi⟩
    · -- `L` is the winner `W₋` of the half-group with bit `i` false
      obtain ⟨Wp, hpL, hpb, hp⟩ := exists_groupWinner_bit x hi L true
      rw [duel_sum_eq x hi hp hL hpb hb hpL rfl, duelColour_of_winner x hi hL, hb]
      simp only [bitSign, Bool.false_eq_true, ite_false, wins_neg_one, sign_eq_neg_one_iff]
      rw [decide_eq_decide]
      constructor
      · intro h
        rw [isGroupWinner_iff]
        intro L' hL'
        cases hb' : L' ⟨i, hi⟩
        · exact (isGroupWinner_iff x _ L).1 hL L'
            ((prefixMask_succ_iff hi L' L).2 ⟨hL', hb'.trans hb.symm⟩)
        · refine le_trans ((isGroupWinner_iff x _ Wp).1 hp L'
            ((prefixMask_succ_iff hi L' Wp).2 ⟨hL'.trans hpL.symm, hb'.trans hpb.symm⟩)) ?_
          exact (beats_iff_winKey x Wp L).1 (Or.inl (by omega))
      · intro h
        rcases h Wp hpL with h | ⟨h1, h2⟩
        · omega
        · exact absurd h2 (not_le.2 (toLex_lt_of_bit hi hpL.symm hb hpb))
    · -- `L` is the winner `W₊` of the half-group with bit `i` true
      obtain ⟨Wm, hmL, hmb, hm⟩ := exists_groupWinner_bit x hi L false
      rw [duel_sum_eq x hi hL hm hb hmb rfl hmL, duelColour_of_winner x hi hL, hb]
      simp only [bitSign, ite_true, wins_one, ne_eq, sign_eq_neg_one_iff]
      rw [decide_eq_decide]
      constructor
      · intro h
        rw [isGroupWinner_iff]
        intro L' hL'
        cases hb' : L' ⟨i, hi⟩
        · refine le_trans ((isGroupWinner_iff x _ Wm).1 hm L'
            ((prefixMask_succ_iff hi L' Wm).2 ⟨hL'.trans hmL.symm, hb'.trans hmb.symm⟩)) ?_
          rcases Nat.lt_or_eq_of_le (show x Wm ≤ x L by omega) with h' | h'
          · exact (beats_iff_winKey x Wm L).1 (Or.inl h')
          · exact (beats_iff_winKey x Wm L).1 (Or.inr ⟨h', (toLex_lt_of_bit hi hmL hmb hb).le⟩)
        · exact (isGroupWinner_iff x _ L).1 hL L'
            ((prefixMask_succ_iff hi L' L).2 ⟨hL', hb'.trans hb.symm⟩)
      · intro h
        rcases h Wm hmL with h | ⟨h1, -⟩ <;> omega
  · have h : ¬ IsGroupWinner x i L := fun h => hL (isGroupWinner_succ x h)
    simp [duelColour, hL, h, wins_zero]

/-- The winner of the group of prefix length `0` is the plurality colour. -/
theorem isGroupWinner_zero_iff (x : Label k → ℕ) (L : Label k) :
    IsGroupWinner x 0 L ↔ IsPlurality x L := by
  have h : ∀ L' : Label k, prefixMask L' 0 = fun _ => false := fun L' => by
    funext t; simp [prefixMask]
  simp only [IsGroupWinner, IsPlurality, h, forall_const]

/-- The transitions of every level keep the labels. -/
theorem relativeMajorityLevel_δ_label : ∀ (m : ℕ) (p q : RelState k m),
    ((relativeMajorityLevel k m).δ (p, q)).1.label = p.label ∧
      ((relativeMajorityLevel k m).δ (p, q)).2.label = q.label
  | 0, _, _ => ⟨rfl, rfl⟩
  | m + 1, p, q => relativeMajorityLevel_δ_label m p.1 q.1

/-- The initial state of every level carries the input label. -/
theorem relativeMajorityLevel_input_label : ∀ (m : ℕ) (L : Label k),
    ((relativeMajorityLevel k m).input L).label = L
  | 0, _ => rfl
  | m + 1, L => relativeMajorityLevel_input_label m L

/-- Level `0` never changes a configuration. -/
theorem relativeMajorityLevel_zero_reaches {n : ℕ} {c d : Fin n → RelState k 0}
    (h : (relativeMajorityLevel k 0).Reaches c d) : d = c := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rw [Protocol.interact_eq_self _ _ _ rfl, ih]

/-- The prefix of length `k` is the whole label. -/
theorem prefixMask_self (L : Label k) : prefixMask L k = L := by
  funext t
  simp [prefixMask]

/-- Every label wins its group of prefix length `k` (the group of the label alone). -/
theorem isGroupWinner_self (x : Label k → ℕ) (L : Label k) : IsGroupWinner x k L := by
  intro L' hL'
  rw [prefixMask_self, prefixMask_self] at hL'
  subst hL'
  exact Or.inr ⟨rfl, le_rfl⟩

/-- **[GHMSS16, proof of Theorem 7], the induction on stages.** For `m ≤ k`, level `m` stably
marks every agent with its label and with whether its label wins its group of prefix length
`k - m` (i.e. the stages `k-1, …, k-m` have stabilized). -/
theorem relativeMajority_level_stablyMarks {m : ℕ} (hm : m ≤ k) :
    (relativeMajorityLevel k m).StablyMarks (fun q => (q.label, q.won))
      fun x L => (L, decide (IsGroupWinner x (k - m) L)) := by
  induction m with
  | zero =>
    intro n hn ι c hc
    refine ⟨c, Protocol.Reaches.refl _, fun f hf v => ?_⟩
    rw [relativeMajorityLevel_zero_reaches (hc.trans hf)]
    show (ι v, true) = (ι v, decide (IsGroupWinner (counts ι).1 (k - 0) (ι v)))
    rw [Nat.sub_zero, decide_eq_true (isGroupWinner_self _ _)]
  | succ m ih =>
    have hi : k - 1 - m < k := by omega
    have hkm : k - m = k - 1 - m + 1 := by omega
    -- level `m` stably marks every agent with its eventual colour for stage `k - 1 - m`
    have hD : (relativeMajorityLevel k m).StablyMarks (fun q => ((q.label, q.won), stageColour q))
        fun x L => ((L, decide (IsGroupWinner x (k - 1 - m + 1) L)), duelColour x (k - 1 - m) L) :=
      ((ih (by omega)).map fun p => (p, if p.2 then bitSign (bitAt p.1 (k - 1 - m)) else 0)).congr
        (fun _ => rfl) fun x L => by
          rw [hkm]
          unfold duelColour
          by_cases h : IsGroupWinner x (k - 1 - m + 1) L <;> simp [h]
    -- the composition step, then the duel lemma
    have h := Protocol.drive_stablyMarks (D := relativeMajorityLevel k m) (col := stageColour)
      (grp := fun q => prefixMask q.label (k - 1 - m)) (γ := fun L => prefixMask L (k - 1 - m))
      (fun p q => ⟨by rw [(relativeMajorityLevel_δ_label m p q).1],
        by rw [(relativeMajorityLevel_δ_label m p q).2]⟩)
      (fun L => by rw [relativeMajorityLevel_input_label]) hD
    refine (h.map fun p =>
      (p.1.1, wins (if p.1.2 then bitSign (bitAt p.1.1 (k - 1 - m)) else 0) p.2)).congr
      (fun _ => rfl) fun x L => ?_
    rw [show k - (m + 1) = k - 1 - m by omega, ← duel_wins_iff x hi L]
    congr 2
    unfold duelColour
    by_cases h : IsGroupWinner x (k - 1 - m + 1) L <;> simp [h]

/-- **[GHMSS16, Theorem 7]** Algorithm Relative-Majority stably marks the agents of the
relative majority colour: eventually and forever, an agent outputs `true` iff its colour is the
most frequent one (the lexicographically largest among several most frequent ones). -/
theorem relativeMajority_stablyMarks :
    (relativeMajority k).StablyMarks RelState.won fun x L => decide (IsPlurality x L) := by
  refine ((relativeMajority_level_stablyMarks (k := k) le_rfl).map Prod.snd).congr (fun _ => rfl)
    fun x L => ?_
  rw [Nat.sub_self]
  exact decide_eq_decide.2 (isGroupWinner_zero_iff x L)

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
