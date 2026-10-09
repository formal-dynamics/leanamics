import Crn.ExactMajorityCompose

/-!
# Absolute majority with `O(k)`-bit states (CRN-5, [GHMSS16, Section 4])

Colours are `k`-bit labels `L : Fin k → Bool` (`Label k`; [GHMSS16] reads the bits as `±1`,
`bitSign`); a population with `C ≤ 2^k` colours uses `C` of the labels. Algorithm
Absolute-Majority [GHMSS16, Section 4.1]: every agent keeps its label `l`, runs `k` independent
copies `P₁(i)` of the static majority protocol on the bits `l[i]` (`bitsProtocol`), and a copy of
the dynamic majority protocol `P₂` whose colour is `1` if the agent's label agrees with all the
majority bits currently reported by its `P₁(i)`, and `-1` otherwise (`absColour`); `P₂` decides
whether the label of the reported majority bits is held by more than half of the agents. An agent
outputs `some L*`, `L*` the reported majority bits, if its `P₂` outputs `1`, and `none` otherwise
(`absOutput`).

Main statements:
* `bitsProtocol_stablyMarks` ([GHMSS16, Section 4]): the `k` copies of `P₁` stably compute the `k`
  majority bits (`majBit`).
* `absTarget_sum_sign_eq_one_iff`, `majBit_eq_of_isAbsMajority` (the combinatorial part of the
  proof of Theorem 6).
* `absoluteMajority_stablyComputes` (Theorem 6): the protocol stably computes the absolute
  majority colour, or reports that there is none (`absMajority`).
* `card_absState` (Theorem 6, space): `2^k · 6^k · 8 ≤ 2^(4k+3)` states, i.e. `4k + 3` bits.
-/

namespace Crn

open Finset

/-- `k`-bit colour labels [GHMSS16, Section 4]. -/
abbrev Label (k : ℕ) := Fin k → Bool

/-- A bit read as `±1` [GHMSS16, Section 4]: `true ↦ 1`, `false ↦ -1`. -/
def bitSign (b : Bool) : SignType := if b then 1 else -1

variable {k : ℕ}

/-- The `k` independent copies `P₁(0), …, P₁(k-1)` of the static majority protocol on the bits of
the labels, the label being kept [GHMSS16, Section 4, memory organisation (1)–(2)]. The `Bool`
output is not used. -/
def bitsProtocol (k : ℕ) : Protocol (Label k) (Label k × (Fin k → StaticState)) where
  input L := (L, fun i => StaticState.strong (bitSign (L i)))
  output _ := false
  δ pq := ((pq.1.1, fun i => (StaticState.δ (pq.1.2 i, pq.2.2 i)).1),
    (pq.2.1, fun i => (StaticState.δ (pq.1.2 i, pq.2.2 i)).2))

/-- The majority bit `i` of the input counts `x`: the sign of `#(bit i = 1) - #(bit i = 0)`, the
output of `P₁(i)`. -/
noncomputable def majBit (x : Label k → ℕ) (i : Fin k) : SignType :=
  SignType.sign (∑ L, (x L : ℤ) * ((bitSign (L i) : SignType) : ℤ))

/-- Component `i` of an encounter of `bitsProtocol` is an encounter of `P₁`. -/
theorem bitsProtocol_interact_snd {n : ℕ} (c : Fin n → Label k × (Fin k → StaticState))
    (e : AgentPair n) (i : Fin k) :
    (fun w => ((bitsProtocol k).interact c e w).2 i) =
      staticMajority.interact (fun w => (c w).2 i) e := by
  funext w
  rw [Protocol.interact_apply, Protocol.interact_apply]
  split_ifs <;> rfl

/-- Encounters of `bitsProtocol` keep the labels. -/
theorem bitsProtocol_interact_fst {n : ℕ} (c : Fin n → Label k × (Fin k → StaticState))
    (e : AgentPair n) : (fun w => ((bitsProtocol k).interact c e w).1) = fun w => (c w).1 := by
  funext w
  rw [Protocol.interact_apply]
  split_ifs with h2 h1
  · rw [h2]
    rfl
  · rw [h1]
    rfl
  · rfl

/-- Paths of `bitsProtocol` project to paths of `P₁` in every component. -/
theorem bitsProtocol_reaches_snd {n : ℕ} {c d : Fin n → Label k × (Fin k → StaticState)}
    (h : (bitsProtocol k).Reaches c d) (i : Fin k) :
    staticMajority.Reaches (fun w => (c w).2 i) (fun w => (d w).2 i) := by
  induction h with
  | refl => exact Protocol.Reaches.refl _
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rw [bitsProtocol_interact_snd]
    exact ih.trans (Protocol.reaches_interact _ e)

/-- Paths of `bitsProtocol` keep the labels. -/
theorem bitsProtocol_reaches_fst {n : ℕ} {c d : Fin n → Label k × (Fin k → StaticState)}
    (h : (bitsProtocol k).Reaches c d) : (fun w => (d w).1) = fun w => (c w).1 := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rw [bitsProtocol_interact_fst, ih]

/-- A path of `P₁` in component `i` lifts to `bitsProtocol` (same encounters). -/
theorem bitsProtocol_lift {n : ℕ} (i : Fin k) {c₁ d₁ : Fin n → StaticState}
    (h : staticMajority.Reaches c₁ d₁) (c : Fin n → Label k × (Fin k → StaticState))
    (hc : (fun w => (c w).2 i) = c₁) :
    ∃ d, (bitsProtocol k).Reaches c d ∧ (fun w => (d w).2 i) = d₁ := by
  induction h with
  | refl => exact ⟨c, Protocol.Reaches.refl _, hc⟩
  | tail _ hst ih =>
    obtain ⟨d, hd, hd1⟩ := ih
    obtain ⟨e, rfl⟩ := hst
    exact ⟨_, hd.trans (Protocol.reaches_interact _ e), by rw [bitsProtocol_interact_snd, hd1]⟩

/-- The output of `P₁(i)` is the majority bit `i`: `#(bit i = 1) - #(bit i = 0)` is
`∑_L x_L · bitSign (L i)`. -/
theorem sign_counts_bit_eq_majBit {n : ℕ} (ι : Fin n → Label k) (i : Fin k) :
    SignType.sign (((counts fun v => bitSign (ι v i)).1 1 : ℤ) -
      (counts fun v => bitSign (ι v i)).1 (-1)) = majBit (counts ι).1 i := by
  rw [← sum_signType_eq_counts (fun v => bitSign (ι v i)), majBit,
    sum_comp_eq_sum_counts ι fun L => ((bitSign (L i) : SignType) : ℤ)]
  simp only [nsmul_eq_mul]

/-- **[GHMSS16, Section 4]** The `k` copies of `P₁` stably compute the `k` majority bits, and
every agent keeps its label. -/
theorem bitsProtocol_stablyMarks :
    (bitsProtocol k).StablyMarks (fun q => (fun i => (q.2 i).out, q.1))
      fun x L => (majBit x, L) := by
  intro n hn ι c hc
  -- stabilize the components in `S`, one at a time
  have key : ∀ S : Finset (Fin k), ∃ d, (bitsProtocol k).Reaches c d ∧ ∀ i ∈ S,
      staticMajority.OutputStableAt StaticState.out (fun _ => majBit (counts ι).1 i)
        (fun w => (d w).2 i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨c, Protocol.Reaches.refl _, by simp⟩
    | insert j S _ ih =>
      obtain ⟨d, hd, hS⟩ := ih
      obtain ⟨e₁, he₁, hs₁⟩ := staticMajority_stablyComputes n hn (fun v => bitSign (ι v j)) _
        (bitsProtocol_reaches_snd (hc.trans hd) j)
      obtain ⟨d', hd', hd'j⟩ := bitsProtocol_lift j he₁ d rfl
      refine ⟨d', hd.trans hd', fun i hi => ?_⟩
      rcases mem_insert.1 hi with rfl | hi
      · rw [hd'j]
        intro f hf v
        rw [hs₁ f hf v]
        exact sign_counts_bit_eq_majBit ι _
      · exact fun f hf => hS i hi f ((bitsProtocol_reaches_snd hd' i).trans hf)
  obtain ⟨d, hd, hall⟩ := key univ
  refine ⟨d, hd, fun f hf v => Prod.ext (funext fun i => ?_) ?_⟩
  · exact hall i (mem_univ i) _ (bitsProtocol_reaches_snd hf i) v
  · exact congrFun (bitsProtocol_reaches_fst ((hc.trans hd).trans hf)) v

/-- The colour of an agent for `P₂` [GHMSS16, Section 4.1, Initialisation Stage 2]: `1` if every
`P₁(i)` currently reports the agent's own bit `l[i]` as the majority bit, `-1` otherwise. -/
def absColour (q : Label k × (Fin k → StaticState)) : SignType :=
  if ∀ i, (q.2 i).out = bitSign (q.1 i) then 1 else -1

/-- Algorithm Absolute-Majority [GHMSS16, Section 4.1]: `P₂` driven by the `k` copies of `P₁`
through `absColour`, in a single group. -/
def absoluteMajority (k : ℕ) : Protocol (Label k) ((Label k × (Fin k → StaticState)) × DynState) :=
  (bitsProtocol k).drive absColour fun _ => ()

/-- The output of Absolute-Majority: `some L*`, `L*` the majority bits reported by the copies of
`P₁`, if `P₂` reports colour `1` in the majority; `none` (no absolute majority) otherwise. -/
def absOutput (p : (Label k × (Fin k → StaticState)) × DynState) : Option (Label k) :=
  if p.2.out = 1 then some fun i => decide ((p.1.2 i).out = 1) else none

/-- `L` is an absolute majority colour: more than half of the agents have colour `L`. -/
def IsAbsMajority (x : Label k → ℕ) (L : Label k) : Prop := ∑ L', x L' < 2 * x L

instance (x : Label k → ℕ) : DecidablePred (IsAbsMajority x) :=
  fun L => inferInstanceAs (Decidable (∑ L', x L' < 2 * x L))

/-- The absolute majority colour of the counts `x`, or `none` if there is none. -/
noncomputable def absMajority (x : Label k → ℕ) : Option (Label k) :=
  if h : ∃ L, IsAbsMajority x L then some h.choose else none

/-- There is at most one absolute majority colour, and `absMajority` returns it. -/
theorem absMajority_eq_some_iff (x : Label k → ℕ) (L : Label k) :
    absMajority x = some L ↔ IsAbsMajority x L := by
  have huniq : ∀ L₁ L₂, IsAbsMajority x L₁ → IsAbsMajority x L₂ → L₁ = L₂ := by
    intro L₁ L₂ h₁ h₂
    by_contra hne
    have : x L₁ + x L₂ ≤ ∑ L', x L' := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    unfold IsAbsMajority at h₁ h₂
    omega
  unfold absMajority
  constructor
  · intro h
    split_ifs at h with hex
    · cases h
      exact hex.choose_spec
  · intro hL
    rw [dif_pos ⟨L, hL⟩]
    exact congrArg some (huniq _ _ (Exists.choose_spec ⟨L, hL⟩) hL)

/-- The eventual colour for `P₂` of an agent with label `L`: `1` if `L` agrees with all majority
bits, `-1` otherwise. -/
noncomputable def absTarget (x : Label k → ℕ) (L : Label k) : SignType :=
  if ∀ i, majBit x i = bitSign (L i) then 1 else -1

/-- A sign `±1` squared is `1`. -/
theorem bitSign_mul_mul_bitSign (b : Bool) (a : ℤ) :
    ((bitSign b : SignType) : ℤ) * (a * ((bitSign b : SignType) : ℤ)) = a := by
  cases b <;> simp [bitSign]

/-- A product of two signs `±1` with `a ≥ 0` is at least `-a`. -/
theorem neg_le_bitSign_mul (b c : Bool) {a : ℤ} (ha : 0 ≤ a) :
    -a ≤ ((bitSign b : SignType) : ℤ) * (a * ((bitSign c : SignType) : ℤ)) := by
  cases b <;> cases c <;> simp [bitSign] <;> linarith

/-- If `s * S > 0` for a sign `s = ±1`, then `sign S = s`. -/
theorem sign_eq_bitSign_of_pos (b : Bool) {S : ℤ} (h : 0 < ((bitSign b : SignType) : ℤ) * S) :
    SignType.sign S = bitSign b := by
  cases b <;> simp [bitSign] at h ⊢
  · exact sign_neg h
  · exact sign_pos h

/-- The majority bits of an absolute majority colour are its bits (the proof of
`majBit_eq_of_isAbsMajority`). -/
theorem majBit_eq_bitSign_of_isAbsMajority {x : Label k → ℕ} {L : Label k}
    (h : IsAbsMajority x L) (i : Fin k) : majBit x i = bitSign (L i) := by
  have hn : ((∑ L', x L' : ℕ) : ℤ) < 2 * x L := by exact_mod_cast h
  rw [Nat.cast_sum, ← Finset.add_sum_erase _ _ (mem_univ L)] at hn
  have hrest : -∑ L' ∈ univ.erase L, (x L' : ℤ) ≤ ∑ L' ∈ univ.erase L,
      ((bitSign (L i) : SignType) : ℤ) * ((x L' : ℤ) * ((bitSign (L' i) : SignType) : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun L' _ => neg_le_bitSign_mul _ _ (Nat.cast_nonneg _)
  refine sign_eq_bitSign_of_pos _ ?_
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (mem_univ L), bitSign_mul_mul_bitSign]
  linarith

/-- `bitSign` is injective. -/
theorem bitSign_injective : Function.Injective bitSign := by decide

/-- If `L` matches every majority bit, the `absTarget`-weighted sum is `2 x L - n`. -/
theorem sum_mul_absTarget_of {x : Label k → ℕ} {L : Label k}
    (hL : ∀ i, majBit x i = bitSign (L i)) :
    ∑ L', (x L' : ℤ) * ((absTarget x L' : SignType) : ℤ) = 2 * x L - ∑ L', (x L' : ℤ) := by
  have hterm : ∀ L', (x L' : ℤ) * ((absTarget x L' : SignType) : ℤ) =
      2 * (if L' = L then (x L' : ℤ) else 0) - x L' := by
    intro L'
    by_cases hL' : L' = L
    · subst hL'
      simp [absTarget, hL]
      ring
    · have : ¬∀ i, majBit x i = bitSign (L' i) := fun h' =>
        hL' (funext fun i => bitSign_injective ((h' i).symm.trans (hL i)))
      simp [absTarget, this, hL']
  simp [hterm, Finset.sum_sub_distrib]

/-- **[GHMSS16, proof of Theorem 6]** The final test of `P₂`: the eventual colour sum
`#(L = L*) - #(L ≠ L*)` is positive iff some colour is an absolute majority (it is then `L*`). -/
theorem absTarget_sum_sign_eq_one_iff (x : Label k → ℕ) :
    SignType.sign (∑ L, (x L : ℤ) * ((absTarget x L : SignType) : ℤ)) = 1 ↔
      ∃ L, IsAbsMajority x L := by
  rw [sign_eq_one_iff]
  constructor
  · intro hpos
    by_cases hex : ∃ L : Label k, ∀ i, majBit x i = bitSign (L i)
    · obtain ⟨L, hL⟩ := hex
      rw [sum_mul_absTarget_of hL] at hpos
      refine ⟨L, ?_⟩
      have : ((∑ L', x L' : ℕ) : ℤ) < 2 * x L := by push_cast; linarith
      exact_mod_cast this
    · have hneg : ∀ L, absTarget x L = -1 := fun L => if_neg fun hL => hex ⟨L, hL⟩
      simp [hneg] at hpos
      exact (hpos.not_ge (by positivity)).elim
  · rintro ⟨L, hL⟩
    rw [sum_mul_absTarget_of (majBit_eq_bitSign_of_isAbsMajority hL)]
    have : ((∑ L', x L' : ℕ) : ℤ) < 2 * x L := by exact_mod_cast hL
    push_cast at this
    linarith

/-- **[GHMSS16, proof of Theorem 6]** The majority bits of an absolute majority colour are its
bits. -/
theorem majBit_eq_of_isAbsMajority {x : Label k → ℕ} {L : Label k} (h : IsAbsMajority x L)
    (i : Fin k) : majBit x i = bitSign (L i) := by
  exact majBit_eq_bitSign_of_isAbsMajority h i

/-- **[GHMSS16, Theorem 6]** Algorithm Absolute-Majority stably computes the absolute majority:
all agents eventually and forever output `some L` if more than half of the agents have colour `L`,
and `none` if there is no such colour. -/
theorem absoluteMajority_stablyComputes :
    (absoluteMajority k).StablyComputesWith absOutput absMajority := by
  -- the copies of `P₁` stably mark every agent with the majority bits, its label and its
  -- eventual colour for `P₂`
  have hD : (bitsProtocol k).StablyMarks
      (fun q => (((fun i => (q.2 i).out, q.1) : (Fin k → SignType) × Label k), absColour q))
      fun x L => (((majBit x, L) : (Fin k → SignType) × Label k), absTarget x L) :=
    bitsProtocol_stablyMarks.map fun p => (p, if ∀ i, p.1 i = bitSign (p.2 i) then 1 else -1)
  have h := Protocol.drive_stablyMarks (D := bitsProtocol k) (col := absColour)
    (grp := fun _ => ()) (γ := fun _ => ()) (fun _ _ => ⟨rfl, rfl⟩) (fun _ => rfl) hD
  intro n hn ι c hc
  obtain ⟨d, hd, hs⟩ := h n hn ι c hc
  refine ⟨d, hd, fun f hf v => ?_⟩
  have := hs f hf v
  simp only [Prod.mk.injEq] at this
  obtain ⟨⟨h1, -⟩, h2⟩ := this
  show (if (f v).2.out = 1 then some fun i => decide (((f v).1.2 i).out = 1) else none) =
    absMajority (counts ι).1
  rw [h2, filter_true_of_mem fun _ _ => trivial]
  split_ifs with hpos
  · obtain ⟨L, hL⟩ := (absTarget_sum_sign_eq_one_iff _).1 hpos
    rw [(absMajority_eq_some_iff _ L).2 hL]
    congr 1
    funext i
    rw [congrFun h1 i, majBit_eq_of_isAbsMajority hL]
    cases L i <;> rfl
  · rw [eq_comm, absMajority, dif_neg fun hex => hpos ((absTarget_sum_sign_eq_one_iff _).2 hex)]

/-- **[GHMSS16, Theorem 6, space]** Absolute-Majority has `2^k · 6^k · 8` states (label, `k` states
of `P₁`, one state of `P₂`), at most `2^(4k+3)`: `O(k)` bits. -/
theorem card_absState :
    Fintype.card ((Label k × (Fin k → StaticState)) × DynState) = 2 ^ k * 6 ^ k * 8 ∧
      2 ^ k * 6 ^ k * 8 ≤ 2 ^ (4 * k + 3) := by
  refine ⟨by simp [Fintype.card_prod, card_staticState, card_dynState], ?_⟩
  rw [← mul_pow, pow_succ, pow_succ, pow_succ, pow_mul]
  have : (2 * 6) ^ k ≤ (2 ^ 4) ^ k := Nat.pow_le_pow_left (by norm_num) k
  omega

end Crn
