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

/-- **[GHMSS16, Section 4]** The `k` copies of `P₁` stably compute the `k` majority bits, and
every agent keeps its label. -/
theorem bitsProtocol_stablyMarks :
    (bitsProtocol k).StablyMarks (fun q => (fun i => (q.2 i).out, q.1))
      fun x L => (majBit x, L) := by
  sorry

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

/-- **[GHMSS16, proof of Theorem 6]** The final test of `P₂`: the eventual colour sum
`#(L = L*) - #(L ≠ L*)` is positive iff some colour is an absolute majority (it is then `L*`). -/
theorem absTarget_sum_sign_eq_one_iff (x : Label k → ℕ) :
    SignType.sign (∑ L, (x L : ℤ) * ((absTarget x L : SignType) : ℤ)) = 1 ↔
      ∃ L, IsAbsMajority x L := by
  sorry

/-- **[GHMSS16, proof of Theorem 6]** The majority bits of an absolute majority colour are its
bits. -/
theorem majBit_eq_of_isAbsMajority {x : Label k → ℕ} {L : Label k} (h : IsAbsMajority x L)
    (i : Fin k) : majBit x i = bitSign (L i) := by
  sorry

/-- **[GHMSS16, Theorem 6]** Algorithm Absolute-Majority stably computes the absolute majority:
all agents eventually and forever output `some L` if more than half of the agents have colour `L`,
and `none` if there is no such colour. -/
theorem absoluteMajority_stablyComputes :
    (absoluteMajority k).StablyComputesWith absOutput absMajority := by
  sorry

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
