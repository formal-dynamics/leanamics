import Crn.ExactMajorityOutput

/-!
# Static exact majority with ties (CRN-5, [GHMSS16, Section 2])

The protocol `P₁` of [GHMSS16, Section 2] (the majority protocol of [AADFP06], reporting ties).
Every agent has a colour in `{-1, 0, 1}` (`SignType`); the protocol decides the sign of the sum of
the colours, i.e. whether there are more `1`s than `-1`s, fewer, or as many. The six states are
the strong states `[x]` and the weak states `⟨x⟩`, `x ∈ {-1, 0, 1}`, with weight `w([x]) = x`,
`w(⟨x⟩) = 0` (Fig. 1). Transitions (Fig. 2): `[1]` and `[-1]` annihilate into `[0], [0]`; a strong
`[x]` turns a weak state into `⟨x⟩`, and a strong `[x]`, `x ≠ 0`, turns `[0]` into `⟨x⟩`; other
encounters change nothing. The table of Fig. 2 agrees with these rules (checked exhaustively).

Main statements:
* `StaticState.weight_sum_eq` (Lemma 1): the weight sum equals the colour sum.
* `StaticState.absWeight_sum_step_le`, `StaticState.exists_reaches_absWeight_sum_eq` (Lemma 2):
  `R = ∑ |w|` does not increase and can be brought down to `|∑ colours|`.
* `staticMajority_stablyComputes` (Theorem 3): the protocol stably computes the sign of
  `#1 - #(-1)`.
-/

namespace Crn

open Finset

/-- The six states of the static majority protocol [GHMSS16, Fig. 1]: strong `[x]` and weak
`⟨x⟩` for `x ∈ {-1, 0, 1}`. -/
inductive StaticState
  /-- The strong state `[x]`. -/
  | strong (x : SignType)
  /-- The weak state `⟨x⟩`. -/
  | weak (x : SignType)
  deriving DecidableEq, Fintype

namespace StaticState

/-- The weight [GHMSS16, Fig. 1]: `w([x]) = x`, `w(⟨x⟩) = 0`. -/
def weight : StaticState → ℤ
  | strong x => x
  | weak _ => 0

/-- The output (the reported sign of the colour sum): `x` in `[x]` and in `⟨x⟩`. -/
def out : StaticState → SignType
  | strong x => x
  | weak x => x

/-- The new state of an agent in state `a` meeting an agent in state `b`, outside annihilations
[GHMSS16, Section 2]: a weak state meeting `[y]` becomes `⟨y⟩`; `[0]` meeting `[y]`, `y ≠ 0`,
becomes `⟨y⟩`; otherwise nothing changes. -/
def recruit : StaticState → StaticState → StaticState
  | weak _, strong y => weak y
  | strong 0, strong y => if y = 0 then strong 0 else weak y
  | a, _ => a

/-- The transition function of [GHMSS16, Fig. 2]: `[1]` and `[-1]` annihilate into `[0], [0]`,
all other encounters recruit (`recruit`). -/
def δ : StaticState × StaticState → StaticState × StaticState
  | (strong 1, strong (-1)) => (strong 0, strong 0)
  | (strong (-1), strong 1) => (strong 0, strong 0)
  | (a, b) => (recruit a b, recruit b a)

end StaticState

/-- The static majority protocol `P₁` [GHMSS16, Section 2]: input colour `x ↦ [x]`. Its `Bool`
output (more `1`s than `-1`s) is not used; the outputs are `StaticState.out`. -/
def staticMajority : Protocol SignType StaticState where
  input := StaticState.strong
  output s := decide (s.out = 1)
  δ := StaticState.δ

/-- Six states. -/
theorem card_staticState : Fintype.card StaticState = 6 := rfl

namespace StaticState

variable {n : ℕ}

/-- Transitions preserve the total weight of the two agents [GHMSS16, proof of Lemma 1]. -/
theorem δ_weight (a b : StaticState) :
    (δ (a, b)).1.weight + (δ (a, b)).2.weight = a.weight + b.weight := by
  revert a b; decide

/-- **[GHMSS16, Lemma 1]** (Invariant 1). Along every execution, the sum of the weights equals the
sum of the input colours. -/
theorem weight_sum_eq {ι : Fin n → SignType} {c : Fin n → StaticState}
    (h : staticMajority.Reaches (staticMajority.input ∘ ι) c) :
    ∑ v, (c v).weight = ∑ v, ((ι v : SignType) : ℤ) := by
  sorry

/-- **[GHMSS16, Lemma 2]**, first part (Invariant 2). `R = ∑ |w|` does not increase along a step. -/
theorem absWeight_sum_step_le {c d : Fin n → StaticState} (h : staticMajority.Step c d) :
    ∑ v, |(d v).weight| ≤ ∑ v, |(c v).weight| := by
  sorry

/-- **[GHMSS16, Lemma 2]**, second part. From every reachable configuration, a configuration with
`R = |S|` is reachable, `S` the sum of the input colours. -/
theorem exists_reaches_absWeight_sum_eq {ι : Fin n → SignType} {c : Fin n → StaticState}
    (h : staticMajority.Reaches (staticMajority.input ∘ ι) c) :
    ∃ d, staticMajority.Reaches c d ∧ ∑ v, |(d v).weight| = |∑ v, ((ι v : SignType) : ℤ)| := by
  sorry

end StaticState

/-- **[GHMSS16, Theorem 3]** The static majority protocol stably computes the sign of
`#1 - #(-1)`: all agents eventually and forever output `1` if there are more `1`s than `-1`s,
`-1` if fewer, and `0` (a tie) if as many. -/
theorem staticMajority_stablyComputes :
    staticMajority.StablyComputesWith StaticState.out
      fun x => SignType.sign ((x 1 : ℤ) - x (-1)) := by
  sorry

end Crn
