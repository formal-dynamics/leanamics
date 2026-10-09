import Median.Expander

/-! # Two-sample voting on expanders with a small imbalance: definitions

Cooper, Elsässer and Radzik, *The power of two choices in distributed voting* (ICALP 2014,
arXiv:1404.7479), Theorem 2 and its Phase I (Lemma 2 and Corollary 2). Lemma, corollary and
equation names follow the arXiv version. The model is the one of `Median.Expander`: the round
`graphStep` on a `d`-regular graph, the minority `minority a x` (the set `B` of vertices whose
opinion differs from `a`) and the spectral quantity `lambdaG`.

* `majority a x`: the size of `A`, the set of vertices holding `a`.
* `imbalance a x`: the paper's `ν = (A − B) / n`.
* `phaseEta α a x`: the paper's `η = α n / √(A B)` in the proof of Lemma 2.
* `gainCount a x y` and `lossCount a x y`: the paper's `Δ_{BA}` (vertices of `B` converting to
  `a`) and `Δ_{AB}` (vertices of `A` converting away from `a`) between `x` and `y`.
* `MixingProp G d α c`: the hypothesis (mixing-prop) of Lemma 2, the mixing inequality
  `|E(X, Y) − d X Y / n| ≤ α d √(X Y)` for disjoint `X`, `Y` with `Y ≥ c n` and
  `X ≥ (2/3) α c^{3/2} n`. By the expander mixing lemma it holds whenever `λ_G ≤ α`
  (`mixingProp_of_lambdaG`).
* `phaseIRounds ν c`: the length `⌈log_{5/4} (1/(2ν))⌉ + ⌈log_{4/3} (1/(4c))⌉` of Phase I in
  the proof of Lemma 2.
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of vertices holding opinion `a` (the paper's `A`, when `a` is the majority). -/
def majority (a : Bool) (x : V → Bool) : ℕ := (univ.filter fun v => x v = a).card

omit [DecidableEq V] in
/-- `A + B = n`. -/
theorem majority_add_minority (a : Bool) (x : V → Bool) :
    majority a x + minority a x = Fintype.card V := by
  unfold majority minority
  exact Finset.card_filter_add_card_filter_not (s := univ) (fun v => x v = a)

/-- The imbalance `ν = (A − B) / n` of the configuration `x` in favour of `a`. -/
noncomputable def imbalance (a : Bool) (x : V → Bool) : ℝ :=
  ((majority a x : ℝ) - minority a x) / Fintype.card V

/-- The quantity `η = α n / √(A B)` of the proof of Lemma 2. -/
noncomputable def phaseEta (α : ℝ) (a : Bool) (x : V → Bool) : ℝ :=
  α * Fintype.card V / √((majority a x : ℝ) * minority a x)

/-- `Δ_{BA}`: the number of vertices whose opinion differs from `a` in `x` and is `a` in `y`. -/
def gainCount (a : Bool) (x y : V → Bool) : ℕ :=
  (univ.filter fun v => x v ≠ a ∧ y v = a).card

/-- `Δ_{AB}`: the number of vertices whose opinion is `a` in `x` and differs from `a` in `y`. -/
def lossCount (a : Bool) (x y : V → Bool) : ℕ :=
  (univ.filter fun v => x v = a ∧ y v ≠ a).card

omit [DecidableEq V] in
/-- The minority changes by `Δ_{AB} − Δ_{BA}`: `B' + Δ_{BA} = B + Δ_{AB}`. -/
theorem minority_add_gainCount (a : Bool) (x y : V → Bool) :
    minority a y + gainCount a x y = minority a x + lossCount a x y := by
  unfold minority gainCount lossCount
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hx : x v = a <;> by_cases hy : y v = a <;> simp [hx, hy]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The hypothesis (mixing-prop) of the paper's Lemma 2: for all disjoint vertex sets `X` and
`Y` with `|Y| ≥ c n` and `|X| ≥ (2/3) α c^{3/2} n`,
`|E(X, Y) − d |X| |Y| / n| ≤ α d √(|X| |Y|)`. -/
def MixingProp (d : ℕ) (α c : ℝ) : Prop :=
  ∀ X Y : Finset V, Disjoint X Y → c * Fintype.card V ≤ Y.card →
    2 / 3 * α * (c * √c) * Fintype.card V ≤ X.card →
      |(edgeCount G X Y : ℝ) - d * X.card * Y.card / Fintype.card V|
        ≤ α * d * √((X.card : ℝ) * Y.card)

/-- By the expander mixing lemma (the paper's Lemma 3), a `d`-regular graph with `λ_G ≤ α`
satisfies the hypothesis (mixing-prop) of Lemma 2, for every `c`. -/
theorem mixingProp_of_lambdaG {d : ℕ} (hreg : G.IsRegularOfDegree d) {α : ℝ}
    (hα : lambdaG G d ≤ α) (c : ℝ) : MixingProp G d α c := by
  intro X Y _ _ _
  refine (expander_mixing G hreg X Y).trans ?_
  have h0 : 0 ≤ (d : ℝ) * √((X.card : ℝ) * Y.card) := by positivity
  have := mul_le_mul_of_nonneg_right hα h0
  calc lambdaG G d * d * √((X.card : ℝ) * Y.card)
      = lambdaG G d * (d * √((X.card : ℝ) * Y.card)) := by ring
    _ ≤ α * (d * √((X.card : ℝ) * Y.card)) := this
    _ = α * d * √((X.card : ℝ) * Y.card) := by ring

/-- The number of rounds of Phase I in the proof of Lemma 2: at most `⌈log_{5/4} (1/(2ν))⌉`
rounds bring the imbalance from `ν` to `1/2`, and `⌈log_{4/3} (1/(4c))⌉` more bring it from
`1/2` to `1 − 2c`. -/
noncomputable def phaseIRounds (ν c : ℝ) : ℕ :=
  ⌈log (1 / (2 * ν)) / log (5 / 4)⌉₊ + ⌈log (1 / (4 * c)) / log (4 / 3)⌉₊

/-! ### Defining equations

The theorems `*_spec` below restate the definitions used by the statements of Theorem 2 (the new
ones above and those of `Median.ExpanderDefs` and `Median.Defs`). They are proved by `rfl` and
pinned together with the statements, so that the definitions cannot change. -/

section Spec

omit [DecidableEq V] in
/-- Defining equation of `majority` (the paper's `A`). -/
theorem majority_spec (a : Bool) (x : V → Bool) :
    majority a x = (univ.filter fun v => x v = a).card := rfl

omit [DecidableEq V] in
/-- Defining equation of `minority` (the paper's `B`). -/
theorem minority_spec (a : Bool) (x : V → Bool) :
    minority a x = (univ.filter fun v => x v ≠ a).card := rfl

omit [DecidableEq V] in
/-- Defining equation of `imbalance` (the paper's `ν = (A − B)/n`). -/
theorem imbalance_spec (a : Bool) (x : V → Bool) :
    imbalance a x = ((majority a x : ℝ) - minority a x) / Fintype.card V := rfl

omit [DecidableEq V] in
/-- Defining equation of `phaseEta` (the paper's `η = α n / √(A B)` in the proof of Lemma 2). -/
theorem phaseEta_spec (α : ℝ) (a : Bool) (x : V → Bool) :
    phaseEta α a x = α * Fintype.card V / √((majority a x : ℝ) * minority a x) := rfl

omit [DecidableEq V] in
/-- Defining equation of `gainCount` (the paper's `Δ_{BA}`). -/
theorem gainCount_spec (a : Bool) (x y : V → Bool) :
    gainCount a x y = (univ.filter fun v => x v ≠ a ∧ y v = a).card := rfl

omit [DecidableEq V] in
/-- Defining equation of `lossCount` (the paper's `Δ_{AB}`). -/
theorem lossCount_spec (a : Bool) (x y : V → Bool) :
    lossCount a x y = (univ.filter fun v => x v = a ∧ y v ≠ a).card := rfl

/-- Defining equation of `phaseIRounds` (the length of Phase I in the proof of Lemma 2). -/
theorem phaseIRounds_spec (ν c : ℝ) :
    phaseIRounds ν c = ⌈log (1 / (2 * ν)) / log (5 / 4)⌉₊ + ⌈log (1 / (4 * c)) / log (4 / 3)⌉₊ :=
  rfl

/-- Defining equation of `med3`, the median of three values. -/
theorem med3_spec {β : Type*} [LinearOrder β] (u v w : β) :
    med3 u v w = max (min u v) (min (max u v) w) := rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Defining equation of `MixingProp` (the hypothesis (mixing-prop) of Lemma 2). -/
theorem mixingProp_spec (d : ℕ) (α c : ℝ) :
    MixingProp G d α c ↔ ∀ X Y : Finset V, Disjoint X Y → c * Fintype.card V ≤ Y.card →
      2 / 3 * α * (c * √c) * Fintype.card V ≤ X.card →
        |(edgeCount G X Y : ℝ) - d * X.card * Y.card / Fintype.card V|
          ≤ α * d * √((X.card : ℝ) * Y.card) := Iff.rfl

/-- Defining equation of `edgeCount` (the paper's `E(S, T)`, ordered pairs). -/
theorem edgeCount_spec (S T : Finset V) :
    edgeCount G S T = ∑ u ∈ S, (G.neighborFinset u ∩ T).card := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A round of two-sample voting is a pair of neighbour choices per vertex. -/
theorem graphRound_spec : GraphRound G = (NeighborRound G × NeighborRound G) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Defining equation of `graphStep` (one round of two-sample voting, written with `med3`). -/
theorem graphStep_spec (x : V → Bool) (r : GraphRound G) :
    graphStep G x r = fun v => med3 (x v) (x (r.1 v)) (x (r.2 v)) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Defining equation of `graphRun` (the rounds of the list, the first round first). -/
theorem graphRun_spec (x : V → Bool) (l : List (GraphRound G)) :
    graphRun G x l = l.foldl (graphStep G) x := rfl

omit [Fintype V] [DecidableEq V] in
/-- Defining equation of `transitionMatrix` (`P = A / d`). -/
theorem transitionMatrix_spec (d : ℕ) : transitionMatrix G d = (d : ℝ)⁻¹ • G.adjMatrix ℝ := rfl

/-- Defining equation of `walkEigenvalues` (the eigenvalues of `P` in non-increasing order). -/
theorem walkEigenvalues_spec (d : ℕ) :
    walkEigenvalues G d = (transitionMatrix_isHermitian G d).eigenvalues₀ := rfl

/-- Defining equation of `lambdaG` (`λ_G = max {λ₂, |λₙ|}`, the paper's Lemma 3 and Theorem 2). -/
theorem lambdaG_spec (d : ℕ) :
    lambdaG G d = if h : 2 ≤ Fintype.card V then
      max (walkEigenvalues G d ⟨1, by omega⟩) |walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩|
    else 0 := rfl

end Spec

end Median.ExpanderGeneral
