import Median.Defs

/-! # The median dynamics against an adaptive adversary: definitions

Doerr, Goldberg, Minder, Sauerwald and Scheideler (*Stabilizing consensus with the power of two
choices*) let a `T`-bounded adversary, who knows the entire history of the process, change the
values of up to `T` nodes in every round, using only values from the initial configuration. Exact
consensus can then no longer be reached; the goal is *almost stable consensus*: from some round
on, all but `O(T)` nodes agree on a common value.

The adversary is modelled inside the finite layer, without enlarging the state of a Markov
kernel: the randomness of `T` rounds is still a list of `T` independent uniform rounds (the
expectation `expList`), and the adversary is a function of the rounds played so far. Since the
initial configuration is fixed, those rounds determine the whole history of the process, so this
is the most general deterministic adaptive adversary. (A randomized adversary is a mixture of
deterministic ones, so worst-case bounds over deterministic adversaries cover it.)

* `Adversary n α`: `A h z` is the configuration that the adversary makes out of the output `z` of
  the median rule in the current round, knowing the rounds `h` played so far (the current one
  last); `Adversary.Bounded F` says it recolours at most `F` nodes (`hammingDist`), and
  `Adversary.UsesValues S` that it only writes values from `S`;
* `runAdv A x l`: the configuration after the rounds `l` (first round first), each round being
  the median rule followed by the adversary;
* `IsAdvRun F x P`: the same notion without naming the adversary: `P l` is any function of the
  rounds `l` that starts at `x` and, after each round, differs from the output of the median rule
  in at most `F` nodes (`runAdv_isAdvRun`);
* `AlmostConsensus K b y`: at most `K` nodes of `y` hold a value other than `b`;
  `notAlmostStable K T₀ H P l` is the indicator that no single value `b` is held by all but `K`
  nodes at every time `t` with `T₀ ≤ t ≤ T₀ + H`.
-/

namespace Median
open Finset Dynamics

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- An **adaptive adversary**: `A h z` is the configuration that the adversary makes out of the
output `z` of the median rule in the current round, knowing the rounds `h` played so far (oldest
first, the current round last). -/
abbrev Adversary (n : ℕ) (α : Type*) := List (Round n) → Config n α → Config n α

/-- The adversary recolours at most `F` nodes per round. -/
def Adversary.Bounded (F : ℕ) (A : Adversary n α) : Prop :=
  ∀ h z, hammingDist (A h z) z ≤ F

/-- The adversary only writes values from `S` (the paper: values of the initial configuration). -/
def Adversary.UsesValues (S : Set α) (A : Adversary n α) : Prop :=
  ∀ h z v, A h z v ≠ z v → A h z v ∈ S

/-- The median dynamics against the adversary `A`, from `x`, along the rounds `l` (first round
first): every round applies the median rule, then lets the adversary act. -/
def runAdv : Adversary n α → Config n α → List (Round n) → Config n α
  | _, x, [] => x
  | A, x, r :: l => runAdv (fun h => A (r :: h)) (A [r] (step x r)) l

/-- `P` is a run of the median rule from `x` against an adversary recolouring at most `F` nodes
per round: `P l` is the configuration after the rounds `l`, any function of `l`, and after each
round it differs from the output of the median rule in at most `F` nodes. -/
def IsAdvRun (F : ℕ) (x : Config n α) (P : List (Round n) → Config n α) : Prop :=
  P [] = x ∧ ∀ l r, hammingDist (P (l ++ [r])) (step (P l) r) ≤ F

/-- **Almost consensus**: at most `K` nodes hold a value other than `b`. -/
def AlmostConsensus (K : ℝ) (b : α) (y : Config n α) : Prop :=
  ((univ.filter fun v => y v ≠ b).card : ℝ) ≤ K

/-- Indicator of failing **almost stable consensus** along the rounds `l`: there is no value `b`
held by all but at most `K` nodes of `P (l.take t)` at every time `t` with `T₀ ≤ t ≤ T₀ + H`. -/
noncomputable def notAlmostStable (K : ℝ) (T₀ H : ℕ) (P : List (Round n) → Config n α)
    (l : List (Round n)) : ℝ := by
  classical
  exact if ∃ b : α, ∀ t, T₀ ≤ t → t ≤ T₀ + H → AlmostConsensus K b (P (l.take t)) then 0 else 1

end Median
