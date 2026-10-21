import ThreeMajority.Model
import ThreeMajority.Prob

/-!
# 3-Majority and Voter with any number of colours (roadmap MAJ-6, part (b))

Model of Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn, Natale, *Ignore or Comply? On
breaking symmetry in consensus*, PODC 2017, arXiv:1702.04921 (v1), Section 2.1. Each of `n`
agents holds a colour of an arbitrary type `σ`; the paper's colours `[k] ⊆ [n]` are `σ = Fin n`.

* `majColour c s`: the 3-Majority rule of Section 2.2 on a sample triple `s`. The paper adopts a
  colour supported by at least two samples, and otherwise a uniformly random one of the three
  samples. Here a three-way tie adopts the *first* sample: since the three samples are i.i.d.,
  this has the same law (the process function of Equation (2), `alpha3M_weight`), and it keeps
  the round randomness `Tgt3 n` of this package.
* `stepCol`, `runCol`: one round and a whole trajectory of 3-Majority, on the round type
  `Tgt3 n` of `ThreeMajority.Model`. With two colours this is the package's `step`
  (`stepCol_bool`), so the model is the existing one, extended to any number of colours.
* `voterStep`, `voterRun`: the Voter process (Equation (1)); a round is `Fin n → Fin n`, every
  agent pulling the colour of one uniformly random agent (itself included).
* `colourCount c a`, `numColours c`: the configuration vector of the paper and the number of
  remaining colours.
-/

namespace ThreeMajority

open Finset

variable {n : ℕ} {σ : Type*}

instance [NeZero n] : Nonempty (Tgt3 n) :=
  tgt3_nonempty (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

section Voter

/-- One round of the Voter process (BCEKMN17, Section 2.2, Equation (1)): agent `v` adopts the
colour of agent `y v`. -/
def voterStep (c : Fin n → σ) (y : Fin n → Fin n) : Fin n → σ :=
  fun v => c (y v)

/-- The configuration of the Voter process after consuming a list of rounds. -/
def voterRun (c : Fin n → σ) : List (Fin n → Fin n) → Fin n → σ
  | [] => c
  | y :: l => voterRun (voterStep c y) l

@[simp] lemma voterRun_nil (c : Fin n → σ) : voterRun c [] = c := rfl

@[simp] lemma voterRun_cons (c : Fin n → σ) (y : Fin n → Fin n) (l : List (Fin n → Fin n)) :
    voterRun c (y :: l) = voterRun (voterStep c y) l := rfl

lemma voterRun_eq_foldl (c : Fin n → σ) (l : List (Fin n → Fin n)) :
    voterRun c l = l.foldl voterStep c := by
  induction l generalizing c with
  | nil => rfl
  | cons y l ih => simp [ih]

end Voter

variable [DecidableEq σ]

/-- The 3-Majority update rule on a sample triple `s = (s₁, s₂, s₃)` (BCEKMN17, Section 2.2):
if the second and third samples agree, adopt their colour (a majority); otherwise the first
sample's colour is a majority or all three colours differ, and the first sample's colour is
adopted. -/
def majColour (c : Fin n → σ) (s : Fin n × Fin n × Fin n) : σ :=
  if c s.2.1 = c s.2.2 then c s.2.1 else c s.1

/-- One round of 3-Majority with any number of colours (BCEKMN17, Section 2.2). -/
def stepCol (c : Fin n → σ) (r : Tgt3 n) : Fin n → σ :=
  fun v => majColour c (r v)

/-- The configuration of 3-Majority after consuming a list of rounds. -/
def runCol (c : Fin n → σ) : List (Tgt3 n) → Fin n → σ
  | [] => c
  | r :: l => runCol (stepCol c r) l

/-- The number `c_a` of agents of colour `a`: the configuration vector of BCEKMN17,
Section 2.1. -/
def colourCount (c : Fin n → σ) (a : σ) : ℕ :=
  (univ.filter fun v => c v = a).card

/-- The number of remaining colours of a configuration. Consensus is `numColours c ≤ 1`. -/
def numColours (c : Fin n → σ) : ℕ :=
  (univ.image c).card

@[simp] lemma runCol_nil (c : Fin n → σ) : runCol c [] = c := rfl

@[simp] lemma runCol_cons (c : Fin n → σ) (r : Tgt3 n) (l : List (Tgt3 n)) :
    runCol c (r :: l) = runCol (stepCol c r) l := rfl

lemma runCol_eq_foldl (c : Fin n → σ) (l : List (Tgt3 n)) :
    runCol c l = l.foldl stepCol c := by
  induction l generalizing c with
  | nil => rfl
  | cons r l ih => simp [ih]

lemma runCol_append (c : Fin n → σ) (l₁ l₂ : List (Tgt3 n)) :
    runCol c (l₁ ++ l₂) = runCol (runCol c l₁) l₂ := by
  simp [runCol_eq_foldl, List.foldl_append]

/-- **Bridge to the two-opinion model.** With colours `Bool`, the agents of colour `true` after
one round of `stepCol` are the opinion-`1` set after one round of the package's `step`. -/
theorem stepCol_bool (c : Fin n → Bool) (r : Tgt3 n) :
    univ.filter (fun v => stepCol c r v = true) = step (univ.filter fun v => c v = true) r := by
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_step, sampleCount, sampleCountOf, stepCol,
    majColour]
  rcases r v with ⟨a, b, d⟩
  cases ha : c a <;> cases hb : c b <;> cases hd : c d <;> simp

/-- 3-Majority never creates a colour: the colours after a round are among the current ones. -/
lemma image_stepCol_subset (c : Fin n → σ) (r : Tgt3 n) :
    univ.image (stepCol c r) ⊆ univ.image c := by
  intro a ha
  simp only [mem_image, mem_univ, true_and] at ha ⊢
  obtain ⟨v, rfl⟩ := ha
  unfold stepCol majColour
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

lemma numColours_stepCol_le (c : Fin n → σ) (r : Tgt3 n) :
    numColours (stepCol c r) ≤ numColours c :=
  card_le_card (image_stepCol_subset c r)

/-- The number of colours of 3-Majority never increases along a trajectory; hence the event
"at most `κ` colours at time `T`" is the event "at most `κ` colours by time `T`", and fixed-time
bounds are bounds on the hitting times `T^κ` of the paper. -/
lemma numColours_runCol_append_le (c : Fin n → σ) (l₁ l₂ : List (Tgt3 n)) :
    numColours (runCol c (l₁ ++ l₂)) ≤ numColours (runCol c l₁) := by
  rw [runCol_append]
  induction l₂ generalizing l₁ c with
  | nil => simp
  | cons r l ih =>
    have h := ih (stepCol (runCol c l₁) r) []
    simp only [runCol_nil] at h
    simp only [runCol_cons]
    exact h.trans (numColours_stepCol_le _ r)

lemma numColours_voterStep_le (c : Fin n → σ) (y : Fin n → Fin n) :
    numColours (voterStep c y) ≤ numColours c := by
  apply card_le_card
  intro a ha
  simp only [mem_image, mem_univ, true_and, voterStep] at ha ⊢
  obtain ⟨v, rfl⟩ := ha
  exact ⟨_, rfl⟩

end ThreeMajority
