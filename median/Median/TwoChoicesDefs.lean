import Median.Basic

/-! # The k-party 2-Choices dynamics: definitions

Elsässer, Friedetzky, Kaaser, Mallmann-Trenn and Trinker, *Efficient k-party voting with two
choices* (arXiv:1602.04667; the latest arXiv version, v5, is titled *Rapid asynchronous plurality
consensus*; arXiv v5 numbering), Section 1.1, synchronous model: on the complete graph `K_n`
every node holds one of `k` colours; in each round every node samples two nodes uniformly at
random (independently, with replacement, itself included) and, if the two sampled colours
coincide, adopts that colour; otherwise it keeps its own colour.

Rounds are those of the median dynamics (`Median.Round n`: the two nodes sampled by every node),
so under the uniform distribution on rounds the `2n` samples are independent and uniform. With
two colours the rule is the median of three Booleans (`step_bool`), so the binary results of
`median/` transfer (`run_bool`). With `k ≥ 3` colours it is not the median rule.

The indicator of a colour `i` dominates the binary median process run on the same samples
(`run_dominates`): this is how a configuration in which `i` holds a large majority is finished.
-/

namespace Median.TwoChoices
open Finset Dynamics

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-- The 2-Choices rule: a node with colour `own` that sees the colours `a` and `b` adopts `a` if
`a = b` and keeps `own` otherwise. -/
def rule (own a b : α) : α := if a = b then a else own

/-- One synchronous round of 2-Choices: node `v` applies `rule` to its own colour and the colours
of its two sampled nodes `(r v).1` and `(r v).2`. -/
def step (x : Config n α) (r : Round n) : Config n α :=
  fun v => rule (x v) (x (r v).1) (x (r v).2)

/-- The configuration after a list of rounds (the first round first). -/
def run (x : Config n α) (l : List (Round n)) : Config n α := l.foldl step x

/-- The number `c_i` of nodes holding colour `i`. -/
def count (x : Config n α) (i : α) : ℕ := (univ.filter fun v => x v = i).card

/-- The number of nodes whose two samples both hold colour `i` in round `r`: the only nodes that
can join `i` (Berenbrink et al., arXiv:1702.04921 v1, proof of Theorem 5). -/
def twice (x : Config n α) (r : Round n) (i : α) : ℕ :=
  (univ.filter fun v => x (r v).1 = i ∧ x (r v).2 = i).card

/-- 2-Choices as a Markov kernel on configurations (uniform i.i.d. rounds). -/
noncomputable def kernel (n : ℕ) [NeZero n] (α : Type*) [Fintype α] [DecidableEq α] :
    Kernel (Config n α) :=
  Kernel.ofStep (step (n := n) (α := α))

/-! ### Basic facts -/

/-- A node whose two samples hold different colours keeps its own colour. -/
theorem step_of_ne (x : Config n α) (r : Round n) (v : Fin n) (h : x (r v).1 ≠ x (r v).2) :
    step x r v = x v := by
  simp [step, rule, h]

/-- A node whose two samples hold the same colour adopts it. -/
theorem step_of_eq (x : Config n α) (r : Round n) (v : Fin n) (h : x (r v).1 = x (r v).2) :
    step x r v = x (r v).1 := by
  simp [step, rule, h]

/-- Consensus configurations are fixed points. -/
theorem step_of_consensus (x : Config n α) (h : Consensus x) (r : Round n) : step x r = x := by
  obtain ⟨c, hc⟩ := h
  funext v
  simp [step, rule, hc]

/-- Running from a consensus configuration does not change it. -/
theorem run_of_consensus (x : Config n α) (h : Consensus x) (l : List (Round n)) :
    run x l = x := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    show run (step x r) l = x
    rw [step_of_consensus x h r]
    exact ih

/-- `run` on a nonempty list: the first round first. -/
theorem run_cons (x : Config n α) (r : Round n) (l : List (Round n)) :
    run x (r :: l) = run (step x r) l := rfl

/-- `run` on a concatenation. -/
theorem run_append (x : Config n α) (l₁ l₂ : List (Round n)) :
    run x (l₁ ++ l₂) = run (run x l₁) l₂ := by
  simp [run, List.foldl_append]

/-- A node joins colour `i` only if it holds `i` already or both its samples hold `i`. -/
theorem step_eq_imp (x : Config n α) (r : Round n) (v : Fin n) (i : α) (h : step x r v = i) :
    x v = i ∨ (x (r v).1 = i ∧ x (r v).2 = i) := by
  by_cases hs : x (r v).1 = x (r v).2
  · rw [step_of_eq x r v hs] at h
    exact Or.inr ⟨h, hs ▸ h⟩
  · rw [step_of_ne x r v hs] at h
    exact Or.inl h

/-- **One round can add at most the nodes that see `i` twice**:
`c_i' ≤ c_i + #{v : both samples of v hold i}` (Berenbrink et al., arXiv:1702.04921 v1,
proof of Theorem 5). -/
theorem count_step_le (x : Config n α) (r : Round n) (i : α) :
    count (step x r) i ≤ count x i + twice x r i := by
  unfold count twice
  calc (univ.filter fun v => step x r v = i).card
      ≤ ((univ.filter fun v => x v = i) ∪
          (univ.filter fun v => x (r v).1 = i ∧ x (r v).2 = i)).card := by
        apply card_le_card
        intro v hv
        simp only [mem_filter, mem_univ, true_and, mem_union] at hv ⊢
        exact step_eq_imp x r v i hv
    _ ≤ _ := card_union_le _ _

/-- A colour that nobody holds stays extinct. -/
theorem count_step_eq_zero (x : Config n α) (r : Round n) (i : α) (h : count x i = 0) :
    count (step x r) i = 0 := by
  unfold count at h ⊢
  rw [card_eq_zero, filter_eq_empty_iff] at h ⊢
  intro v _ hv
  rcases step_eq_imp x r v i hv with h1 | ⟨h1, _⟩
  · exact h (mem_univ _) h1
  · exact h (mem_univ _) h1

/-! ### Two colours: the median rule -/

/-- With two colours the 2-Choices rule is the median of three Booleans. -/
theorem rule_bool (own a b : Bool) : rule own a b = med3 own a b := by
  cases own <;> cases a <;> cases b <;> rfl

/-- **Bridge to the median dynamics**: on `Bool`, one 2-Choices round is one round of
`Median.step`, with the same samples. -/
theorem step_bool (x : Config n Bool) (r : Round n) : step x r = Median.step x r := by
  funext v
  exact rule_bool _ _ _

/-- **Bridge to the median dynamics**, any number of rounds. -/
theorem run_bool (x : Config n Bool) (l : List (Round n)) : run x l = Median.run x l := by
  have h : (step : Config n Bool → Round n → Config n Bool) = Median.step := by
    funext x r
    exact step_bool x r
  simp only [run, Median.run, h]

/-- On `Bool`, the count of `true` is `Median.ones`. -/
theorem count_true (x : Config n Bool) : count x true = ones x := rfl

/-- On `Bool`, the counts of `true` and `false` add up to `n`. -/
theorem count_true_add_count_false (x : Config n Bool) : count x true + count x false = n := by
  unfold count
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun v => x v = true)
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at h
  exact h

/-! ### Domination of a colour by the binary median process -/

/-- One round: if every `true` of `y` sits on a node of colour `i`, the same holds after one
median round of `y` and one 2-Choices round of `x` with the same samples. -/
theorem step_dominates (x : Config n α) (i : α) (y : Config n Bool)
    (hy : ∀ v, y v = true → x v = i) (r : Round n) (v : Fin n)
    (h : Median.step y r v = true) : step x r v = i := by
  have h0 := hy v
  have h1 := hy (r v).1
  have h2 := hy (r v).2
  simp only [Median.step] at h
  unfold step rule
  revert h h0 h1 h2
  cases y v <;> cases y (r v).1 <;> cases y (r v).2 <;> simp [med3] <;> intros <;> split_ifs <;>
    simp_all

/-- **Domination by the binary median process**: run the median dynamics on the indicator of
colour `i` and 2-Choices on `x` with the same rounds; every node holding `true` in the first
process holds `i` in the second. The node-wise form of the paper's remark that, once colour `i`
holds a large majority, 2-Choices is dominated by the two-colour process (Elsässer et al.,
proof of Theorem 1.2). -/
theorem run_dominates (x : Config n α) (i : α) (l : List (Round n)) (v : Fin n)
    (h : Median.run (fun u => decide (x u = i)) l v = true) : run x l v = i := by
  suffices H : ∀ (l : List (Round n)) (x : Config n α) (y : Config n Bool),
      (∀ u, y u = true → x u = i) → ∀ v, Median.run y l v = true → run x l v = i by
    exact H l x _ (fun u hu => of_decide_eq_true hu) v h
  intro l
  induction l with
  | nil => intro x y hy v hv; exact hy v hv
  | cons r l ih =>
    intro x y hy v hv
    exact ih (step x r) (Median.step y r) (fun u hu => step_dominates x i y hy r u hu) v hv

end Median.TwoChoices
