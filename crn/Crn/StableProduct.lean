import Crn.StableInteract

/-!
# Parallel composition of population protocols (CRN-3)

The protocol of the proof of [AADFP06, Lemma 3]: states `Q₁ × Q₂`, input `s ↦ (I₁ s, I₂ s)`,
both components make their own transition in every encounter, and the output of `(p₁, p₂)` is
`ξ(O₁ p₁, O₂ p₂)`. Every path of the composition projects to paths of both components
(`reaches_fst`, `reaches_snd`), and a path of one component lifts to a path of the composition,
along which the other component follows a path of its own (`lift_fst`, `lift_snd`). Hence
(`prod_stablyComputes`): run the first component to an output-stable configuration, then the
second; the first stays output-stable.
-/

namespace Crn

variable {X Q₁ Q₂ : Type*} {n : ℕ}

namespace Protocol

/-- Parallel composition of two protocols with output `ξ(O₁, O₂)` [AADFP06, proof of
Lemma 3]. -/
def prod (P₁ : Protocol X Q₁) (P₂ : Protocol X Q₂) (ξ : Bool → Bool → Bool) :
    Protocol X (Q₁ × Q₂) where
  input i := (P₁.input i, P₂.input i)
  output p := ξ (P₁.output p.1) (P₂.output p.2)
  δ pq := (((P₁.δ (pq.1.1, pq.2.1)).1, (P₂.δ (pq.1.2, pq.2.2)).1),
    ((P₁.δ (pq.1.1, pq.2.1)).2, (P₂.δ (pq.1.2, pq.2.2)).2))

variable {P₁ : Protocol X Q₁} {P₂ : Protocol X Q₂} {ξ : Bool → Bool → Bool}

/-- The first component of an encounter of the composition is an encounter of `P₁`. -/
lemma prod_interact_fst (c : Fin n → Q₁ × Q₂) (e : AgentPair n) :
    (fun w => ((P₁.prod P₂ ξ).interact c e w).1) = P₁.interact (fun w => (c w).1) e := by
  funext w
  rw [interact_apply, interact_apply]
  split_ifs <;> rfl

/-- The second component of an encounter of the composition is an encounter of `P₂`. -/
lemma prod_interact_snd (c : Fin n → Q₁ × Q₂) (e : AgentPair n) :
    (fun w => ((P₁.prod P₂ ξ).interact c e w).2) = P₂.interact (fun w => (c w).2) e := by
  funext w
  rw [interact_apply, interact_apply]
  split_ifs <;> rfl

/-- Paths of the composition project to paths of the first component. -/
lemma reaches_fst {c d : Fin n → Q₁ × Q₂} (h : (P₁.prod P₂ ξ).Reaches c d) :
    P₁.Reaches (fun w => (c w).1) (fun w => (d w).1) := by
  induction h with
  | refl => exact Reaches.refl _
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rw [prod_interact_fst]
    exact ih.trans (reaches_interact _ e)

/-- Paths of the composition project to paths of the second component. -/
lemma reaches_snd {c d : Fin n → Q₁ × Q₂} (h : (P₁.prod P₂ ξ).Reaches c d) :
    P₂.Reaches (fun w => (c w).2) (fun w => (d w).2) := by
  induction h with
  | refl => exact Reaches.refl _
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rw [prod_interact_snd]
    exact ih.trans (reaches_interact _ e)

/-- A path of the first component lifts to the composition (same encounters); the second
component follows a path of `P₂`. -/
lemma lift_fst {c₁ d₁ : Fin n → Q₁} (h : P₁.Reaches c₁ d₁) (c : Fin n → Q₁ × Q₂)
    (hc : (fun w => (c w).1) = c₁) :
    ∃ d, (P₁.prod P₂ ξ).Reaches c d ∧ (fun w => (d w).1) = d₁ ∧
      P₂.Reaches (fun w => (c w).2) (fun w => (d w).2) := by
  induction h with
  | refl => exact ⟨c, Reaches.refl _, hc, Reaches.refl _⟩
  | tail _ hst ih =>
    obtain ⟨d, hd, hd1, hd2⟩ := ih
    obtain ⟨e, rfl⟩ := hst
    refine ⟨(P₁.prod P₂ ξ).interact d e, hd.trans (reaches_interact _ e), ?_, ?_⟩
    · rw [prod_interact_fst, hd1]
    · rw [prod_interact_snd]
      exact hd2.trans (reaches_interact _ e)

/-- A path of the second component lifts to the composition (same encounters); the first
component follows a path of `P₁`. -/
lemma lift_snd {c₂ d₂ : Fin n → Q₂} (h : P₂.Reaches c₂ d₂) (c : Fin n → Q₁ × Q₂)
    (hc : (fun w => (c w).2) = c₂) :
    ∃ d, (P₁.prod P₂ ξ).Reaches c d ∧ (fun w => (d w).2) = d₂ ∧
      P₁.Reaches (fun w => (c w).1) (fun w => (d w).1) := by
  induction h with
  | refl => exact ⟨c, Reaches.refl _, hc, Reaches.refl _⟩
  | tail _ hst ih =>
    obtain ⟨d, hd, hd2, hd1⟩ := ih
    obtain ⟨e, rfl⟩ := hst
    refine ⟨(P₁.prod P₂ ξ).interact d e, hd.trans (reaches_interact _ e), ?_, ?_⟩
    · rw [prod_interact_snd, hd2]
    · rw [prod_interact_fst]
      exact hd1.trans (reaches_interact _ e)

/-- **[AADFP06, Lemma 3]** The parallel composition of protocols stably computing `φ` and `ψ`
stably computes `ξ(φ, ψ)`. -/
theorem prod_stablyComputes [Fintype X] [DecidableEq X] {φ ψ : (X → ℕ) → Bool}
    (h₁ : P₁.StablyComputes φ) (h₂ : P₂.StablyComputes ψ) :
    (P₁.prod P₂ ξ).StablyComputes fun x => ξ (φ x) (ψ x) := by
  intro n hn ι c hc
  obtain ⟨d₁, hd₁, hs₁⟩ := h₁ n hn ι _ (reaches_fst hc)
  obtain ⟨c', hc', hc'1, hc'2⟩ := lift_fst (P₂ := P₂) (ξ := ξ) hd₁ c rfl
  obtain ⟨d₂, hd₂, hs₂⟩ := h₂ n hn ι _ ((reaches_snd hc).trans hc'2)
  obtain ⟨d, hd, hd2, hd1⟩ := lift_snd (P₁ := P₁) (ξ := ξ) hd₂ c' rfl
  refine ⟨d, hc'.trans hd, fun e he w => ?_⟩
  have e1 : P₁.Reaches d₁ (fun w => (e w).1) := hc'1 ▸ hd1.trans (reaches_fst he)
  have e2 : P₂.Reaches d₂ (fun w => (e w).2) := hd2 ▸ reaches_snd he
  have o1 := hs₁ _ e1 w
  have o2 := hs₂ _ e2 w
  change ξ (P₁.output (e w).1) (P₂.output (e w).2) = _
  rw [o1, o2]

end Protocol

end Crn
