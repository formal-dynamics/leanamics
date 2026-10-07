import Crn.Basic
import Crn.StableInteract

/-!
# From population protocols to CRNs: helper lemmas (CRN-3)

* The reaction of a transition, `p + q → δ₁(p, q) + δ₂(p, q)` (`Protocol.reactionOf`), and the
  effect of an encounter on count vectors (`counts_interact`): the counts change exactly as by
  this reaction, which is applicable (`consumed_le_counts`); a transition that does not change
  the multiset of states does not change the counts (`counts_interact_of_trivial`).
* Conversely, a reaction with reactants `s(p, q)` applicable at the counts of a configuration
  comes from an encounter of two distinct agents in states `p`, `q` (`exists_agentPair`).
* Input tagging (`Protocol.tagInputs`): a protocol with one fresh state per input symbol, so that
  its input map is injective, which simulates the original protocol (`tagInputs_stablyComputes`).
-/

namespace Crn

open Finset

variable {X Q : Type*} {n : ℕ}

/-! ### Multiplicities -/

/-- Multiplicity of `a` in `s(A, B)`, in the form `[A = a] + [B = a]`. -/
lemma count_mk [DecidableEq Q] (A B a : Q) :
    (s(A, B) : Sym2 Q).toMultiset.count a =
      (if A = a then 1 else 0) + (if B = a then 1 else 0) := by
  rw [Reaction.count_toMultiset_mk]
  by_cases hA : A = a <;> by_cases hB : B = a <;> simp [hA, hB, eq_comm]

/-! ### The reaction of a transition -/

/-- The reaction `p + q → δ₁(p, q) + δ₂(p, q)` of the transition `δ(p, q)`. -/
def Protocol.reactionOf (P : Protocol X Q) (p q : Q) : Reaction Q :=
  ⟨s(p, q), s((P.δ (p, q)).1, (P.δ (p, q)).2)⟩

variable [Fintype Q] [DecidableEq Q]

/-- The counts after an encounter, as an identity in `ℕ`:
`counts' + consumed = counts + produced`. -/
lemma counts_interact_add (P : Protocol X Q) (c : Fin n → Q) (e : AgentPair n) (a : Q) :
    (counts (P.interact c e)).1 a + (P.reactionOf (c e.1.1) (c e.1.2)).consumed a =
      (counts c).1 a + (P.reactionOf (c e.1.1) (c e.1.2)).produced a := by
  have h := sum_add_pair e.2 (fun w => if c w = a then 1 else 0)
    (fun w => if P.interact c e w = a then 1 else 0)
    (fun w h1 h2 => by simp only [P.interact_of_ne c e h1 h2])
  simp only [P.interact_fst, P.interact_snd] at h
  simp only [counts_val, card_filter, Reaction.consumed, Reaction.produced, Protocol.reactionOf,
    count_mk]
  exact h

/-- The reactants of the transition at an encounter are present. -/
lemma consumed_le_counts (P : Protocol X Q) (c : Fin n → Q) (e : AgentPair n) (a : Q) :
    (P.reactionOf (c e.1.1) (c e.1.2)).consumed a ≤ (counts c).1 a := by
  simp only [counts_val, card_filter, Reaction.consumed, Protocol.reactionOf, count_mk]
  exact add_le_sum_pair (G := fun w => if c w = a then 1 else 0) e.2

/-- An encounter changes the counts as the reaction of its transition. -/
lemma counts_interact (P : Protocol X Q) (c : Fin n → Q) (e : AgentPair n) :
    counts (P.interact c e) = (counts c).react (P.reactionOf (c e.1.1) (c e.1.2)) := by
  refine Subtype.ext (funext fun a => ?_)
  rw [Counts.react_val (consumed_le_counts P c e)]
  have h1 := counts_interact_add P c e a
  have h2 := consumed_le_counts P c e a
  omega

/-- An encounter whose transition does not change the multiset of states does not change the
counts. -/
lemma counts_interact_of_trivial (P : Protocol X Q) (c : Fin n → Q) (e : AgentPair n)
    (h : (P.reactionOf (c e.1.1) (c e.1.2)).reactants =
      (P.reactionOf (c e.1.1) (c e.1.2)).products) :
    counts (P.interact c e) = counts c := by
  refine Subtype.ext (funext fun a => ?_)
  have h1 := counts_interact_add P c e a
  rw [Reaction.consumed, Reaction.produced, h] at h1
  omega

/-- A reaction with reactants `s(p, q)` whose reactants are present comes from an encounter of
two distinct agents in states `p` and `q`. -/
lemma exists_agentPair (c : Fin n → Q) {p q : Q}
    (h : ∀ a, (s(p, q) : Sym2 Q).toMultiset.count a ≤ (counts c).1 a) :
    ∃ e : AgentPair n, c e.1.1 = p ∧ c e.1.2 = q := by
  by_cases hpq : p = q
  · subst hpq
    have h2 := h p
    simp only [count_mk, if_true, counts_val] at h2
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.1 (by omega : 1 < #{w | c w = p})
    exact ⟨⟨(u, v), huv⟩, (mem_filter.1 hu).2, (mem_filter.1 hv).2⟩
  · have hp := h p
    have hq := h q
    simp only [count_mk, if_true, counts_val, hpq, Ne.symm hpq, if_false] at hp hq
    obtain ⟨u, hu⟩ := card_pos.1 (by omega : 0 < #{w | c w = p})
    obtain ⟨v, hv⟩ := card_pos.1 (by omega : 0 < #{w | c w = q})
    have hu' := (mem_filter.1 hu).2
    have hv' := (mem_filter.1 hv).2
    have huv : u ≠ v := fun h' => hpq (by rw [← hu', ← hv', h'])
    exact ⟨⟨(u, v), huv⟩, hu', hv'⟩

/-! ### Input tagging -/

omit [Fintype Q] [DecidableEq Q]

/-- The state of the original protocol represented by a state of `P.tagInputs eX`. -/
def Protocol.untag (P : Protocol X Q) {k : ℕ} (eX : X ≃ Fin k) : Fin k ⊕ Q → Q :=
  Sum.elim (fun j => P.input (eX.symm j)) id

/-- `P` with one fresh state `inl j` per input symbol: input `i` starts in `inl (eX i)`, which
behaves as `P.input i`; every encounter moves both agents to `inr`-states. -/
def Protocol.tagInputs (P : Protocol X Q) {k : ℕ} (eX : X ≃ Fin k) : Protocol X (Fin k ⊕ Q) where
  input i := Sum.inl (eX i)
  output a := P.output (P.untag eX a)
  δ ab := (Sum.inr (P.δ (P.untag eX ab.1, P.untag eX ab.2)).1,
    Sum.inr (P.δ (P.untag eX ab.1, P.untag eX ab.2)).2)

variable {P : Protocol X Q} {k : ℕ} {eX : X ≃ Fin k}

/-- An encounter of the tagged protocol is an encounter of `P` on the represented states. -/
lemma untag_interact (c : Fin n → Fin k ⊕ Q) (e : AgentPair n) :
    P.untag eX ∘ (P.tagInputs eX).interact c e = P.interact (P.untag eX ∘ c) e := by
  funext w
  simp only [Function.comp_apply, Protocol.interact_apply]
  split_ifs <;> rfl

/-- Paths of the tagged protocol are paths of `P` on the represented states. -/
lemma reaches_untag {c d : Fin n → Fin k ⊕ Q} (h : (P.tagInputs eX).Reaches c d) :
    P.Reaches (P.untag eX ∘ c) (P.untag eX ∘ d) := by
  induction h with
  | refl => exact Protocol.Reaches.refl _
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rw [untag_interact]
    exact ih.trans (Protocol.reaches_interact _ e)

/-- Paths of `P` from the represented configuration lift to the tagged protocol. -/
lemma lift_untag {c : Fin n → Fin k ⊕ Q} {d : Fin n → Q} (h : P.Reaches (P.untag eX ∘ c) d) :
    ∃ c', (P.tagInputs eX).Reaches c c' ∧ P.untag eX ∘ c' = d := by
  induction h with
  | refl => exact ⟨c, Protocol.Reaches.refl c, rfl⟩
  | tail _ hst ih =>
    obtain ⟨c', hc', rfl⟩ := ih
    obtain ⟨e, rfl⟩ := hst
    exact ⟨_, hc'.trans (Protocol.reaches_interact c' e), untag_interact c' e⟩

/-- Input tagging preserves stable computation. -/
theorem tagInputs_stablyComputes [Fintype X] [DecidableEq X] {φ : (X → ℕ) → Bool}
    (h : P.StablyComputes φ) : (P.tagInputs eX).StablyComputes φ := by
  intro n hn ι c hc
  have h0 : P.untag eX ∘ ((P.tagInputs eX).input ∘ ι) = P.input ∘ ι := by
    funext w
    simp [Protocol.untag, Protocol.tagInputs]
  obtain ⟨d, hd, hds⟩ := h n hn ι _ (h0 ▸ reaches_untag hc)
  obtain ⟨c', hc', rfl⟩ := lift_untag hd
  exact ⟨c', hc', fun e he w => hds _ (reaches_untag he) w⟩

/-- The tagged protocol has a transition changing the multiset of states (from two copies of an
input state to two `inr`-states). -/
lemma tagInputs_nontrivial (i : X) :
    ∃ p q : Fin k ⊕ Q, s(p, q) ≠ s(((P.tagInputs eX).δ (p, q)).1, ((P.tagInputs eX).δ (p, q)).2) :=
  ⟨Sum.inl (eX i), Sum.inl (eX i), by simp [Protocol.tagInputs]⟩

end Crn
