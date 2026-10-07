import Crn.StableBasic

/-!
# Encounters and reachability: helper lemmas (CRN-3)

Generic facts about `Protocol.interact`, `Protocol.Step`, `Protocol.Reaches` and
`Protocol.OutputStable`, used by all constructions of CRN-3, and two counting lemmas for sums
over agents in which only the two agents of an encounter change.
-/

namespace Crn

open Finset

variable {X Q : Type*} {n : ℕ}

namespace Protocol

variable (P : Protocol X Q)

/-- The state of agent `w` after the encounter `e`. -/
lemma interact_apply (c : Fin n → Q) (e : AgentPair n) (w : Fin n) :
    P.interact c e w = if w = e.1.2 then (P.δ (c e.1.1, c e.1.2)).2
      else if w = e.1.1 then (P.δ (c e.1.1, c e.1.2)).1 else c w := by
  simp only [interact, Function.update_apply]

/-- The initiator gets `δ₁`. -/
lemma interact_fst (c : Fin n → Q) (e : AgentPair n) :
    P.interact c e e.1.1 = (P.δ (c e.1.1, c e.1.2)).1 := by
  rw [interact_apply, if_neg e.2, if_pos rfl]

/-- The responder gets `δ₂`. -/
lemma interact_snd (c : Fin n → Q) (e : AgentPair n) :
    P.interact c e e.1.2 = (P.δ (c e.1.1, c e.1.2)).2 := by
  rw [interact_apply, if_pos rfl]

/-- The other agents keep their states. -/
lemma interact_of_ne (c : Fin n → Q) (e : AgentPair n) {w : Fin n} (h1 : w ≠ e.1.1)
    (h2 : w ≠ e.1.2) : P.interact c e w = c w := by
  rw [interact_apply, if_neg h2, if_neg h1]

/-- An encounter whose transition leaves both states unchanged leaves the configuration
unchanged. -/
lemma interact_eq_self (c : Fin n → Q) (e : AgentPair n)
    (h : P.δ (c e.1.1, c e.1.2) = (c e.1.1, c e.1.2)) : P.interact c e = c := by
  funext w
  rw [interact_apply, h]
  split_ifs with h2 h1
  · rw [h2]
  · rw [h1]
  · rfl

variable {P}

/-- Every configuration reaches itself. -/
lemma Reaches.refl (c : Fin n → Q) : P.Reaches c c := Relation.ReflTransGen.refl

/-- Reachability is transitive. -/
lemma Reaches.trans {c d e : Fin n → Q} (h₁ : P.Reaches c d) (h₂ : P.Reaches d e) :
    P.Reaches c e := Relation.ReflTransGen.trans h₁ h₂

/-- A step is a path. -/
lemma Step.reaches {c d : Fin n → Q} (h : P.Step c d) : P.Reaches c d :=
  Relation.ReflTransGen.single h

/-- A path followed by a step is a path. -/
lemma Reaches.tail {c d e : Fin n → Q} (h₁ : P.Reaches c d) (h₂ : P.Step d e) :
    P.Reaches c e := Relation.ReflTransGen.tail h₁ h₂

/-- One encounter is a step. -/
lemma reaches_interact (c : Fin n → Q) (e : AgentPair n) : P.Reaches c (P.interact c e) :=
  Step.reaches ⟨e, rfl⟩

/-- A property preserved by every step holds along reachability. -/
lemma Reaches.invariant {I : (Fin n → Q) → Prop} (hI : ∀ c d, I c → P.Step c d → I d)
    {c d : Fin n → Q} (h : P.Reaches c d) (hc : I c) : I d := by
  induction h with
  | refl => exact hc
  | tail _ hst ih => exact hI _ _ ih hst

/-- Output-stability is inherited along reachability. -/
lemma OutputStable.reaches {b : Bool} {c d : Fin n → Q} (hc : P.OutputStable b c)
    (h : P.Reaches c d) : P.OutputStable b d :=
  fun e he => hc e (h.trans he)

/-- A property preserved by every step, under which all agents output `b`, gives
output-stability. -/
lemma outputStable_of_invariant {I : (Fin n → Q) → Prop} (hI : ∀ c d, I c → P.Step c d → I d)
    {b : Bool} (hb : ∀ c, I c → ∀ v, P.output (c v) = b) {c : Fin n → Q} (hc : I c) :
    P.OutputStable b c :=
  fun _ h => hb _ (h.invariant hI hc)

end Protocol

/-- Sums over agents when only the agents `u ≠ v` change:
`∑ G' + (G u + G v) = ∑ G + (G' u + G' v)`. -/
lemma sum_add_pair {M : Type*} [AddCommMonoid M] {u v : Fin n} (huv : u ≠ v)
    (G G' : Fin n → M) (h : ∀ w, w ≠ u → w ≠ v → G' w = G w) :
    ∑ w, G' w + (G u + G v) = ∑ w, G w + (G' u + G' v) := by
  have hs : ({u, v} : Finset (Fin n)) ⊆ univ := subset_univ _
  rw [← sum_sdiff hs (f := G'), ← sum_sdiff hs (f := G), sum_pair huv, sum_pair huv,
    sum_congr rfl fun w hw => h w (fun h' => by simp [h'] at hw) (fun h' => by simp [h'] at hw)]
  abel

/-- A sum over agents is at least its terms at two distinct agents. -/
lemma add_le_sum_pair {G : Fin n → ℕ} {u v : Fin n} (huv : u ≠ v) :
    G u + G v ≤ ∑ w, G w := by
  rw [← sum_pair huv]
  exact sum_le_sum_of_subset (subset_univ _)

/-- A sum over agents of a function of their input symbols, grouped by symbol:
`∑_w F(ι w) = ∑_i (counts ι)ᵢ • F i`. -/
lemma sum_comp_eq_sum_counts [Fintype X] [DecidableEq X] {M : Type*} [AddCommMonoid M]
    (ι : Fin n → X) (F : X → M) : ∑ w, F (ι w) = ∑ i, (counts ι).1 i • F i := by
  rw [← sum_fiberwise univ ι fun w => F (ι w)]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_congr rfl fun w hw => by rw [(mem_filter.1 hw).2], sum_const, counts_val]

end Crn
