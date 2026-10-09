import Crn.ExactMajorityDynamic

/-!
# Driving the dynamic majority protocol by another protocol (CRN-5, [GHMSS16, Sections 4–5])

The composition step of [GHMSS16, Sections 4 and 5]: a protocol `D` (the *driver*) runs, and
every agent derives from its `D`-state a colour `col q ∈ {-1, 0, 1}` for a copy of the dynamic
majority protocol `P₂`. The changes of these colours are the external force of `P₂` [GHMSS16,
Section 3]. In `D.drive col grp`, the states are pairs `(q, s)`, `s` a state of `P₂`; in an
encounter, `D` makes its transition, `P₂` makes its transition if the two agents are in the same
group (`grp`, a function of the `D`-state that `D` never changes: the label prefix in Section 5,
a single group in Section 4), and then each agent whose colour changed applies the state change of
Fig. 3 (`DynState.recolour`). Initially the `P₂`-state is `[col q]`.

Main statements:
* `drive_dynInv`: along every execution, the colours derived from the `D`-states and the
  `P₂`-states satisfy the invariants of Section 3 (Lemma 4 for the composition).
* `drive_stablyMarks`: if `D` stably marks every agent with its eventual colour (and possibly
  further outputs), then `D.drive col grp` stably marks every agent with the sign of the eventual
  colour sum of its group, i.e. `P₂` tolerates the dynamic changes of its inputs while `D`
  stabilizes [GHMSS16, proofs of Theorems 6 and 7].
-/

namespace Crn

open Finset

variable {X Q G Y : Type*} [DecidableEq G] {n : ℕ}

namespace Protocol

/-- The dynamic majority protocol driven by `D` through the colours `col`, run inside the groups
`grp` [GHMSS16, Sections 4–5]: `D` makes its transition, `P₂` makes its transition between agents
of the same group, then each agent recolours its `P₂`-state from its old colour to its new colour.
The `Bool` output (the `P₂`-output is `1`) is not used. -/
def drive (D : Protocol X Q) (col : Q → SignType) (grp : Q → G) : Protocol X (Q × DynState) where
  input x := (D.input x, DynState.ofWeight (col (D.input x)))
  output p := decide (p.2.out = 1)
  δ pq :=
    let r := D.δ (pq.1.1, pq.2.1)
    let s := if grp pq.1.1 = grp pq.2.1 then DynState.δ (pq.1.2, pq.2.2) else (pq.1.2, pq.2.2)
    ((r.1, DynState.recolour (col pq.1.1) (col r.1) s.1),
      (r.2, DynState.recolour (col pq.2.1) (col r.2) s.2))

variable {D : Protocol X Q} {col : Q → SignType} {grp : Q → G}

/-- The transition of the driven protocol, unfolded. -/
theorem drive_δ (p q : Q × DynState) : (D.drive col grp).δ (p, q) =
    (((D.δ (p.1, q.1)).1, DynState.recolour (col p.1) (col (D.δ (p.1, q.1)).1)
        (if grp p.1 = grp q.1 then DynState.δ (p.2, q.2) else (p.2, q.2)).1),
      ((D.δ (p.1, q.1)).2, DynState.recolour (col q.1) (col (D.δ (p.1, q.1)).2)
        (if grp p.1 = grp q.1 then DynState.δ (p.2, q.2) else (p.2, q.2)).2)) := rfl

/-- The `D`-states of an encounter of the driven protocol make an encounter of `D`. -/
theorem drive_interact_fst (c : Fin n → Q × DynState) (e : AgentPair n) :
    (fun w => ((D.drive col grp).interact c e w).1) = D.interact (fun w => (c w).1) e := by
  funext w
  rw [interact_apply, interact_apply]
  split_ifs <;> rfl

/-- Paths of the driven protocol project to paths of `D`. -/
theorem drive_reaches_fst {c d : Fin n → Q × DynState} (h : (D.drive col grp).Reaches c d) :
    D.Reaches (fun w => (c w).1) (fun w => (d w).1) := by
  induction h with
  | refl => exact Reaches.refl _
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rw [drive_interact_fst]
    exact ih.trans (reaches_interact _ e)

/-- A path of `D` lifts to the driven protocol (same encounters). -/
theorem drive_lift_fst {c₁ d₁ : Fin n → Q} (h : D.Reaches c₁ d₁) (c : Fin n → Q × DynState)
    (hc : (fun w => (c w).1) = c₁) :
    ∃ d, (D.drive col grp).Reaches c d ∧ (fun w => (d w).1) = d₁ := by
  induction h with
  | refl => exact ⟨c, Reaches.refl _, hc⟩
  | tail _ hst ih =>
    obtain ⟨d, hd, hd1⟩ := ih
    obtain ⟨e, rfl⟩ := hst
    exact ⟨_, hd.trans (reaches_interact _ e), by rw [drive_interact_fst, hd1]⟩

/-- If `D` never changes groups, the group of every agent is constant along paths of the driven
protocol. -/
theorem drive_grp (hgrp : ∀ p q, grp (D.δ (p, q)).1 = grp p ∧ grp (D.δ (p, q)).2 = grp q)
    {c d : Fin n → Q × DynState} (h : (D.drive col grp).Reaches c d) :
    ∀ w, grp (d w).1 = grp (c w).1 := by
  induction h with
  | refl => exact fun _ => rfl
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    intro w
    rw [interact_apply]
    split_ifs with h2 h1
    · subst h2
      exact (hgrp _ _).2.trans (ih _)
    · subst h1
      exact (hgrp _ _).1.trans (ih _)
    · exact ih w

/-- If the transition of `D` does not change the colours of the two agents, the `P₂`-states of an
encounter of the driven protocol make an encounter of `P₂` if the agents are in the same group,
and do not change otherwise. -/
theorem drive_interact_snd (c : Fin n → Q × DynState) (e : AgentPair n)
    (h1 : col (D.δ ((c e.1.1).1, (c e.1.2).1)).1 = col (c e.1.1).1)
    (h2 : col (D.δ ((c e.1.1).1, (c e.1.2).1)).2 = col (c e.1.2).1) :
    (fun w => ((D.drive col grp).interact c e w).2) =
      if grp (c e.1.1).1 = grp (c e.1.2).1 then dynamicMajority.interact (fun w => (c w).2) e
      else fun w => (c w).2 := by
  funext w
  split_ifs with hg
  · rw [interact_apply, interact_apply, drive_δ, h1, h2, if_pos hg]
    split_ifs <;> simp only [DynState.recolour_self] <;> rfl
  · rw [interact_apply, drive_δ, h1, h2, if_neg hg]
    split_ifs with hw2 hw1
    · subst hw2
      simp only [DynState.recolour_self]
    · subst hw1
      simp only [DynState.recolour_self]
    · rfl

/-- If every `D`-configuration reachable from the `D`-part of `c` has the colours `κ`, then a path
of `P₂` inside the groups `g` (the groups of the agents in `c`) lifts to the driven protocol. -/
theorem drive_lift_snd (hgrp : ∀ p q, grp (D.δ (p, q)).1 = grp p ∧ grp (D.δ (p, q)).2 = grp q)
    {g : Fin n → G} {κ : Fin n → SignType} {c : Fin n → Q × DynState}
    (hg : ∀ w, grp (c w).1 = g w)
    (hκ : ∀ d₁, D.Reaches (fun w => (c w).1) d₁ → ∀ w, col (d₁ w) = κ w)
    {d₂ : Fin n → DynState} (h : dynamicMajority.GReaches g (fun w => (c w).2) d₂) :
    ∃ d, (D.drive col grp).Reaches c d ∧ (fun w => (d w).2) = d₂ := by
  induction h with
  | refl => exact ⟨c, Reaches.refl _, rfl⟩
  | tail _ hst ih =>
    obtain ⟨d, hd, hd2⟩ := ih
    obtain ⟨e, he, rfl⟩ := hst
    refine ⟨_, hd.trans (reaches_interact _ e), ?_⟩
    have hd1 := drive_reaches_fst hd
    have hdg := drive_grp hgrp hd
    have hcol : ∀ w, col (d w).1 = κ w := hκ _ hd1
    have hcol' := hκ _ (hd1.trans (reaches_interact _ e))
    have h1 : col (D.δ ((d e.1.1).1, (d e.1.2).1)).1 = col (d e.1.1).1 := by
      have := hcol' e.1.1
      rw [interact_fst] at this
      exact this.trans (hcol _).symm
    have h2 : col (D.δ ((d e.1.1).1, (d e.1.2).1)).2 = col (d e.1.2).1 := by
      have := hcol' e.1.2
      rw [interact_snd] at this
      exact this.trans (hcol _).symm
    rw [drive_interact_snd d e h1 h2, if_pos (by rw [hdg, hdg, hg, hg]; exact he), hd2]

/-- If every `D`-configuration reachable from the `D`-part of `c` has the colours `κ`, then paths
of the driven protocol from `c` project to paths of `P₂` inside the groups `g` (the groups of the
agents in `c`). -/
theorem drive_greaches_snd
    (hgrp : ∀ p q, grp (D.δ (p, q)).1 = grp p ∧ grp (D.δ (p, q)).2 = grp q)
    {g : Fin n → G} {κ : Fin n → SignType} {c : Fin n → Q × DynState}
    (hg : ∀ w, grp (c w).1 = g w)
    (hκ : ∀ d₁, D.Reaches (fun w => (c w).1) d₁ → ∀ w, col (d₁ w) = κ w)
    {d : Fin n → Q × DynState} (h : (D.drive col grp).Reaches c d) :
    dynamicMajority.GReaches g (fun w => (c w).2) (fun w => (d w).2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hcd hst ih =>
    obtain ⟨e, rfl⟩ := hst
    rename_i d
    have hd1 := drive_reaches_fst hcd
    have hdg := drive_grp hgrp hcd
    have hcol : ∀ w, col (d w).1 = κ w := hκ _ hd1
    have hcol' := hκ _ (hd1.trans (reaches_interact _ e))
    have h1 : col (D.δ ((d e.1.1).1, (d e.1.2).1)).1 = col (d e.1.1).1 := by
      have := hcol' e.1.1
      rw [interact_fst] at this
      exact this.trans (hcol _).symm
    have h2 : col (D.δ ((d e.1.1).1, (d e.1.2).1)).2 = col (d e.1.2).1 := by
      have := hcol' e.1.2
      rw [interact_snd] at this
      exact this.trans (hcol _).symm
    rw [drive_interact_snd d e h1 h2]
    split_ifs with hge
    · exact Relation.ReflTransGen.tail ih ⟨e, by rw [← hg, ← hg, ← hdg, ← hdg]; exact hge, rfl⟩
    · exact ih

/-- One encounter of the driven protocol preserves the invariants of Section 3: it is an
interaction of `P₂` inside a group (or nothing), followed by the colour changes of its two
agents. -/
theorem drive_dynInv_interact
    (hgrp : ∀ p q, grp (D.δ (p, q)).1 = grp p ∧ grp (D.δ (p, q)).2 = grp q)
    {c : Fin n → Q × DynState}
    (hc : DynInv (fun v => grp (c v).1) (fun v => col (c v).1) (fun v => (c v).2))
    (e : AgentPair n) :
    DynInv (fun v => grp ((D.drive col grp).interact c e v).1)
      (fun v => col ((D.drive col grp).interact c e v).1)
      (fun v => ((D.drive col grp).interact c e v).2) := by
  obtain ⟨⟨u, v⟩, huv⟩ := e
  have hg : (fun w => grp ((D.drive col grp).interact c ⟨(u, v), huv⟩ w).1) =
      fun w => grp (c w).1 := by
    funext w
    rw [interact_apply]
    split_ifs with h2 h1
    · rw [h2]
      exact (hgrp _ _).2
    · rw [h1]
      exact (hgrp _ _).1
    · rfl
  rw [hg]
  obtain ⟨r, hr⟩ : ∃ r, r = D.δ ((c u).1, (c v).1) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = if grp (c u).1 = grp (c v).1 then DynState.δ ((c u).2, (c v).2)
      else ((c u).2, (c v).2) := ⟨_, rfl⟩
  -- the interaction of `P₂` (with the old colours)
  have h1 : DynInv (fun w => grp (c w).1) (fun w => col (c w).1)
      (fun w => if w = v then s.2 else if w = u then s.1 else (c w).2) := by
    by_cases hg' : grp (c u).1 = grp (c v).1
    · have : (fun w => if w = v then s.2 else if w = u then s.1 else (c w).2) =
          dynamicMajority.interact (fun w => (c w).2) ⟨(u, v), huv⟩ := by
        funext w
        rw [interact_apply, hs, if_pos hg']
        rfl
      rw [this]
      exact hc.gstep ⟨_, hg', rfl⟩
    · have : (fun w => if w = v then s.2 else if w = u then s.1 else (c w).2) =
          fun w => (c w).2 := by
        funext w
        rw [hs, if_neg hg']
        split_ifs with h2 h1
        · rw [h2]
        · rw [h1]
        · rfl
      rw [this]
      exact hc
  -- the colour changes of `u` and `v`
  have h2 := (h1.recolour u (col r.1)).recolour v (col r.2)
  have hcol : (fun w => col ((D.drive col grp).interact c ⟨(u, v), huv⟩ w).1) =
      Function.update (Function.update (fun w => col (c w).1) u (col r.1)) v (col r.2) := by
    funext w
    rw [interact_apply, drive_δ, ← hr]
    simp only [Function.update_apply]
    split_ifs <;> rfl
  have hst : (fun w => ((D.drive col grp).interact c ⟨(u, v), huv⟩ w).2) =
      Function.update (Function.update
        (fun w => if w = v then s.2 else if w = u then s.1 else (c w).2) u
        (DynState.recolour (col (c u).1) (col r.1) (if u = v then s.2 else if u = u then s.1
          else (c u).2))) v
        (DynState.recolour (Function.update (fun w => col (c w).1) u (col r.1) v) (col r.2)
          (Function.update (fun w => if w = v then s.2 else if w = u then s.1 else (c w).2) u
            (DynState.recolour (col (c u).1) (col r.1) (if u = v then s.2 else if u = u then s.1
              else (c u).2)) v)) := by
    funext w
    rw [interact_apply, drive_δ, ← hr, ← hs]
    simp only [Function.update_apply, if_neg huv.symm, if_neg huv]
    split_ifs <;> rfl
  rw [hcol, hst]
  exact h2

/-- **[GHMSS16, Lemma 4] for the composition.** If `D` never changes the group of an agent, then
along every execution of `D.drive col grp` the derived colours and the `P₂`-states satisfy the
invariants of Section 3, with the groups given by the `D`-states. -/
theorem drive_dynInv (hgrp : ∀ p q, grp (D.δ (p, q)).1 = grp p ∧ grp (D.δ (p, q)).2 = grp q)
    (ι : Fin n → X) {c : Fin n → Q × DynState}
    (h : (D.drive col grp).Reaches ((D.drive col grp).input ∘ ι) c) :
    DynInv (fun v => grp (c v).1) (fun v => col (c v).1) (fun v => (c v).2) := by
  induction h with
  | refl => exact DynInv.input _ _
  | tail _ hst ih =>
    obtain ⟨e, rfl⟩ := hst
    exact drive_dynInv_interact hgrp ih e

variable [Fintype X] [DecidableEq X]

/-- **The composition step [GHMSS16, proofs of Theorems 6 and 7].** Let `D` never change groups,
with the group of an agent with input `i` equal to `γ i`. If `D` stably marks the agents with the
outputs `O` and the colours `col` (targets `gO` and `gc`), then the driven protocol stably marks
them with the outputs `O` and with the `P₂`-output equal to the sign of the eventual colour sum of
the group: `sign (∑_{j : γ j = γ i} x_j · gc(x, j))` for an agent with input `i`. -/
theorem drive_stablyMarks
    (hgrp : ∀ p q, grp (D.δ (p, q)).1 = grp p ∧ grp (D.δ (p, q)).2 = grp q)
    {γ : X → G} (hγ : ∀ i, grp (D.input i) = γ i) {O : Q → Y} {gO : (X → ℕ) → X → Y}
    {gc : (X → ℕ) → X → SignType}
    (hD : D.StablyMarks (fun q => (O q, col q)) fun x i => (gO x i, gc x i)) :
    (D.drive col grp).StablyMarks (fun p => (O p.1, p.2.out)) fun x i =>
      (gO x i, SignType.sign (∑ j ∈ univ.filter (fun j => γ j = γ i),
        (x j : ℤ) * ((gc x j : SignType) : ℤ))) := by
  intro n hn ι c hc
  -- `D` stabilizes its outputs and colours
  obtain ⟨d₁, hd₁, hs₁⟩ := hD n hn ι _ (drive_reaches_fst hc)
  obtain ⟨c', hc', hc'1⟩ := drive_lift_fst (col := col) (grp := grp) hd₁ c rfl
  have hreach := hc.trans hc'
  have hg : ∀ w, grp (c' w).1 = γ (ι w) := fun w => (drive_grp hgrp hreach w).trans (hγ (ι w))
  have hκ : ∀ d', D.Reaches (fun w => (c' w).1) d' → ∀ w, col (d' w) = gc (counts ι).1 (ι w) := by
    intro d' hd' w
    rw [hc'1] at hd'
    exact congrArg Prod.snd (hs₁ d' hd' w)
  -- then `P₂` stabilizes inside the groups
  have hinv := drive_dynInv hgrp ι hreach
  rw [show (fun v => grp (c' v).1) = fun v => γ (ι v) from funext hg] at hinv
  obtain ⟨d₂, hd₂, hst₂⟩ := hinv.exists_stable
  obtain ⟨d, hd, hd2⟩ := drive_lift_snd hgrp hg hκ hd₂
  refine ⟨d, hc'.trans hd, fun f hf v => ?_⟩
  have hfst : D.Reaches d₁ (fun w => (f w).1) := by
    rw [← hc'1]
    exact drive_reaches_fst (hd.trans hf)
  have hdg : ∀ w, grp (d w).1 = γ (ι w) := fun w => (drive_grp hgrp hd w).trans (hg w)
  have hdκ : ∀ d', D.Reaches (fun w => (d w).1) d' → ∀ w, col (d' w) = gc (counts ι).1 (ι w) :=
    fun d' hd' => hκ d' ((drive_reaches_fst hd).trans hd')
  have hsnd := drive_greaches_snd hgrp hdg hdκ hf
  rw [hd2] at hsnd
  have h1 := hs₁ _ hfst v
  have h2 : (f v).2.out = _ := hst₂ _ hsnd v
  have h1' := congrArg Prod.fst h1
  refine Prod.ext h1' ?_
  dsimp only
  rw [h2]
  congr 1
  -- the colour sum of the group, over agents and over labels
  rw [sum_congr rfl fun u _ => congrArg (fun s : SignType => (s : ℤ))
      (hκ _ (Reaches.refl _) u : col (c' u).1 = gc (counts ι).1 (ι u)),
    sum_filter, sum_filter, sum_comp_eq_sum_counts ι fun j =>
      if γ j = γ (ι v) then ((gc (counts ι).1 j : SignType) : ℤ) else 0]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

end Protocol

end Crn
