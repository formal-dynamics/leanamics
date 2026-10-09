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

/-- **[GHMSS16, Lemma 4] for the composition.** If `D` never changes the group of an agent, then
along every execution of `D.drive col grp` the derived colours and the `P₂`-states satisfy the
invariants of Section 3, with the groups given by the `D`-states. -/
theorem drive_dynInv (hgrp : ∀ p q, grp (D.δ (p, q)).1 = grp p ∧ grp (D.δ (p, q)).2 = grp q)
    (ι : Fin n → X) {c : Fin n → Q × DynState}
    (h : (D.drive col grp).Reaches ((D.drive col grp).input ∘ ι) c) :
    DynInv (fun v => grp (c v).1) (fun v => col (c v).1) (fun v => (c v).2) := by
  sorry

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
  sorry

end Protocol

end Crn
