import Epidemics.CobraCoverIndep
import Epidemics.CobraCoverEngine
import Epidemics.CobraReverse
import Dynamics.Reverse

/-! # COBRA and BIPS with target sets (EPI-4, Theorem 3)

Both COBRA with branching factor `1 + ρ` and its dual BIPS read, in a round `ρ`, a finite set
`tg ρ x` of neighbours used by each vertex `x`: COBRA pushes from `x` to `tg ρ x`, and in BIPS a
vertex `u` is infected iff it is the source or `tg ρ u` meets the infected set. This file proves,
for an arbitrary target map `tg`,

* the pathwise duality and Theorem 4 (`tgt_hit_iff_bips_reverse`, `tgt_duality`), by the proof
  of `cobra_hit_iff_bips_reverse` and `cobra_bips_duality`;
* monotonicity, persistence of the source, `univ` absorbing and nonemptiness of COBRA when the
  target sets are nonempty;
* when `tg ρ u` only depends on the coordinate `u` of `ρ` under an equivalence
  `R ≃ (u : V) → Ω u` (independent vertices), the moment generating function bound (12) and the
  formula `E|A'| = ∑_u P(u ∈ A')`.

`cobraCoinStep p` and `bipsCoinStep p v` are `tgtCobraStep (coinTargets p)` and
`tgtBipsStep (coinTargets p) v` by definition.
-/

namespace Epidemics
open Finset Dynamics Real

variable {V R : Type*} [DecidableEq V]

/-- COBRA with target sets: every vertex `x` of `D` pushes to the vertices of `tg ρ x`. -/
def tgtCobraStep (tg : R → V → Finset V) (D : Finset V) (ρ : R) : Finset V :=
  D.biUnion (tg ρ)

/-- BIPS with target sets and source `v`: `u` is infected iff `u = v` or `tg ρ u` meets `A`. -/
def tgtBipsStep [Fintype V] (tg : R → V → Finset V) (v : V) (A : Finset V) (ρ : R) :
    Finset V :=
  insert v (univ.filter fun u => ∃ y ∈ tg ρ u, y ∈ A)

variable {tg : R → V → Finset V}

lemma mem_tgtCobraStep {D : Finset V} {ρ : R} {y : V} :
    y ∈ tgtCobraStep tg D ρ ↔ ∃ x ∈ D, y ∈ tg ρ x := by
  simp [tgtCobraStep]

lemma mem_tgtBipsStep [Fintype V] {v : V} {A : Finset V} {ρ : R} {u : V} :
    u ∈ tgtBipsStep tg v A ρ ↔ u = v ∨ ∃ y ∈ tg ρ u, y ∈ A := by
  simp [tgtBipsStep]

omit [DecidableEq V] in
/-- The COBRA hitting event over the rounds `ρ :: l` (as `hits_cons`, for any step). -/
lemma hits_cons_roundRun (step : Finset V → R → Finset V) (v : V) (C : Finset V) (ρ : R)
    (l : List R) :
    (∃ s ≤ (ρ :: l).length, v ∈ roundRun step C ((ρ :: l).take s)) ↔
      v ∈ C ∨ ∃ s ≤ l.length, v ∈ roundRun step (step C ρ) (l.take s) := by
  constructor
  · rintro ⟨s, hs, hv⟩
    cases s with
    | zero => exact Or.inl (by simpa using hv)
    | succ s => exact Or.inr ⟨s, by simpa using hs, by simpa using hv⟩
  · rintro (hv | ⟨s, hs, hv⟩)
    · exact ⟨0, Nat.zero_le _, by simpa using hv⟩
    · exact ⟨s + 1, by simpa using hs, by simpa using hv⟩

/-- **Pathwise duality with target sets**: COBRA from `C` visits `v` within the rounds `l` iff
BIPS from `{v}` along the reversed rounds infects a vertex of `C`. -/
theorem tgt_hit_iff_bips_reverse [Fintype V] (v : V) (C : Finset V) (l : List R) :
    (∃ s ≤ l.length, v ∈ roundRun (tgtCobraStep tg) C (l.take s)) ↔
      (C ∩ roundRun (tgtBipsStep tg v) {v} l.reverse).Nonempty := by
  induction l generalizing C with
  | nil => by_cases hv : v ∈ C <;> simp [hv]
  | cons ρ l ih =>
    rw [hits_cons_roundRun, ih, List.reverse_cons, roundRun_append]
    simp only [roundRun_cons, roundRun_nil, Finset.Nonempty, mem_inter, mem_tgtCobraStep,
      mem_tgtBipsStep]
    constructor
    · rintro (hv | ⟨y, ⟨x, hx, hy⟩, hyA⟩)
      · exact ⟨v, hv, Or.inl rfl⟩
      · exact ⟨x, hx, Or.inr ⟨y, hy, hyA⟩⟩
    · rintro ⟨x, hx, rfl | ⟨y, hy, hyA⟩⟩
      · exact Or.inl hx
      · exact Or.inr ⟨y, ⟨x, hx, hy⟩, hyA⟩

/-- **Theorem 4 with target sets**: `P(Hit_C(v) > t) = P(C ∩ A_t = ∅ ∣ A₀ = {v})`. -/
theorem tgt_duality [Fintype V] [Fintype R] (v : V) (C : Finset V) (t : ℕ) :
    expList R t
        (fun l => if ∀ s ≤ t, v ∉ roundRun (tgtCobraStep tg) C (l.take s) then (1 : ℝ) else 0) =
      expList R t (fun l => if C ∩ roundRun (tgtBipsStep tg v) {v} l = ∅ then (1 : ℝ) else 0) := by
  conv_rhs => rw [← expList_comp_reverse]
  refine expList_congr_length t fun l hl => ?_
  have h : (∀ s ≤ t, v ∉ roundRun (tgtCobraStep tg) C (l.take s)) ↔
      C ∩ roundRun (tgtBipsStep tg v) {v} l.reverse = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty, ← tgt_hit_iff_bips_reverse, hl]
    push Not
    rfl
  exact if_congr h rfl rfl

lemma src_mem_tgtBipsStep [Fintype V] (v : V) (A : Finset V) (ρ : R) :
    v ∈ tgtBipsStep tg v A ρ :=
  mem_insert_self _ _

lemma tgtBipsStep_mono [Fintype V] (v : V) {A B : Finset V} (h : A ⊆ B) (ρ : R) :
    tgtBipsStep tg v A ρ ⊆ tgtBipsStep tg v B ρ := by
  intro u hu
  rw [mem_tgtBipsStep] at hu ⊢
  rcases hu with rfl | ⟨y, hy, hyA⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨y, hy, h hyA⟩

lemma tgtBipsStep_univ [Fintype V] (htg : ∀ ρ u, (tg ρ u).Nonempty) (v : V) (ρ : R) :
    tgtBipsStep tg v univ ρ = univ := by
  refine eq_univ_iff_forall.mpr fun u => ?_
  obtain ⟨y, hy⟩ := htg ρ u
  exact mem_tgtBipsStep.mpr (Or.inr ⟨y, hy, mem_univ y⟩)

lemma tgtCobraStep_nonempty (htg : ∀ ρ u, (tg ρ u).Nonempty) {D : Finset V} (hD : D.Nonempty)
    (ρ : R) : (tgtCobraStep tg D ρ).Nonempty := by
  obtain ⟨x, hx⟩ := hD
  obtain ⟨y, hy⟩ := htg ρ x
  exact ⟨y, mem_tgtCobraStep.mpr ⟨x, hx, hy⟩⟩

section Independent

variable [Fintype V] [Fintype R] {Ω : V → Type*} [∀ u, Fintype (Ω u)]

omit [Fintype R] [∀ u, Fintype (Ω u)] in
/-- With independent targets, the size of the next BIPS set counts independent events. -/
lemma card_tgtBipsStep_eq (e : R ≃ ((u : V) → Ω u)) (g : (u : V) → Ω u → Finset V)
    (htg : ∀ ρ u, tg ρ u = g u (e ρ u)) (v : V) (A : Finset V) (ρ : R) :
    (tgtBipsStep tg v A ρ).card =
      (univ.filter fun u => u = v ∨ ∃ y ∈ g u (e ρ u), y ∈ A).card := by
  congr 1
  ext u
  simp only [mem_tgtBipsStep, htg, mem_filter, mem_univ, true_and]

/-- **Moment generating function of one round** (computation (12)) for BIPS with independent
target sets. -/
theorem tgtBips_mgf_le (e : R ≃ ((u : V) → Ω u)) (g : (u : V) → Ω u → Finset V)
    (htg : ∀ ρ u, tg ρ u = g u (e ρ u)) (v : V) (A : Finset V) (φ : ℝ) :
    avg (fun ρ : R => exp (-φ * ((tgtBipsStep tg v A ρ).card : ℝ))) ≤
      exp (-(1 - exp (-φ)) * avg (fun ρ : R => ((tgtBipsStep tg v A ρ).card : ℝ))) := by
  let X : (u : V) → Ω u → Prop := fun u a => u = v ∨ ∃ y ∈ g u a, y ∈ A
  have hc (ρ : R) : ((tgtBipsStep tg v A ρ).card : ℝ) =
      ((univ.filter fun u => X u (e ρ u)).card : ℝ) := by
    rw [card_tgtBipsStep_eq e g htg v A ρ]
  simp_rw [hc]
  rw [avg_equiv e (fun ω => exp (-φ * ((univ.filter fun u => X u (ω u)).card : ℝ))),
    avg_equiv e (fun ω => ((univ.filter fun u => X u (ω u)).card : ℝ))]
  exact pi_count_mgf_le X φ

/-- **Expected size of one round** for BIPS with independent target sets:
`E|A'| = ∑_u P(u ∈ A')`. -/
theorem tgtBips_expected_card [∀ u, Nonempty (Ω u)] (e : R ≃ ((u : V) → Ω u))
    (g : (u : V) → Ω u → Finset V) (htg : ∀ ρ u, tg ρ u = g u (e ρ u)) (v : V)
    (A : Finset V) :
    avg (fun ρ : R => ((tgtBipsStep tg v A ρ).card : ℝ)) =
      ∑ u, avg (fun a : Ω u => if u = v ∨ ∃ y ∈ g u a, y ∈ A then (1 : ℝ) else 0) := by
  let X : (u : V) → Ω u → Prop := fun u a => u = v ∨ ∃ y ∈ g u a, y ∈ A
  have hc (ρ : R) : ((tgtBipsStep tg v A ρ).card : ℝ) =
      ((univ.filter fun u => X u (e ρ u)).card : ℝ) := by
    rw [card_tgtBipsStep_eq e g htg v A ρ]
  simp_rw [hc]
  rw [avg_equiv e (fun ω => ((univ.filter fun u => X u (ω u)).card : ℝ))]
  exact avg_pi_count X

end Independent

end Epidemics
