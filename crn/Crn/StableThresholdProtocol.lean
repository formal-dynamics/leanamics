import Crn.StableLeader

/-!
# The threshold protocol (CRN-3)

The protocol of [AADFP06, proof of Lemma 5(1)] for `∑ᵢ aᵢ xᵢ < c`, as a leader protocol
(`Leader.protocol`). Values are integers in `[-s, s]` with `s = |c| + 1 + ∑ᵢ |aᵢ|`; input `i`
starts with value `aᵢ`. A leader encounter gives the initiator the clamped sum
`q(u, u') = max(-s, min(s, u + u'))` and the responder the rest `r(u, u') = u + u' - q(u, u')`,
and the output test is `t(u) = [u < c]`. Unlike AADFP06 (output bit `0`), an input starts with
output bit `t(aᵢ)`, which is needed for a single agent (Deviation 2 of `PROGRESS-CRN3.md`).

Correctness (`stablyComputes`): the sum of the values is `∑ᵢ aᵢ xᵢ`; merge the leaders, then let
the leader absorb the non-leaders' values while this decreases `∑ |u|` over non-leaders. Then
(`classify`) either all non-leaders hold `0`, or the leader holds `s` and all non-leaders are
`≥ 0`, or the leader holds `-s` and all non-leaders are `≤ 0` (AADFP06's stable configurations),
and the leader's test `t` is the predicate's value in each case.
-/

namespace Crn

namespace ThresholdProtocol

open Finset

/-- Counter values `u ∈ [-s, s]`. -/
abbrev Val (s : ℤ) := {u : ℤ // -s ≤ u ∧ u ≤ s}

/-- There are finitely many counter values. -/
instance (s : ℤ) : Finite (Val s) := (Set.finite_Icc (-s) s).to_subtype

/-- Clamping to `[-s, s]`. -/
def clamp (s z : ℤ) : ℤ := max (-s) (min s z)

/-- The initiator's new value: the clamped sum. -/
def q (s : ℤ) (u v : Val s) : Val s :=
  ⟨clamp s (u + v), by have := u.2; unfold clamp; omega⟩

/-- The responder's new value: the rest of the sum. -/
def r (s : ℤ) (u v : Val s) : Val s :=
  ⟨u + v - clamp s (u + v), by have := u.2; have := v.2; unfold clamp; omega⟩

/-- The output test `[u < c]`. -/
def t (s c : ℤ) (u : Val s) : Bool := decide ((u : ℤ) < c)

/-- An encounter conserves the sum of the two values. -/
lemma q_add_r (s : ℤ) (u v : Val s) : ((q s u v : Val s) : ℤ) + (r s u v : ℤ) = u + v := by
  simp only [q, r]
  ring

/-- If no encounter with the leader holding `L` decreases `|y|`, then `y = 0`, or `L = s` and
`y ≥ 0`, or `L = -s` and `y ≤ 0`. -/
lemma classify {s : ℤ} (L y : Val s) (h : (y : ℤ).natAbs ≤ ((r s L y : Val s) : ℤ).natAbs) :
    (y : ℤ) = 0 ∨ ((L : ℤ) = s ∧ 0 ≤ (y : ℤ)) ∨ ((L : ℤ) = -s ∧ (y : ℤ) ≤ 0) := by
  have := L.2
  have := y.2
  simp only [r, clamp] at h
  omega

/-- Stable shape 1: all non-leaders hold `0`. -/
lemma merge_zero {s : ℤ} (L : Val s) : ∀ y : Val s, (y : ℤ) = 0 →
    q s L y = L ∧ r s L y = y ∧ q s y L = L ∧ r s y L = y := by
  intro y hy
  have := L.2
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    simp only [q, r, clamp] <;> omega

/-- Stable shape 2: the leader holds `s`, the non-leaders are `≥ 0`. -/
lemma merge_top {s : ℤ} (L : Val s) (hL : (L : ℤ) = s) : ∀ y : Val s, 0 ≤ (y : ℤ) →
    q s L y = L ∧ r s L y = y ∧ q s y L = L ∧ r s y L = y := by
  intro y hy
  have := y.2
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    simp only [q, r, clamp] <;> omega

/-- Stable shape 3: the leader holds `-s`, the non-leaders are `≤ 0`. -/
lemma merge_bot {s : ℤ} (L : Val s) (hL : (L : ℤ) = -s) : ∀ y : Val s, (y : ℤ) ≤ 0 →
    q s L y = L ∧ r s L y = y ∧ q s y L = L ∧ r s y L = y := by
  intro y hy
  have := y.2
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    simp only [q, r, clamp] <;> omega

variable {X : Type*} [Fintype X]

/-- The bound `s = |c| + 1 + ∑ᵢ |aᵢ|` on the counter values. -/
def bound (a : X → ℤ) (c : ℤ) : ℤ := |c| + 1 + ∑ i, |a i|

/-- `c < s`, `-s < c` and `s ≥ 1`. -/
lemma bound_spec (a : X → ℤ) (c : ℤ) : c < bound a c ∧ -bound a c < c ∧ 1 ≤ bound a c := by
  have h1 : 0 ≤ ∑ i, |a i| := sum_nonneg fun i _ => abs_nonneg (a i)
  have h2 := le_abs_self c
  have h3 := neg_abs_le c
  unfold bound
  omega

/-- The coefficients lie in `[-s, s]`. -/
lemma abs_le_bound (a : X → ℤ) (c : ℤ) (i : X) : -bound a c ≤ a i ∧ a i ≤ bound a c := by
  have h1 : |a i| ≤ ∑ j, |a j| := single_le_sum (fun j _ => abs_nonneg (a j)) (mem_univ i)
  have h2 := abs_nonneg c
  exact abs_le.1 (by unfold bound; linarith)

/-- The initial value `aᵢ` of input `i`. -/
def init (a : X → ℤ) (c : ℤ) (i : X) : Val (bound a c) := ⟨a i, abs_le_bound a c i⟩

/-- The threshold protocol for `∑ᵢ aᵢ xᵢ < c` [AADFP06, proof of Lemma 5(1)]. -/
def protocol (a : X → ℤ) (c : ℤ) : Protocol X (Bool × Bool × Val (bound a c)) :=
  Leader.protocol (init a c) (q _) (r _) (t _ c)

/-- **[AADFP06, Lemma 5(1)]** The threshold protocol stably computes `∑ᵢ aᵢ xᵢ < c`. -/
theorem stablyComputes [DecidableEq X] (a : X → ℤ) (c : ℤ) :
    (protocol a c).StablyComputes fun x => decide (∑ i, a i * (x i : ℤ) < c) := by
  intro n hn ι C hC
  show ∃ D, _ ∧ (protocol a c).OutputStable (decide (∑ i, a i * ((counts ι).1 i : ℤ) < c)) D
  obtain ⟨hcs, hcs', hs1⟩ := bound_spec a c
  obtain ⟨T, hT⟩ : ∃ T, ∑ i, a i * ((counts ι).1 i : ℤ) = T := ⟨_, rfl⟩
  rw [hT]
  -- invariants of the reachable configurations
  have hinv : ∀ D, (protocol a c).Reaches ((protocol a c).input ∘ ι) D →
      Leader.HasLeader D ∧ Leader.LeadOut (t _ c) D ∧ ∑ w, ((D w).2.2 : ℤ) = T := by
    intro D hD
    refine hD.invariant (I := fun D => Leader.HasLeader D ∧ Leader.LeadOut (t _ c) D ∧
      ∑ w, ((D w).2.2 : ℤ) = T) ?_ ⟨Leader.hasLeader_input hn ι, Leader.leadOut_input ι, ?_⟩
    · rintro D D' ⟨h1, h2, h3⟩ hst
      exact ⟨Leader.hasLeader_step hst h1, Leader.leadOut_step h2 hst,
        (Leader.sum_step (F := Subtype.val) (q_add_r _) hst).trans h3⟩
    · rw [protocol, Leader.sum_input Subtype.val ι, ← hT]
      exact sum_congr rfl fun i _ => by rw [nsmul_eq_mul, mul_comm]; rfl
  -- merge the leaders, then decrease `∑ |u|` over the non-leaders
  obtain ⟨C₁, hC₁, h1⟩ := Leader.exists_reaches_atMostOne (init := init a c) (q := q _)
    (r := r _) (t := t _ c) C
  obtain ⟨C₂, hC₂, h2, h3⟩ := Leader.exists_reaches_noImprove (init := init a c) (q := q _)
    (t := t _ c) (fun y => (y : ℤ).natAbs) C₁ h1
  obtain ⟨⟨ℓ, hℓ⟩, hlo, hsum⟩ := hinv C₂ (hC.trans (hC₁.trans hC₂))
  obtain ⟨L, hL⟩ : ∃ L, (C₂ ℓ).2.2 = L := ⟨_, rfl⟩
  have hcl : ∀ j, (C₂ j).1 = false → ((C₂ j).2.2 : ℤ) = 0 ∨ ((L : ℤ) = bound a c ∧
      0 ≤ ((C₂ j).2.2 : ℤ)) ∨ ((L : ℤ) = -bound a c ∧ ((C₂ j).2.2 : ℤ) ≤ 0) :=
    fun j hj => hL ▸ classify _ _ (h3 ℓ j hℓ hj)
  have hnl : ∀ w ∈ univ.erase ℓ, (C₂ w).1 = false := fun w hw => by
    cases h : (C₂ w).1
    · rfl
    · exact absurd (h2 _ _ h hℓ) (mem_erase.1 hw).1
  have hTL : T = L + ∑ w ∈ univ.erase ℓ, ((C₂ w).2.2 : ℤ) := by
    rw [← hsum, ← add_sum_erase _ _ (mem_univ ℓ), hL]
  -- the leader holds `L`; the non-leaders satisfy `R`
  have finish : ∀ R : Val (bound a c) → Prop, (∀ j, (C₂ j).1 = false → R (C₂ j).2.2) →
      (∀ y, R y → q _ L y = L ∧ r _ L y = y ∧ q _ y L = L ∧ r _ y L = y) →
      ((L : ℤ) < c ↔ T < c) →
      ∃ D, (protocol a c).Reaches C D ∧ (protocol a c).OutputStable (decide (T < c)) D := by
    intro R hR H hiff
    have good : Leader.Good (t _ c) L R C₂ :=
      ⟨⟨ℓ, hℓ⟩, h2, fun w hw => by rw [h2 _ _ hw hℓ, hlo ℓ hℓ, hL]; exact ⟨rfl, rfl⟩, hR⟩
    obtain ⟨D, hD, hDs⟩ := good.exists_outputStable H
    refine ⟨D, hC₁.trans (hC₂.trans hD), ?_⟩
    have ht : t _ c L = decide (T < c) := decide_eq_decide.2 hiff
    rw [← ht]
    exact hDs
  by_cases hLs : (L : ℤ) = bound a c
  · refine finish (fun y => 0 ≤ (y : ℤ)) (fun j hj => by have := hcl j hj; omega)
      (merge_top L hLs) ?_
    have : 0 ≤ ∑ w ∈ univ.erase ℓ, ((C₂ w).2.2 : ℤ) := sum_nonneg fun w hw => by
      have := hcl w (hnl w hw); omega
    omega
  by_cases hLs' : (L : ℤ) = -bound a c
  · refine finish (fun y => (y : ℤ) ≤ 0) (fun j hj => by have := hcl j hj; omega)
      (merge_bot L hLs') ?_
    have : ∑ w ∈ univ.erase ℓ, ((C₂ w).2.2 : ℤ) ≤ 0 := sum_nonpos fun w hw => by
      have := hcl w (hnl w hw); omega
    omega
  · refine finish (fun y => (y : ℤ) = 0) (fun j hj => by have := hcl j hj; omega)
      (merge_zero L) ?_
    have : ∑ w ∈ univ.erase ℓ, ((C₂ w).2.2 : ℤ) = 0 := sum_eq_zero fun w hw => by
      have := hcl w (hnl w hw); omega
    omega

end ThresholdProtocol

end Crn
