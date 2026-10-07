import Epidemics.CobraLemmas
import Epidemics.CobraReverse

/-! # COBRA ⇔ BIPS duality (EPI-4)

Cooper, Radzik, Rivera, PODC 2016 (arXiv:1602.05768), Theorem 4 and equation (2).

Write `Hit_C(v) = min {s ≥ 0 : v ∈ C_s}` for the first time COBRA started from `C₀ = C` visits
`v`. Theorem 4 says that `P(Hit_C(v) > t | C₀ = C) = P(C ∩ A_t = ∅ | A₀ = {v})`, where `A_t` is
BIPS with persistent source `v`.

*Pathwise form.* Fix the rounds `r₁, …, r_t`. COBRA from `C` along `r₁, …, r_t` visits `v` by time
`t` iff some vertex of `C` is infected at time `t` by BIPS from `{v}` run along the reversed rounds
`r_t, …, r₁`: both say that a chain `x₀ ∈ C`, `x₁ = r₁ x₀ i₁`, …, `x_s = r_s x_{s-1} i_s = v` with
`s ≤ t` exists. Since the rounds are i.i.d., reversing them preserves their joint law, which gives
the distributional statement.
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

/-- **Pathwise COBRA–BIPS duality.** COBRA started from `C` visits `v` within the rounds `l` (at
some time `s ≤ l.length`, time `0` included) iff BIPS with source `v`, started from `{v}` and run
along the same rounds in reverse order, infects a vertex of `C`. -/
theorem cobra_hit_iff_bips_reverse (v : V) (C : Finset V) (l : List (Choices G k)) :
    (∃ s ≤ l.length, v ∈ cobraRun C (l.take s)) ↔ (C ∩ bipsRun v {v} l.reverse).Nonempty := by
  induction l generalizing C with
  | nil => by_cases hv : v ∈ C <;> simp [bipsRun, hv]
  | cons r l ih =>
    rw [hits_cons, ih, List.reverse_cons, bipsRun_append_singleton]
    simp only [Finset.Nonempty, mem_inter, mem_cobraStep, mem_bipsStep]
    constructor
    · rintro (hv | ⟨y, ⟨x, hx, i, rfl⟩, hy⟩)
      · exact ⟨v, hv, Or.inl rfl⟩
      · exact ⟨x, hx, Or.inr ⟨i, hy⟩⟩
    · rintro ⟨x, hx, rfl | ⟨i, hi⟩⟩
      · exact Or.inl hx
      · exact Or.inr ⟨_, ⟨x, hx, i, rfl⟩, hi⟩

variable [DecidableRel G.Adj]

/-- **Theorem 4 (COBRA–BIPS duality).** For every vertex `v`, set `C` and time `t`, the
probability that COBRA started from `C₀ = C` has not visited `v` by time `t` (`Hit_C(v) > t`)
equals the probability that BIPS with persistent source `v`, started from `A₀ = {v}`, has not
infected any vertex of `C` at time `t` (`C ∩ A_t = ∅`). Both sides average over `t` i.i.d. rounds
in which every vertex samples `k` uniform neighbours with replacement. The paper assumes `G`
connected and regular and `k ≥ 1`; the statement holds for every finite graph and every `k`. -/
theorem cobra_bips_duality (v : V) (C : Finset V) (t : ℕ) :
    expList (Choices G k) t
        (fun l => if ∀ s ≤ t, v ∉ cobraRun C (l.take s) then 1 else 0) =
      expList (Choices G k) t (fun l => if C ∩ bipsRun v {v} l = ∅ then 1 else 0) := by
  conv_rhs => rw [← expList_comp_reverse]
  refine expList_congr_length t fun l hl => ?_
  have h : (∀ s ≤ t, v ∉ cobraRun C (l.take s)) ↔ C ∩ bipsRun v {v} l.reverse = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty, ← cobra_hit_iff_bips_reverse, hl]
    push Not
    rfl
  exact if_congr h rfl rfl

/-- **Equation (2)**, the case `C = {u}` of Theorem 4: `P(Hit_u(v) > t) = P(u ∉ A_t | A₀ = {v})`,
the form used to derive the COBRA cover time (Theorem 1) from the BIPS infection time
(Theorem 2). -/
theorem cobra_bips_duality_singleton (u v : V) (t : ℕ) :
    expList (Choices G k) t
        (fun l => if ∀ s ≤ t, v ∉ cobraRun {u} (l.take s) then 1 else 0) =
      expList (Choices G k) t (fun l => if u ∉ bipsRun v {v} l then 1 else 0) := by
  rw [cobra_bips_duality]
  simp only [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_singleton_left]

end Epidemics
