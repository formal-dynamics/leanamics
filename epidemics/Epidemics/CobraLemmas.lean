import Epidemics.Cobra

/-! # One-round lemmas for COBRA and BIPS (EPI-4)

Membership in one COBRA or BIPS round, the recursions of `cobraRun` and `bipsRun`, and the
unfolding of the COBRA hitting event "`v ∈ C_s` for some `s ≤ t`" over the first round.
-/

namespace Epidemics
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

omit [Fintype V] in
/-- A vertex is reached by a COBRA round from `D` iff some vertex of `D` sampled it. -/
lemma mem_cobraStep {D : Finset V} {r : Choices G k} {y : V} :
    y ∈ cobraStep D r ↔ ∃ x ∈ D, ∃ i, (r x i : V) = y := by
  simp [cobraStep]

/-- A vertex is infected after a BIPS round iff it is the source or sampled an infected vertex. -/
lemma mem_bipsStep {v : V} {A : Finset V} {r : Choices G k} {u : V} :
    u ∈ bipsStep v A r ↔ u = v ∨ ∃ i, (r u i : V) ∈ A := by
  simp [bipsStep]

omit [Fintype V] in
@[simp] lemma cobraRun_nil (C : Finset V) : cobraRun C ([] : List (Choices G k)) = C := rfl

omit [Fintype V] in
/-- COBRA after the rounds `r :: l` is COBRA from `cobraStep C r` after the rounds `l`. -/
@[simp] lemma cobraRun_cons (C : Finset V) (r : Choices G k) (l : List (Choices G k)) :
    cobraRun C (r :: l) = cobraRun (cobraStep C r) l := rfl

/-- BIPS after the rounds `l ++ [r]` is one more round `r` after the rounds `l`. -/
lemma bipsRun_append_singleton (v : V) (A₀ : Finset V) (l : List (Choices G k))
    (r : Choices G k) : bipsRun v A₀ (l ++ [r]) = bipsStep v (bipsRun v A₀ l) r := by
  simp [bipsRun]

omit [Fintype V] in
/-- The COBRA hitting event over the rounds `r :: l`: either `v` is in the start set, or COBRA
restarted from the first round's image hits `v` within the rounds `l`. -/
lemma hits_cons (v : V) (C : Finset V) (r : Choices G k) (l : List (Choices G k)) :
    (∃ s ≤ (r :: l).length, v ∈ cobraRun C ((r :: l).take s)) ↔
      v ∈ C ∨ ∃ s ≤ l.length, v ∈ cobraRun (cobraStep C r) (l.take s) := by
  constructor
  · rintro ⟨s, hs, hv⟩
    cases s with
    | zero => exact Or.inl (by simpa using hv)
    | succ s => exact Or.inr ⟨s, by simpa using hs, by simpa using hv⟩
  · rintro (hv | ⟨s, hs, hv⟩)
    · exact ⟨0, Nat.zero_le _, by simpa using hv⟩
    · exact ⟨s + 1, by simpa using hs, by simpa using hv⟩

end Epidemics
