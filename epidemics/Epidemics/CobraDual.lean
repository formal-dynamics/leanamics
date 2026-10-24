import Dynamics.DriftHittingStop
import Dynamics.Relations
import Dynamics.Rounds
import Epidemics.CobraDuality

/-! # COBRA ⇔ BIPS duality as a duality of kernels (EPI-4)

The dictionary relation `duality` is `Dynamics.Kernel.Dual H K L`, `𝔼_x[H(X₁, y)] = 𝔼_y[H(x, Y₁)]`,
which then holds at every time (`Dynamics.Kernel.Dual.iterate`). Theorem 4 of Cooper, Radzik and
Rivera (PODC 2016) is such a duality, for `H(C, A) = 1{C ∩ A = ∅}`, between

* COBRA stopped when it visits `v` (`cobraStopped v`, the stopped chain `Kernel.stopped` of the
  COBRA kernel): it avoids `v` up to time `t` iff `Hit_C(v) > t`;
* BIPS with persistent source `v` on the sets that contain `v` (`bipsKernel v`): BIPS starts from
  `{v}` and never loses `v`.

In one round both sides of the identity agree for every choice of neighbours
(`cobraStopStep_inter_eq_empty_iff`), so the kernels are dual (`cobra_bips_dual`) and the duality
holds at every time. With `A₀ = {v}` this is Theorem 4 with the hitting
probability of the COBRA kernel (`cobra_bips_duality_hitProb`), and it gives the statement
`cobra_bips_duality` back by the Markov property, without reversing the rounds
(`cobra_bips_duality_of_dual`). The kernels need a round of neighbour choices to exist
(`Nonempty (Choices G k)`, true on the connected graphs with at least two vertices of the paper,
`choices_nonempty`).
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- One BIPS round with persistent source `v`, on the sets that contain `v`. -/
def bipsSourceStep (v : V) (A : {A : Finset V // v ∈ A}) (r : Choices G k) :
    {A : Finset V // v ∈ A} :=
  ⟨bipsStep v A.1 r, mem_insert_self v _⟩

/-- One COBRA round, stopped once `v` has been visited. -/
def cobraStopStep (v : V) (C : Finset V) (r : Choices G k) : Finset V :=
  if v ∈ C then C else cobraStep C r

variable [Nonempty (Choices G k)]

/-- COBRA stopped when it visits `v`: the stopped chain of the COBRA kernel on sets of vertices. -/
noncomputable def cobraStopped (v : V) : Kernel (Finset V) :=
  (Kernel.ofStep (cobraStep (G := G) (k := k))).stopped fun C => v ∈ C

/-- BIPS with persistent source `v`, as a kernel on the sets that contain `v`. -/
noncomputable def bipsKernel (v : V) : Kernel {A : Finset V // v ∈ A} :=
  Kernel.ofStep (bipsSourceStep (G := G) (k := k) v)

omit [DecidableRel G.Adj] [Nonempty (Choices G k)] in
/-- **One round of the duality, pathwise.** If `v ∈ A`, then for every round `r`, COBRA stopped at
`v` from `C` avoids `A` after `r` iff `C` avoids BIPS from `A` after `r`. -/
lemma cobraStopStep_inter_eq_empty_iff {v : V} (C : Finset V) {A : Finset V} (hA : v ∈ A)
    (r : Choices G k) : cobraStopStep v C r ∩ A = ∅ ↔ C ∩ bipsStep v A r = ∅ := by
  simp only [← disjoint_iff_inter_eq_empty, disjoint_left, mem_bipsStep]
  by_cases hv : v ∈ C
  · simp only [cobraStopStep, if_pos hv]
    exact ⟨fun h => absurd hA (h hv), fun h => absurd (Or.inl rfl) (h hv)⟩
  · simp only [cobraStopStep, if_neg hv, mem_cobraStep]
    constructor
    · rintro h u hu (rfl | ⟨i, hi⟩)
      · exact hv hu
      · exact h ⟨u, hu, i, rfl⟩ hi
    · rintro h y ⟨x, hx, i, rfl⟩ hy
      exact h hx (Or.inr ⟨i, hy⟩)

/-- The stopped COBRA kernel is the kernel of the stopped round `cobraStopStep`. -/
lemma cobraStopped_eq_ofStep (v : V) :
    cobraStopped (G := G) (k := k) v = Kernel.ofStep (cobraStopStep (G := G) (k := k) v) := by
  funext C
  by_cases hv : v ∈ C
  · rw [cobraStopped, Kernel.stopped_of_mem (B := fun D => v ∈ D) _ hv]
    refine Distribution.ext_expect fun f => ?_
    simp only [Kernel.ofStep, Distribution.map_expect, Distribution.point_expect, cobraStopStep,
      if_pos hv, Distribution.expect_const]
  · rw [cobraStopped, Kernel.stopped_of_not_mem (B := fun D => v ∈ D) _ hv]
    have h : cobraStopStep (G := G) (k := k) v C = cobraStep C := funext fun r => if_neg hv
    simp only [Kernel.ofStep, h]

/-- **COBRA ⇔ BIPS duality (Theorem 4) as a duality of kernels.** COBRA stopped when it visits `v`
and BIPS with persistent source `v` are dual with respect to `H(C, A) = 1{C ∩ A = ∅}`:
`𝔼_C[H(C₁, A)] = 𝔼_A[H(C, A₁)]` for every set `C` and every set `A ∋ v`. -/
theorem cobra_bips_dual (v : V) :
    Kernel.Dual (fun C (A : {A : Finset V // v ∈ A}) => if C ∩ A.1 = ∅ then (1 : ℝ) else 0)
      (cobraStopped (G := G) (k := k) v) (bipsKernel (G := G) (k := k) v) := fun C A => by
  rw [cobraStopped_eq_ofStep, bipsKernel, Kernel.apply_ofStep, Kernel.apply_ofStep]
  exact congrArg avg (funext fun r => if_congr (cobraStopStep_inter_eq_empty_iff C A.2 r) rfl rfl)

/-- **Theorem 4 with hitting probabilities.** For every vertex `v`, set `C` and time `t`, the
probability that the COBRA kernel started from `C` has not visited `v` by time `t`,
`1 - P_C(Hit_C(v) ≤ t)`, equals the probability that BIPS with source `v` started from `{v}` has
not infected any vertex of `C` at time `t`. -/
theorem cobra_bips_duality_hitProb (v : V) (C : Finset V) (t : ℕ) :
    1 - (Kernel.ofStep (cobraStep (G := G) (k := k))).hitProb (fun D => v ∈ D) t C =
      (bipsKernel (G := G) (k := k) v).iterate t
        (fun A => if C ∩ A.1 = ∅ then (1 : ℝ) else 0) ⟨{v}, mem_singleton_self v⟩ := by
  classical
  rw [Kernel.one_sub_hitProb_eq_event_stopped, ← (cobra_bips_dual v).iterate t C,
    Kernel.event_eq_iterate]
  refine congrFun (congrArg _ (funext fun D => if_congr ?_ rfl rfl)) C
  rw [← disjoint_iff_inter_eq_empty, disjoint_singleton_right]

omit [Fintype V] [DecidableRel G.Adj] [Nonempty (Choices G k)] in
/-- Stopped COBRA has not visited `v` after the rounds `l` iff COBRA has not visited `v` at any
time `s ≤ l.length`. -/
lemma not_mem_foldl_cobraStopStep (v : V) (C : Finset V) (l : List (Choices G k)) :
    v ∉ l.foldl (cobraStopStep v) C ↔ ∀ s ≤ l.length, v ∉ cobraRun C (l.take s) := by
  induction l generalizing C with
  | nil => simp [cobraRun]
  | cons r l ih =>
    have hstop (D : Finset V) (hD : v ∈ D) (l' : List (Choices G k)) :
        l'.foldl (cobraStopStep v) D = D := by
      induction l' with
      | nil => rfl
      | cons r' l' ih' => rw [List.foldl_cons, cobraStopStep, if_pos hD, ih']
    have hcons := hits_cons v C r l
    rw [List.foldl_cons]
    by_cases hv : v ∈ C
    · rw [cobraStopStep, if_pos hv, hstop C hv]
      constructor
      · exact fun h => absurd hv h
      · intro h
        exact absurd hv (by simpa [cobraRun] using h 0 (Nat.zero_le _))
    · rw [cobraStopStep, if_neg hv, ih]
      constructor
      · intro h s hs hmem
        rcases hcons.1 ⟨s, hs, hmem⟩ with hC | ⟨s', hs', hmem'⟩
        · exact hv hC
        · exact h s' hs' hmem'
      · intro h s hs hmem
        exact h (s + 1) (by simpa using hs) (by simpa [cobraRun] using hmem)

omit [DecidableRel G.Adj] [Nonempty (Choices G k)] in
/-- BIPS on the sets that contain `v` runs as `bipsRun`. -/
lemma foldl_bipsSourceStep (v : V) (A : {A : Finset V // v ∈ A}) (l : List (Choices G k)) :
    (l.foldl (bipsSourceStep v) A).1 = bipsRun v A.1 l := by
  induction l generalizing A with
  | nil => rfl
  | cons r l ih => rw [List.foldl_cons, ih]; rfl

/-- **Theorem 4 again, from the duality of kernels.** The statement `cobra_bips_duality`, under
`Nonempty (Choices G k)`, derived from the one-round duality `cobra_bips_dual` by
`Dynamics.Kernel.Dual.iterate` (the Markov property) instead of the reversal of the rounds. -/
theorem cobra_bips_duality_of_dual (v : V) (C : Finset V) (t : ℕ) :
    expList (Choices G k) t
        (fun l => if ∀ s ≤ t, v ∉ cobraRun C (l.take s) then 1 else 0) =
      expList (Choices G k) t (fun l => if C ∩ bipsRun v {v} l = ∅ then 1 else 0) := by
  have h := (cobra_bips_dual (G := G) (k := k) v).iterate t C ⟨{v}, mem_singleton_self v⟩
  rw [cobraStopped_eq_ofStep, bipsKernel, Kernel.iterate_ofStep, Kernel.iterate_ofStep] at h
  simp only [foldl_bipsSourceStep] at h
  rw [← h]
  refine Dynamics.expList_congr_length fun l hl => if_congr ?_ rfl rfl
  rw [← disjoint_iff_inter_eq_empty, disjoint_singleton_right, not_mem_foldl_cobraStopStep, hl]

end Epidemics
