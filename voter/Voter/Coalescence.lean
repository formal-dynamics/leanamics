import Voter.Absorption
import Dynamics.Uniform

/-! # Coalescing random walks and consensus time on the complete graph (VOT-3)

Hassin–Peleg §2.4 and Survey Theorems 6–7, on the complete graph with self-loops
(Wright–Fisher sampling): in every round each vertex copies the colour of a uniformly random
vertex, itself included.

*Duality.* After rounds `r₁, …, r_T` the colour of `u` is `s (r₁ (r₂ (⋯ (r_T u))))`: running
the voter forward reads the initial colours through the backward map `r₁ ∘ ⋯ ∘ r_T`, whose
point images are coalescing random walks. Consensus holds as soon as the backward map is
constant.

*Time.* Backward walks from two distinct vertices have not met after `T` rounds with
probability exactly `(1 - 1/n)^T`. A union bound over the walks that must meet the walk of a
fixed vertex gives consensus within `2 n log n` rounds with probability at least `1 - 1/n`.
-/

namespace Voter
open Dynamics Finset

variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- Run the synchronous voter along a list of rounds, first round first. -/
def runRounds (s : Config V C) : List (V → V) → Config V C
  | [] => s
  | r :: l => runRounds (step s r) l

/-- The backward map `r₁ ∘ r₂ ∘ ⋯ ∘ r_T` of the rounds `[r₁, …, r_T]`. -/
def backward (l : List (V → V)) : V → V := l.foldr (fun r g => r ∘ g) id

/-- Nonconsensus indicator for an arbitrary colour type. -/
noncomputable def disagreement (s : Config V C) : ℝ := by
  classical
  exact if ∃ c, s = fun _ => c then 0 else 1

/-- Wright–Fisher sampling: every vertex picks a uniformly random vertex, itself included. -/
noncomputable def wfKernel (V : Type*) [Fintype V] [Nonempty V] : Kernel V :=
  fun _ => Distribution.uniform V

omit [Fintype V] [DecidableEq V] in
lemma backward_nil : backward ([] : List (V → V)) = id := rfl

omit [Fintype V] [DecidableEq V] in
lemma backward_cons (r : V → V) (l : List (V → V)) :
    backward (r :: l) = r ∘ backward l := rfl

omit [Fintype V] [DecidableEq V] in
lemma disagreement_le_one (s : Config V C) : disagreement s ≤ 1 := by
  classical
  unfold disagreement
  split <;> norm_num

/-- Probability that two distinct coordinates of a uniform random map `V → V` agree. -/
lemma avg_maps_agree (a b : V) (hab : a ≠ b) :
    avg (fun r : V → V => if r a = r b then (1 : ℝ) else 0) =
      1 / (Fintype.card V : ℝ) := by
  haveI : Nonempty V := ⟨a⟩
  let W := {j // j ≠ a}
  let b' : W := ⟨b, hab.symm⟩
  -- Transparent so `(e r).1 = r a` and `(e r).2 ⟨b, _⟩ = r b` are definitional.
  let e : (V → V) ≃ V × (W → V) :=
    { toFun := fun r => (r a, fun j => r j)
      invFun := fun p j => if h : j = a then p.1 else p.2 ⟨j, h⟩
      left_inv := fun r => by
        funext j
        by_cases h : j = a <;> simp [h]
      right_inv := fun p => by
        apply Prod.ext
        · simp
        · funext j
          simp [j.prop] }
  have hcomp :
      (fun r : V → V => if r a = r b then (1 : ℝ) else 0) =
        fun r => (fun p : V × (W → V) => if p.1 = p.2 b' then (1 : ℝ) else 0) (e r) := by
    funext r
    rfl
  have havg := avg_equiv e (fun p : V × (W → V) => if p.1 = p.2 b' then (1 : ℝ) else 0)
  rw [hcomp, havg]
  unfold avg
  rw [Fintype.card_prod, Nat.cast_mul]
  have hsum :
      (∑ p : V × (W → V), if p.1 = p.2 b' then (1 : ℝ) else 0) =
        (Fintype.card (W → V) : ℝ) := by
    -- Sum the copied value first: for each fixed rest-function exactly one value agrees.
    rw [Fintype.sum_prod_type_right]
    simp_rw [Fintype.sum_ite_eq']
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum, mul_comm (Fintype.card V : ℝ)]
  have hc : (Fintype.card (W → V) : ℝ) ≠ 0 := by
    haveI : Nonempty (W → V) := ⟨fun _ => a⟩
    exact ne_of_gt (card_cast_pos (α := W → V))
  calc
    (Fintype.card (W → V) : ℝ) / (Fintype.card (W → V) * Fintype.card V)
        = (Fintype.card (W → V) * 1) / (Fintype.card (W → V) * Fintype.card V) := by
          rw [mul_one]
    _ = 1 / (Fintype.card V : ℝ) := mul_div_mul_left 1 (Fintype.card V : ℝ) hc

/-- One-step probability that the images of two vertices under a uniform round differ. -/
lemma avg_coord_disagree (a b : V) :
    avg (fun r : V → V => if r a = r b then (0 : ℝ) else 1) =
      if a = b then 0 else 1 - 1 / (Fintype.card V : ℝ) := by
  by_cases hab : a = b
  · haveI : Nonempty V := ⟨a⟩
    haveI : Nonempty (V → V) := ⟨fun _ => a⟩
    subst hab
    have hfun : (fun r : V → V => if r a = r a then (0 : ℝ) else 1) = fun _ => (0 : ℝ) := by
      funext r
      simp
    rw [hfun, avg_const]
    simp
  · haveI : Nonempty V := ⟨a⟩
    haveI : Nonempty (V → V) := ⟨fun _ => a⟩
    have hfun :
        (fun r : V → V => if r a = r b then (0 : ℝ) else 1) =
          fun r => (1 : ℝ) - if r a = r b then 1 else 0 := by
      funext r
      by_cases h : r a = r b <;> simp [h]
    rw [hfun, avg_sub, avg_const, avg_maps_agree a b hab, if_neg hab]

/-- The independent Wright–Fisher round is uniform on the whole map space. -/
lemma independent_wfKernel_expect [Nonempty V] (g : (V → V) → ℝ) :
    (Distribution.independent (wfKernel V)).expect g = avg g := by
  have hw (r : V → V) :
      (Distribution.independent (wfKernel V)).weight r =
        (Fintype.card (V → V) : ℝ)⁻¹ := by
    dsimp [Distribution.independent, wfKernel, Distribution.uniform]
    rw [Finset.prod_const, Finset.card_univ, inv_pow]
    apply congrArg Inv.inv
    rw [Fintype.card_fun]
    norm_cast
  simp_rw [Distribution.expect, hw, ← Finset.mul_sum]
  rw [avg, div_eq_mul_inv, mul_comm]

/-- Meeting indicator for an arbitrary pair, including the diagonal (value `0`). -/
lemma expList_backward_indicator (x y : V) (T : ℕ) :
    expList (V → V) T (fun l => if backward l x = backward l y then (0 : ℝ) else 1) =
      if x = y then 0 else (1 - 1 / (Fintype.card V : ℝ)) ^ T := by
  induction T generalizing x y with
  | zero =>
    simp only [expList_zero, backward, List.foldr_nil, pow_zero]
    by_cases h : x = y <;> simp [h]
  | succ T ih =>
    rw [expList_succ]
    have hfun :
        (fun r : V → V => expList (V → V) T fun l =>
            if backward (r :: l) x = backward (r :: l) y then (0 : ℝ) else 1) =
          fun r => expList (V → V) T fun l =>
            if r (backward l x) = r (backward l y) then (0 : ℝ) else 1 := by
      funext r
      refine congrArg (expList (V → V) T) ?_
      funext l
      rw [backward_cons]
      rfl
    rw [hfun, expList_avg_comm]
    have hscale (l : List (V → V)) :
        (if backward l x = backward l y then (0 : ℝ)
          else 1 - 1 / (Fintype.card V : ℝ)) =
          (1 - 1 / (Fintype.card V : ℝ)) *
            (if backward l x = backward l y then 0 else 1) := by
      by_cases h : backward l x = backward l y <;> simp [h]
    simp_rw [avg_coord_disagree, hscale, expList_const_mul, ih]
    by_cases hxy : x = y
    · simp [hxy]
    · rw [if_neg hxy, if_neg hxy, ← pow_succ']

omit [Fintype V] [DecidableEq V] in
/-- **Duality.** Running the voter forward reads the initial colours through the backward map. -/
theorem runRounds_eq_comp (s : Config V C) (l : List (V → V)) :
    runRounds s l = s ∘ backward l := by
  induction l generalizing s with
  | nil => simp [runRounds, backward]
  | cons r l ih =>
    rw [runRounds, ih]
    ext u
    simp [step, backward_cons]

omit [Fintype V] [DecidableEq V] in
/-- A constant backward map forces consensus. -/
theorem disagreement_runRounds_eq_zero [Nonempty V] (s : Config V C) (l : List (V → V))
    (h : ∀ u v, backward l u = backward l v) : disagreement (runRounds s l) = 0 := by
  classical
  rw [runRounds_eq_comp]
  obtain ⟨u₀⟩ := ‹Nonempty V›
  unfold disagreement
  exact if_pos ⟨s (backward l u₀), funext fun v => congrArg s (h v u₀)⟩

omit [DecidableEq V] in
/-- For Boolean colours, `disagreement` is the survival indicator of `Voter.Absorption`. -/
theorem disagreement_eq_survival (s : Config V Bool) : disagreement s = survival s := by
  unfold disagreement survival
  by_cases h : ∃ c, s = fun _ => c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The configuration kernel of Wright–Fisher sampling is the average over `T` i.i.d.
uniform rounds. -/
theorem iterate_wfKernel_eq_expList [Nonempty V] [Fintype C] (f : Config V C → ℝ) (T : ℕ)
    (s : Config V C) :
    (transition (wfKernel V)).iterate T f s =
      expList (V → V) T (fun l => f (runRounds s l)) := by
  induction T generalizing s with
  | zero => simp [runRounds]
  | succ T ih =>
    rw [Kernel.iterate_succ, transition_apply, expList_succ]
    unfold round
    simp_rw [show ∀ r l, runRounds s (r :: l) = runRounds (step s r) l from fun _ _ => rfl, ← ih]
    exact independent_wfKernel_expect
      (fun r => (transition (wfKernel V)).iterate T f (step s r))

/-- **Meeting probability.** Backward walks from distinct vertices have not met after `T`
rounds with probability exactly `(1 - 1/n)^T`. -/
theorem expList_backward_ne {u v : V} (huv : u ≠ v) (T : ℕ) :
    expList (V → V) T (fun l => if backward l u = backward l v then 0 else 1) =
      (1 - 1 / (Fintype.card V : ℝ)) ^ T := by
  simpa [huv] using expList_backward_indicator u v T

/-- Pointwise, nonconsensus is bounded by the walks that have not met a fixed vertex. -/
lemma disagreement_runRounds_le (s : Config V C) (l : List (V → V)) (u₀ : V) :
    disagreement (runRounds s l) ≤
      ∑ v ∈ univ.erase u₀, if backward l v = backward l u₀ then (0 : ℝ) else 1 := by
  classical
  haveI : Nonempty V := ⟨u₀⟩
  by_cases h : ∀ v ∈ univ.erase u₀, backward l v = backward l u₀
  · have hconst : ∀ u v, backward l u = backward l v := by
      intro u v
      have key (w : V) : backward l w = backward l u₀ := by
        by_cases hw : w = u₀
        · rw [hw]
        · exact h w (mem_erase.mpr ⟨hw, mem_univ w⟩)
      exact (key u).trans (key v).symm
    rw [disagreement_runRounds_eq_zero s l hconst]
    exact Finset.sum_nonneg fun _ _ => by split <;> norm_num
  · push Not at h
    obtain ⟨v, hv, hne⟩ := h
    have hnonneg : ∀ w ∈ univ.erase u₀,
        0 ≤ (if backward l w = backward l u₀ then (0 : ℝ) else 1) := by
      intro _ _
      split <;> norm_num
    have hterm : (if backward l v = backward l u₀ then (0 : ℝ) else 1) = 1 := by
      simp [hne]
    have hone : (1 : ℝ) ≤ ∑ w ∈ univ.erase u₀,
        if backward l w = backward l u₀ then (0 : ℝ) else 1 := by
      calc
        (1 : ℝ) = if backward l v = backward l u₀ then 0 else 1 := hterm.symm
        _ ≤ ∑ w ∈ univ.erase u₀, if backward l w = backward l u₀ then 0 else 1 :=
          Finset.single_le_sum hnonneg hv
    exact (disagreement_le_one (runRounds s l)).trans hone

/-- **Consensus time, union bound.** -/
theorem iterate_disagreement_le [Nonempty V] [Fintype C] (s : Config V C) (T : ℕ) :
    (transition (wfKernel V)).iterate T disagreement s ≤
      ((Fintype.card V : ℝ) - 1) * (1 - 1 / (Fintype.card V : ℝ)) ^ T := by
  obtain ⟨u₀⟩ := ‹Nonempty V›
  rw [iterate_wfKernel_eq_expList]
  refine le_trans (expList_le_expList (fun l => disagreement_runRounds_le s l u₀)) ?_
  rw [expList_finset_sum]
  have hterm : ∀ v ∈ univ.erase u₀,
      expList (V → V) T (fun l => if backward l v = backward l u₀ then (0 : ℝ) else 1) =
        (1 - 1 / (Fintype.card V : ℝ)) ^ T := by
    intro v hv
    exact expList_backward_ne (mem_erase.mp hv).1 T
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (mem_univ u₀), Finset.card_univ,
    Nat.cast_sub (Nat.succ_le_of_lt (Fintype.card_pos (α := V))), Nat.cast_one]

/-- **Consensus within `2 n log n` rounds with probability at least `1 - 1/n`.** -/
theorem voter_consensus_whp [Nonempty V] [Fintype C] (s : Config V C) (T : ℕ)
    (hT : 2 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ (T : ℝ)) :
    (transition (wfKernel V)).iterate T disagreement s ≤ 1 / (Fintype.card V : ℝ) := by
  let n : ℝ := Fintype.card V
  have hn_pos : 0 < n := card_cast_pos
  have hn_ge : 1 ≤ n := by
    have hcard : (1 : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := V))
    simpa [n] using hcard
  have hbase : 0 ≤ 1 - 1 / n :=
    sub_nonneg.mpr ((div_le_one hn_pos).mpr hn_ge)
  have hpow : (1 - 1 / n) ^ T ≤ Real.exp (-((T : ℝ) / n)) := by
    calc
      (1 - 1 / n) ^ T ≤ Real.exp (-(1 / n)) ^ T :=
        pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (1 / n)) T
      _ = Real.exp (↑T * -(1 / n)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (-(↑T / n)) := by
        congr 1
        ring
  have hrate : Real.exp (-((T : ℝ) / n)) ≤ Real.exp (-(2 * Real.log n)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_le_neg_iff, le_div_iff₀ hn_pos]
    have hT' : 2 * n * Real.log n ≤ (T : ℝ) := by simpa [n] using hT
    calc
      2 * Real.log n * n = 2 * n * Real.log n := by ring
      _ ≤ (T : ℝ) := hT'
  have hexp : Real.exp (-(2 * Real.log n)) = 1 / n ^ 2 := by
    have hrewrite : -(2 * Real.log n) = Real.log n * (-2) := by ring
    have hsq : n ^ (2 : ℝ) = n ^ 2 := by
      rw [Real.rpow_def_of_pos hn_pos,
        show Real.log n * (2 : ℝ) = Real.log n + Real.log n by ring, Real.exp_add,
        Real.exp_log hn_pos]
      ring
    rw [hrewrite, Real.exp_mul, Real.exp_log hn_pos, Real.rpow_neg (le_of_lt hn_pos) (2 : ℝ),
      hsq, inv_eq_one_div]
  have htail : (n - 1) * (1 / n ^ 2) ≤ 1 / n := by
    rw [mul_one_div, div_le_div_iff₀ (pow_pos hn_pos 2) hn_pos]
    calc
      (n - 1) * n ≤ n * n :=
        mul_le_mul_of_nonneg_right (sub_le_self n zero_le_one) (le_of_lt hn_pos)
      _ = 1 * n ^ 2 := by ring
  calc
    (transition (wfKernel V)).iterate T disagreement s
        ≤ (n - 1) * (1 - 1 / n) ^ T := by
          simpa [n] using iterate_disagreement_le (V := V) (C := C) s T
    _ ≤ (n - 1) * Real.exp (-((T : ℝ) / n)) :=
          mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hn_ge)
    _ ≤ (n - 1) * Real.exp (-(2 * Real.log n)) :=
          mul_le_mul_of_nonneg_left hrate (sub_nonneg.mpr hn_ge)
    _ = (n - 1) * (1 / n ^ 2) := by rw [hexp]
    _ ≤ 1 / n := htail

end Voter
