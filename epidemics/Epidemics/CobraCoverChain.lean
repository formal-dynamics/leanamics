import Epidemics.CobraCoverGrowth
import Epidemics.CobraLemmas
import Dynamics.Uniform

/-! # Chaining one-round phases (EPI-4, Theorems 1 and 2)

A first-hit bound for a round-driven process, and the geometric estimate for a tail that
contracts every `T₀` steps. The BIPS and COBRA theorems instantiate both.
-/

namespace Epidemics
open Finset Dynamics

variable {S R : Type*} [Fintype R] [Nonempty R]

omit [Nonempty R] in
/-- `expList` only evaluates lists of length `T`, so a comparison on those lists is enough. -/
lemma expList_le_of_length {T : ℕ} {F G : List R → ℝ}
    (h : ∀ l, l.length = T → F l ≤ G l) : expList R T F ≤ expList R T G := by
  induction T generalizing F G with
  | zero => exact h [] rfl
  | succ T ih =>
    rw [expList_succ, expList_succ]
    refine avg_le_avg fun a => ?_
    exact ih fun l hl => h (a :: l) (by simp [hl])

lemma expList_fail_le_one (T : ℕ) (P : List R → Prop) [DecidablePred P] :
    expList R T (fun l => if P l then (0 : ℝ) else 1) ≤ 1 := by
  refine (expList_le_expList (G := fun _ => (1 : ℝ)) fun l => ?_).trans_eq (expList_const T 1)
  by_cases h : P l
  · rw [if_pos h]; norm_num
  · rw [if_neg h]

omit [Fintype R] [Nonempty R] in
/-- Stepping once: avoiding `P` for `T₁ + 1` steps from `a`, when `a` itself misses `P`, is
avoiding `P` for `T₁` steps from `step a ρ`. -/
lemma forall_not_cons (step : S → R → S) (P : S → Prop) (a : S) (ρ : R) (l : List R) {T₁ : ℕ}
    (hP : ¬ P a) :
    (∀ s ≤ T₁ + 1, ¬ P (((ρ :: l).take s).foldl step a)) ↔
      ∀ t ≤ T₁, ¬ P ((l.take t).foldl step (step a ρ)) := by
  constructor
  · intro h t ht
    have := h (t + 1) (Nat.succ_le_succ ht)
    simpa [List.take_succ_cons, List.foldl_cons] using this
  · intro h s hs
    cases s with
    | zero => simpa [List.take_zero, List.foldl_nil] using hP
    | succ t =>
      have ht : t ≤ T₁ := Nat.succ_le_succ_iff.mp hs
      simpa [List.take_succ_cons, List.foldl_cons] using h t ht

/-- If every state satisfying `P` reaches `Q` within `T₂` steps except with probability `ε`,
and the same bound holds for every longer horizon, then from an arbitrary start the failure
probability after `T₁ + T₂'` steps is at most the probability of avoiding `P` for `T₁` steps,
plus `ε`. -/
lemma round_first_hit (step : S → R → S) (P Q : S → Prop) [DecidablePred P] [DecidablePred Q]
    {T₂ : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ b, P b → ∀ T', T₂ ≤ T' →
      expList R T' (fun l => if Q (l.foldl step b) then (0 : ℝ) else 1) ≤ ε)
    (a : S) (T₁ T₂' : ℕ) (hT : T₂ ≤ T₂') :
    expList R (T₁ + T₂') (fun l => if Q (l.foldl step a) then (0 : ℝ) else 1) ≤
      expList R T₁ (fun l =>
        if ∀ s ≤ T₁, ¬ P ((l.take s).foldl step a) then (1 : ℝ) else 0) + ε := by
  induction T₁ generalizing a with
  | zero =>
    simp only [Nat.zero_add, expList_zero]
    by_cases hP : P a
    · have hnever : ¬ ∀ s ≤ 0, ¬ P (([].take s).foldl step a) := by
        intro h
        exact h 0 le_rfl (by simpa [List.take_zero, List.foldl_nil] using hP)
      rw [if_neg hnever]
      exact (hgood a hP T₂' hT).trans (by norm_num : ε ≤ 0 + ε)
    · rw [if_pos]
      · exact le_add_of_le_of_nonneg (expList_fail_le_one T₂' (fun l => Q (l.foldl step a))) hε
      · intro s hs
        have hs0 : s = 0 := by omega
        simpa [hs0, List.take_zero, List.foldl_nil] using hP
  | succ T₁ ih =>
    have htime : (T₁ + 1) + T₂' = (T₁ + T₂') + 1 := by omega
    by_cases hP : P a
    · rw [htime]
      have hle := hgood a hP ((T₁ + T₂') + 1) (by omega)
      have hnn : 0 ≤ expList R (T₁ + 1) (fun l =>
          if ∀ s ≤ T₁ + 1, ¬ P ((l.take s).foldl step a) then (1 : ℝ) else 0) :=
        expList_nonneg fun l => by
          by_cases h : ∀ s ≤ T₁ + 1, ¬ P ((l.take s).foldl step a)
          · rw [if_pos h]; norm_num
          · rw [if_neg h]
      linarith
    · rw [htime, expList_succ]
      have hchild : ∀ ρ, expList R (T₁ + T₂')
          (fun l => if Q ((ρ :: l).foldl step a) then (0 : ℝ) else 1) ≤
          expList R T₁ (fun l =>
            if ∀ s ≤ T₁, ¬ P ((l.take s).foldl step (step a ρ)) then (1 : ℝ) else 0) + ε := by
        intro ρ
        have hfun : (fun l => if Q ((ρ :: l).foldl step a) then (0 : ℝ) else 1) =
            fun l => if Q (l.foldl step (step a ρ)) then (0 : ℝ) else 1 := by
          funext l
          simp [List.foldl_cons]
        rw [hfun]
        exact ih (step a ρ)
      have havg := avg_le_avg hchild
      rw [avg_add, avg_const] at havg
      have hparent : avg (fun ρ => expList R T₁ (fun l =>
          if ∀ s ≤ T₁, ¬ P ((l.take s).foldl step (step a ρ)) then (1 : ℝ) else 0)) =
          expList R (T₁ + 1) (fun l =>
            if ∀ s ≤ T₁ + 1, ¬ P ((l.take s).foldl step a) then (1 : ℝ) else 0) := by
        rw [expList_succ]
        refine congrArg avg (funext fun ρ => ?_)
        refine congrArg (expList R T₁) (funext fun l => ?_)
        exact if_congr (forall_not_cons step P a ρ l hP).symm rfl rfl
      exact havg.trans_eq (by rw [hparent])

lemma geom_partial_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (q : ℕ) :
    ∑ j ∈ range q, ε ^ j ≤ 1 / (1 - ε) := by
  have hne : ε ≠ 1 := ne_of_lt hε1
  rw [geom_sum_eq hne]
  have hden : (0 : ℝ) < 1 - ε := by linarith
  have heq : (ε ^ q - 1) / (ε - 1) = (1 - ε ^ q) / (1 - ε) := by
    have hsub : ε - 1 = -(1 - ε) := by ring
    have hpow : ε ^ q - 1 = -(1 - ε ^ q) := by ring
    rw [hsub, hpow, neg_div_neg_eq]
  rw [heq]
  have hnum : 1 - ε ^ q ≤ 1 := by
    have : 0 ≤ ε ^ q := pow_nonneg hε0 q
    linarith
  exact div_le_div_of_nonneg_right hnum hden.le

lemma sum_range_add {m n : ℕ} (f : ℕ → ℝ) :
    ∑ s ∈ range (m + n), f s = ∑ s ∈ range m, f s + ∑ s ∈ range n, f (m + s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma iterate_shift {a : ℕ → ℝ} {T₀ : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hshift : ∀ s, a (s + T₀) ≤ ε * a s) : ∀ q r, a (q * T₀ + r) ≤ ε ^ q * a r := by
  intro q
  induction q with
  | zero => intro r; simp
  | succ q ih =>
    intro r
    have heq : (q + 1) * T₀ + r = q * T₀ + r + T₀ := by ring
    rw [heq]
    calc a (q * T₀ + r + T₀) ≤ ε * a (q * T₀ + r) := hshift _
      _ ≤ ε * (ε ^ q * a r) := mul_le_mul_of_nonneg_left (ih r) hε0
      _ = ε ^ (q + 1) * a r := by ring

/-- If `0 ≤ a s ≤ 1` and `a (s + T₀) ≤ ε a s` with `0 ≤ ε < 1`, every partial sum is at most
`T₀ / (1 - ε)`. -/
lemma sum_range_shift_le {a : ℕ → ℝ} {T₀ : ℕ} {ε : ℝ} (hT : 0 < T₀) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h0 : ∀ s, 0 ≤ a s) (h1 : ∀ s, a s ≤ 1) (hshift : ∀ s, a (s + T₀) ≤ ε * a s) (H : ℕ) :
    ∑ s ∈ range H, a s ≤ (T₀ : ℝ) / (1 - ε) := by
  have hden : (0 : ℝ) < 1 - ε := by linarith
  let q := H / T₀
  let r := H % T₀
  have hdiv : q * T₀ + r = H := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod H T₀
  have hr : r < T₀ := Nat.mod_lt H hT
  have hrle : r ≤ T₀ := le_of_lt hr
  have hsplit : ∑ s ∈ range H, a s =
      ∑ s ∈ range (q * T₀), a s + ∑ i ∈ range r, a (q * T₀ + i) := by
    have hraw := sum_range_add (m := q * T₀) (n := r) a
    rwa [hdiv] at hraw
  have hblock : ∀ p, ∑ s ∈ range (p * T₀), a s ≤
      (∑ t ∈ range T₀, a t) * ∑ j ∈ range p, ε ^ j := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      have hadd : (p + 1) * T₀ = p * T₀ + T₀ := by ring
      rw [hadd, sum_range_add]
      have htail : ∑ i ∈ range T₀, a (p * T₀ + i) ≤ ε ^ p * ∑ t ∈ range T₀, a t := by
        have hpt : ∀ i ∈ range T₀, a (p * T₀ + i) ≤ ε ^ p * a i := fun i _ =>
          iterate_shift hε0 hshift p i
        have hsum := Finset.sum_le_sum hpt
        rwa [← Finset.mul_sum] at hsum
      calc ∑ s ∈ range (p * T₀), a s + ∑ i ∈ range T₀, a (p * T₀ + i)
          ≤ (∑ t ∈ range T₀, a t) * ∑ j ∈ range p, ε ^ j +
              ε ^ p * ∑ t ∈ range T₀, a t := add_le_add ih htail
        _ = (∑ t ∈ range T₀, a t) * ∑ j ∈ range (p + 1), ε ^ j := by
            rw [Finset.sum_range_succ]; ring
  have hrest : ∑ i ∈ range r, a (q * T₀ + i) ≤ ε ^ q * ∑ t ∈ range T₀, a t := by
    have hpt : ∀ i ∈ range r, a (q * T₀ + i) ≤ ε ^ q * a i := fun i _ =>
      iterate_shift hε0 hshift q i
    have hsum := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum] at hsum
    have hsub : ∑ i ∈ range r, a i ≤ ∑ t ∈ range T₀, a t := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrle) fun t _ ht => ?_
      exact h0 t
    have hmul := mul_le_mul_of_nonneg_left hsub (pow_nonneg hε0 q)
    exact le_trans hsum hmul
  have hsum1 : ∑ t ∈ range T₀, a t ≤ T₀ := by
    have hle := Finset.sum_le_sum fun t (_ : t ∈ range T₀) => h1 t
    have hconst : ∑ t ∈ range T₀, (1 : ℝ) = T₀ := by simp
    exact le_trans hle (le_of_eq hconst)
  have hpos : 0 ≤ ∑ t ∈ range T₀, a t := Finset.sum_nonneg fun t _ => h0 t
  have hgeom := geom_partial_le hε0 hε1 (q + 1)
  rw [hsplit]
  have htot : ∑ s ∈ range (q * T₀), a s + ∑ i ∈ range r, a (q * T₀ + i) ≤
      (∑ t ∈ range T₀, a t) * ∑ j ∈ range (q + 1), ε ^ j := by
    calc ∑ s ∈ range (q * T₀), a s + ∑ i ∈ range r, a (q * T₀ + i)
        ≤ (∑ t ∈ range T₀, a t) * ∑ j ∈ range q, ε ^ j + ε ^ q * ∑ t ∈ range T₀, a t :=
          add_le_add (hblock q) hrest
      _ = (∑ t ∈ range T₀, a t) * ∑ j ∈ range (q + 1), ε ^ j := by
          rw [Finset.sum_range_succ]; ring
  have hmul := mul_le_mul_of_nonneg_left hgeom hpos
  calc ∑ s ∈ range (q * T₀), a s + ∑ i ∈ range r, a (q * T₀ + i)
      ≤ (∑ t ∈ range T₀, a t) * ∑ j ∈ range (q + 1), ε ^ j := htot
    _ ≤ (∑ t ∈ range T₀, a t) * (1 / (1 - ε)) := hmul
    _ ≤ (T₀ : ℝ) * (1 / (1 - ε)) := mul_le_mul_of_nonneg_right hsum1 (by positivity)
    _ = (T₀ : ℝ) / (1 - ε) := by ring

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

lemma bipsRun_mono (v : V) {A B : Finset V} (h : A ⊆ B) (l : List (Choices G k)) :
    bipsRun v A l ⊆ bipsRun v B l := by
  induction l generalizing A B with
  | nil => simpa [bipsRun] using h
  | cons ρ l ih =>
    simpa [bipsRun] using ih (bipsStep_mono v h ρ)

lemma source_mem_bipsRun (v : V) {A : Finset V} (hv : v ∈ A) (l : List (Choices G k)) :
    v ∈ bipsRun v A l := by
  induction l generalizing A with
  | nil => simpa [bipsRun] using hv
  | cons ρ l ih =>
    simpa [bipsRun] using ih (source_mem_bipsStep v A ρ)

lemma bipsRun_univ (v : V) (hk : 1 ≤ k) (l : List (Choices G k)) :
    bipsRun v univ l = univ := by
  induction l with
  | nil => simp [bipsRun]
  | cons ρ l ih =>
    simpa [bipsRun, bipsStep_univ v hk ρ] using ih

omit [Fintype V] in
lemma cobraRun_append (C : Finset V) (l₁ l₂ : List (Choices G k)) :
    cobraRun C (l₁ ++ l₂) = cobraRun (cobraRun C l₁) l₂ := by
  simp [cobraRun, List.foldl_append]

omit [Fintype V] in
lemma cobraStep_nonempty (hk : 1 ≤ k) {D : Finset V} (hD : D.Nonempty) (ρ : Choices G k) :
    (cobraStep D ρ).Nonempty := by
  obtain ⟨x, hx⟩ := hD
  refine ⟨(ρ x ⟨0, hk⟩ : V), ?_⟩
  rw [mem_cobraStep]
  exact ⟨x, hx, ⟨0, hk⟩, rfl⟩

end Epidemics
