import Epidemics.CobraCoverNumerics
import Dynamics.Uniform

/-! # Generic one-step growth engine, small phase (EPI-4, Lemma 2)

Lemmas 2 to 4 use only a round-driven set process with a persistent source, an MGF bound, and a
linear growth lower bound `E|A'| ≥ |A| (1 + c (1 - |A|/n))` for some `0 < c ≤ 1`. This file proves
the small-set phase with `c` in place of `1 - λ`. The large phase is in `CobraCoverEngineLarge`
and the end phase is in `CobraCoverEngineEnd`.
-/

namespace Epidemics

open Finset Dynamics Real

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R]

/-- The state of a round-driven process after the rounds `l`, starting from `A`. -/
def roundRun (step : Finset V → R → Finset V) (A : Finset V) (l : List R) : Finset V :=
  l.foldl step A

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
@[simp] lemma roundRun_nil (step : Finset V → R → Finset V) (A : Finset V) :
    roundRun step A [] = A := rfl

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
@[simp] lemma roundRun_cons (step : Finset V → R → Finset V) (A : Finset V) (ρ : R)
    (l : List R) : roundRun step A (ρ :: l) = roundRun step (step A ρ) l := rfl

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
lemma roundRun_append (step : Finset V → R → Finset V) (A : Finset V) (l₁ l₂ : List R) :
    roundRun step A (l₁ ++ l₂) = roundRun step (roundRun step A l₁) l₂ :=
  List.foldl_append

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
lemma roundRun_take_succ (step : Finset V → R → Finset V) (A : Finset V) (ρ : R) (l : List R)
    (s : ℕ) : roundRun step A ((ρ :: l).take (s + 1)) =
      roundRun step (step A ρ) (l.take s) := by
  rw [List.take_cons (Nat.succ_pos s), Nat.succ_sub_one, roundRun_cons]

/-- `E(e^{-φ |A_t|} 1_{|A_s| ≤ m for all s < t})`, for the process `step` started at `A`. -/
noncomputable def smallWeight (step : Finset V → R → Finset V) (φ : ℝ) (m t : ℕ)
    (A : Finset V) : ℝ :=
  expList R t fun l =>
    exp (-φ * ((roundRun step A l).card : ℝ)) *
      if ∀ s < t, (roundRun step A (l.take s)).card ≤ m then (1 : ℝ) else 0

/-- `P(|A_s| ≤ m for every s ≤ t)`. -/
noncomputable def smallProb (step : Finset V → R → Finset V) (m t : ℕ) (A : Finset V) : ℝ :=
  expList R t fun l =>
    if ∀ s ≤ t, (roundRun step A (l.take s)).card ≤ m then (1 : ℝ) else 0

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
lemma forall_lt_cons (step : Finset V → R → Finset V) (A : Finset V) (ρ : R) (l : List R)
    (m t : ℕ) :
    (∀ s < t + 1, (roundRun step A ((ρ :: l).take s)).card ≤ m) ↔
      A.card ≤ m ∧ ∀ s < t, (roundRun step (step A ρ) (l.take s)).card ≤ m := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [roundRun_nil, List.take_zero] using h 0 (Nat.succ_pos t)
    · intro s hs
      simpa [roundRun_take_succ] using h (s + 1) (Nat.succ_lt_succ hs)
  · intro h s hs
    cases s with
    | zero => simpa [roundRun_nil, List.take_zero] using h.1
    | succ s =>
      simpa [roundRun_take_succ] using h.2 s (Nat.lt_of_succ_lt_succ hs)

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
lemma forall_le_cons (step : Finset V → R → Finset V) (A : Finset V) (ρ : R) (l : List R)
    (m t : ℕ) :
    (∀ s ≤ t + 1, (roundRun step A ((ρ :: l).take s)).card ≤ m) ↔
      A.card ≤ m ∧ ∀ s ≤ t, (roundRun step (step A ρ) (l.take s)).card ≤ m := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [roundRun_nil, List.take_zero] using h 0 (Nat.zero_le _)
    · intro s hs
      simpa [roundRun_take_succ] using h (s + 1) (Nat.succ_le_succ hs)
  · intro h s hs
    cases s with
    | zero => simpa [roundRun_nil, List.take_zero] using h.1
    | succ s =>
      simpa [roundRun_take_succ] using h.2 s (Nat.le_of_succ_le_succ hs)

omit [Fintype V] [DecidableEq V] [Nonempty R] in
lemma smallProb_succ_pull (step : Finset V → R → Finset V) (m t : ℕ) (A : Finset V) (ρ : R) :
    expList R t (fun l =>
        if ∀ s ≤ t + 1, (roundRun step A ((ρ :: l).take s)).card ≤ m then (1 : ℝ) else 0) =
      (if A.card ≤ m then (1 : ℝ) else 0) * smallProb step m t (step A ρ) := by
  classical
  simp_rw [smallProb, ← expList_const_mul]
  refine congrArg (expList R t) (funext fun l => ?_)
  by_cases hA : A.card ≤ m
  · rw [if_pos hA, one_mul]
    by_cases htail : ∀ s ≤ t, (roundRun step (step A ρ) (l.take s)).card ≤ m
    · rw [if_pos htail, if_pos ((forall_le_cons step A ρ l m t).2 ⟨hA, htail⟩)]
    · rw [if_neg htail, if_neg (fun h => htail ((forall_le_cons step A ρ l m t).1 h).2)]
  · rw [if_neg hA, zero_mul, if_neg]
    intro h
    exact hA ((forall_le_cons step A ρ l m t).1 h).1

omit [Fintype V] [DecidableEq V] [Nonempty R] in
lemma smallWeight_succ_pull (step : Finset V → R → Finset V) (φ : ℝ) (m t : ℕ) (A : Finset V)
    (ρ : R) :
    expList R t (fun l =>
        exp (-φ * ((roundRun step A (ρ :: l)).card : ℝ)) *
          if ∀ s < t + 1, (roundRun step A ((ρ :: l).take s)).card ≤ m then (1 : ℝ) else 0) =
      (if A.card ≤ m then (1 : ℝ) else 0) * smallWeight step φ m t (step A ρ) := by
  classical
  simp_rw [smallWeight, roundRun_cons, ← expList_const_mul]
  refine congrArg (expList R t) (funext fun l => ?_)
  by_cases hA : A.card ≤ m
  · rw [if_pos hA, one_mul]
    congr 1
    by_cases htail : ∀ s < t, (roundRun step (step A ρ) (l.take s)).card ≤ m
    · rw [if_pos htail, if_pos ((forall_lt_cons step A ρ l m t).2 ⟨hA, htail⟩)]
    · rw [if_neg htail, if_neg (fun h => htail ((forall_lt_cons step A ρ l m t).1 h).2)]
  · rw [if_neg hA, zero_mul]
    rw [mul_eq_zero]
    right
    rw [if_neg]
    intro h
    exact hA ((forall_lt_cons step A ρ l m t).1 h).1

omit [Fintype V] [DecidableEq V] in
/-- While the set stays of size at most `m`, the failure probability is at most `e^{φ m}` times
the weighted expectation. Only `φ ≥ 0` is used. -/
lemma smallProb_le_weight (step : Finset V → R → Finset V) (φ : ℝ) (hφ : 0 ≤ φ) (m : ℕ) :
    ∀ (t : ℕ) (A : Finset V),
      smallProb step m t A ≤ exp (φ * (m : ℝ)) * smallWeight step φ m t A := by
  classical
  intro t
  induction t with
  | zero =>
    intro A
    rw [smallProb, smallWeight, expList_zero, expList_zero, roundRun_nil]
    have hvac : (∀ s < 0, (roundRun step A ([].take s)).card ≤ m) :=
      fun s hs => (Nat.not_lt_zero s hs).elim
    rw [if_pos hvac, mul_one]
    by_cases hA : A.card ≤ m
    · have hall : ∀ s ≤ 0, (roundRun step A ([].take s)).card ≤ m := by
        intro s hs
        have hs0 : s = 0 := Nat.le_zero.1 hs
        simpa [hs0, roundRun_nil, List.take_zero] using hA
      rw [if_pos hall, ← exp_add, one_le_exp_iff]
      have : (A.card : ℝ) ≤ m := by exact_mod_cast hA
      nlinarith
    · rw [if_neg]
      · positivity
      · intro h
        exact hA (by simpa [roundRun_nil, List.take_zero] using h 0 (Nat.zero_le _))
  | succ t ih =>
    intro A
    rw [smallProb, smallWeight, expList_succ, expList_succ]
    simp_rw [smallProb_succ_pull, smallWeight_succ_pull]
    by_cases hA : A.card ≤ m
    · simp_rw [if_pos hA, one_mul]
      calc avg (fun ρ => smallProb step m t (step A ρ))
          ≤ avg (fun ρ => exp (φ * (m : ℝ)) * smallWeight step φ m t (step A ρ)) :=
            avg_le_avg fun ρ => ih (step A ρ)
        _ = exp (φ * (m : ℝ)) * avg (fun ρ => smallWeight step φ m t (step A ρ)) :=
            avg_const_mul _ _
    · simp_rw [if_neg hA, zero_mul, avg_const, mul_zero]
      exact le_refl 0

omit [Fintype V] [DecidableEq V] in
lemma smallProb_le_one (step : Finset V → R → Finset V) (m t : ℕ) (A : Finset V) :
    smallProb step m t A ≤ 1 := by
  rw [smallProb]
  calc expList R t (fun l =>
        if ∀ s ≤ t, (roundRun step A (l.take s)).card ≤ m then (1 : ℝ) else 0)
      ≤ expList R t (fun _ => (1 : ℝ)) :=
        expList_le_expList fun _ => by split_ifs <;> norm_num
    _ = 1 := expList_const _ _

omit [DecidableEq V] [Nonempty R] in
/-- One round from a set of size in `1, …, m` multiplies the Laplace weight by at most
`e^{φ - x}`. -/
lemma exp_mean_le (step : Finset V → R → Finset V) {c x φ : ℝ} (hc0 : 0 < c)
    (hx : x = c / 2) (hφ : φ = log (1 + x)) {m : ℕ} (hm : 2 * m ≤ Fintype.card V)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ : R => ((step A ρ).card : ℝ)))
    {A : Finset V} (hA1 : 1 ≤ A.card) (hAm : A.card ≤ m) :
    exp (-(1 - exp (-φ)) * avg (fun ρ : R => ((step A ρ).card : ℝ))) ≤
      exp ((φ - x) - φ * (A.card : ℝ)) := by
  have hx0 : 0 < x := by
    rw [hx]
    exact div_pos hc0 (by norm_num)
  have h1x : 0 < 1 + x := by
    rw [hx]
    linarith
  have hφexp : exp φ = 1 + x := by rw [hφ, exp_log h1x]
  have hneg : exp (-φ) = (1 + x)⁻¹ := by rw [exp_neg, hφexp]
  have hxφ : (1 - exp (-φ)) * exp φ = x := by
    rw [hφexp, hneg]
    field_simp
    ring
  have hφ_le_x : φ ≤ x := by
    rw [hφ]
    have := log_le_sub_one_of_pos h1x
    linarith
  have hApos : 0 < A.card := by omega
  obtain ⟨a, _⟩ := Finset.card_pos.mp hApos
  haveI : Nonempty V := ⟨a⟩
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have htwo : (2 : ℝ) * A.card ≤ Fintype.card V := by
    have : 2 * A.card ≤ Fintype.card V := (Nat.mul_le_mul_left 2 hAm).trans hm
    exact_mod_cast this
  have hfrac : (A.card : ℝ) / ↑(Fintype.card V) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by exact_mod_cast hn) (by norm_num)]
    linarith
  have hgap : (1 : ℝ) / 2 ≤ 1 - (A.card : ℝ) / ↑(Fintype.card V) := by linarith
  have hxle : x ≤ c * (1 - (A.card : ℝ) / ↑(Fintype.card V)) := by
    rw [hx]
    calc c / 2 = c * (1 / 2) := by ring
      _ ≤ c * (1 - (A.card : ℝ) / ↑(Fintype.card V)) :=
          mul_le_mul_of_nonneg_left hgap hc0.le
  have hmean : (A.card : ℝ) * (1 + x) ≤ avg (fun ρ => ((step A ρ).card : ℝ)) := by
    have hlin : 1 + x ≤ 1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V)) := by linarith
    calc (A.card : ℝ) * (1 + x)
        ≤ (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) :=
          mul_le_mul_of_nonneg_left hlin (by exact_mod_cast Nat.zero_le A.card)
      _ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) := hgrowth A
  have hmean' : (A.card : ℝ) * exp φ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) := by
    simpa [hφexp] using hmean
  have ha0 : 0 ≤ 1 - exp (-φ) := by
    have : exp (-φ) ≤ 1 := by
      rw [hneg, inv_le_one₀ h1x]
      linarith
    linarith
  have hscale : (A.card : ℝ) * x ≤
      (1 - exp (-φ)) * avg (fun ρ => ((step A ρ).card : ℝ)) := by
    calc (A.card : ℝ) * x
        = (A.card : ℝ) * ((1 - exp (-φ)) * exp φ) := by rw [hxφ]
      _ = (1 - exp (-φ)) * ((A.card : ℝ) * exp φ) := by ring
      _ ≤ (1 - exp (-φ)) * avg (fun ρ => ((step A ρ).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hmean' ha0
  have hExp1 : -(1 - exp (-φ)) * avg (fun ρ => ((step A ρ).card : ℝ)) ≤
      -((A.card : ℝ) * x) := by
    have hnegmul : -(1 - exp (-φ)) * avg (fun ρ => ((step A ρ).card : ℝ)) =
        -((1 - exp (-φ)) * avg (fun ρ => ((step A ρ).card : ℝ))) := by ring
    linarith
  have hslack : -((A.card : ℝ) * x) ≤ (φ - x) - φ * (A.card : ℝ) := by
    have hcard1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hA1
    have hnonpos : (φ - x) * ((A.card : ℝ) - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  exact (exp_le_exp).mpr (hExp1.trans hslack)

omit [DecidableEq V] in
/-- While `|A| ≥ 1`, the weighted expectation contracts by `e^{φ - x}` at every round. -/
lemma smallWeight_contract (step : Finset V → R → Finset V) (src : V)
    (hsrc : ∀ A ρ, src ∈ step A ρ)
    {c x φ : ℝ} (hc0 : 0 < c) (hx : x = c / 2) (hφ : φ = log (1 + x))
    (hmgf : ∀ (A : Finset V) (ψ : ℝ),
      avg (fun ρ => exp (-ψ * ((step A ρ).card : ℝ))) ≤
        exp (-(1 - exp (-ψ)) * avg (fun ρ => ((step A ρ).card : ℝ))))
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    {m : ℕ} (hm : 2 * m ≤ Fintype.card V) :
    ∀ (t : ℕ) (A : Finset V), 1 ≤ A.card →
      smallWeight step φ m t A ≤
        exp ((t : ℝ) * (φ - x)) * exp (-φ * (A.card : ℝ)) := by
  intro t
  induction t with
  | zero =>
    intro A _
    rw [smallWeight, expList_zero, roundRun_nil]
    have hvac : (∀ s < 0, (roundRun step A ([].take s)).card ≤ m) :=
      fun s hs => (Nat.not_lt_zero s hs).elim
    rw [if_pos hvac, mul_one, Nat.cast_zero, zero_mul, exp_zero, one_mul]
  | succ t ih =>
    intro A hA1
    rw [smallWeight, expList_succ]
    simp_rw [smallWeight_succ_pull]
    by_cases hAm : A.card ≤ m
    · simp_rw [if_pos hAm, one_mul]
      calc avg (fun ρ => smallWeight step φ m t (step A ρ))
          ≤ avg (fun ρ => exp ((t : ℝ) * (φ - x)) *
              exp (-φ * ((step A ρ).card : ℝ))) := by
              refine avg_le_avg fun ρ => ?_
              exact ih (step A ρ) (Finset.one_le_card.mpr ⟨src, hsrc A ρ⟩)
        _ = exp ((t : ℝ) * (φ - x)) *
              avg (fun ρ => exp (-φ * ((step A ρ).card : ℝ))) := avg_const_mul _ _
        _ ≤ exp ((t : ℝ) * (φ - x)) *
              exp (-(1 - exp (-φ)) * avg (fun ρ => ((step A ρ).card : ℝ))) :=
            mul_le_mul_of_nonneg_left (hmgf A φ) (exp_nonneg _)
        _ ≤ exp ((t : ℝ) * (φ - x)) * exp ((φ - x) - φ * (A.card : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (exp_mean_le step hc0 hx hφ hm hgrowth hA1 hAm) (exp_nonneg _)
        _ = exp (((t + 1 : ℕ) : ℝ) * (φ - x)) * exp (-φ * (A.card : ℝ)) := by
            rw [← exp_add, ← exp_add]
            congr 1
            push_cast
            ring
    · simp_rw [if_neg hAm, zero_mul]
      rw [avg_const]
      positivity

omit [DecidableEq V] in
/-- **Lemma 2, abstract form.** A round-driven process with a persistent source, the BIPS
moment bound and relative growth `1 + c (1 - |A|/n)` exceeds size `m ≤ n/2` within
`T ≥ 13 m/c + 24 C log n/c²` rounds, except with probability `n^{-C}`. -/
lemma round_small_phase (step : Finset V → R → Finset V) (src : V)
    (hsrc : ∀ A ρ, src ∈ step A ρ)
    (hmgf : ∀ (A : Finset V) (ψ : ℝ),
      avg (fun ρ => exp (-ψ * ((step A ρ).card : ℝ))) ≤
        exp (-(1 - exp (-ψ)) * avg (fun ρ => ((step A ρ).card : ℝ))))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    {m T : ℕ} (hm : 2 * m ≤ Fintype.card V) (C : ℝ)
    (hT : 13 * (m : ℝ) / c + 24 * C * log (Fintype.card V) / c ^ 2 ≤ T) :
    smallProb step m T {src} ≤ (Fintype.card V : ℝ) ^ (-C) := by
  haveI : Nonempty V := ⟨src⟩
  have hn1 : 1 ≤ Fintype.card V := Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  by_cases hC : 0 ≤ C
  · obtain ⟨x, hx⟩ : ∃ x : ℝ, x = c / 2 := ⟨_, rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = log (1 + x) := ⟨_, rfl⟩
    have hx0 : 0 < x := by
      rw [hx]
      exact div_pos hc0 (by norm_num)
    have h1x : 0 < 1 + x := by linarith
    have hφ0 : 0 ≤ φ := by
      rw [hφ]
      have hlog : log 1 ≤ log (1 + x) :=
        (log_le_log_iff (by norm_num) h1x).2 (by linarith)
      simpa [log_one] using hlog
    have hcard : ({src} : Finset V).card = 1 := Finset.card_singleton src
    have hw := smallWeight_contract step src hsrc hc0 hx hφ hmgf hgrowth hm T {src}
      (by simp [hcard])
    have hw' : smallWeight step φ m T {src} ≤ exp ((T : ℝ) * (φ - x)) * exp (-φ) := by
      simpa [hcard, mul_one] using hw
    have hsw := smallProb_le_weight step φ hφ0 m T {src}
    have heq : exp (φ * (m : ℝ)) * (exp ((T : ℝ) * (φ - x)) * exp (-φ)) =
        exp (φ * (m : ℝ) + (T : ℝ) * (φ - x) - φ) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring
    calc smallProb step m T {src}
        ≤ exp (φ * (m : ℝ)) * smallWeight step φ m T {src} := hsw
      _ ≤ exp (φ * (m : ℝ)) * (exp ((T : ℝ) * (φ - x)) * exp (-φ)) :=
          mul_le_mul_of_nonneg_left hw' (exp_nonneg _)
      _ = exp (φ * (m : ℝ) + (T : ℝ) * (φ - x) - φ) := heq
      _ ≤ exp (φ * (m : ℝ) + (T : ℝ) * (φ - x)) := by
          refine (exp_le_exp).mpr ?_
          linarith
      _ ≤ exp (-C * log (Fintype.card V : ℝ)) := by
          refine (exp_le_exp).mpr ?_
          exact small_phase_exponent (by exact_mod_cast Nat.zero_le m)
            (by exact_mod_cast Nat.zero_le T) hc0 hc1 hx hφ hC hn1 hT
      _ = (Fintype.card V : ℝ) ^ (-C) := by
          rw [rpow_def_of_pos (by exact_mod_cast (Nat.succ_le_iff.mp hn1))]
          congr 1
          ring
  · push Not at hC
    have hle : smallProb step m T {src} ≤ 1 := smallProb_le_one step m T {src}
    have hone : (1 : ℝ) ≤ (Fintype.card V : ℝ) ^ (-C) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by linarith)
    exact hle.trans hone

end Epidemics
