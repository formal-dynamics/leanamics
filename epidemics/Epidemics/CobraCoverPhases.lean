import Epidemics.CobraCoverEngineEnd
import Epidemics.CobraCoverChain
import Epidemics.CobraCoverSchedule

/-! # The three phases chained, for an abstract growth process (EPI-4, Theorems 2 and 3)

`GrowthProcess step src c` collects what the proofs of Lemmas 2 to 4 use about one round of a
set process: the source `src` is always in the next set (H1), the moment generating function
bound of `bips_mgf_le` (H2), the growth bound `E|A'| ≥ |A| (1 + c (1 - |A|/n))` of Lemma 1
(H3), monotonicity in the current set (H4), and `univ` is absorbing (H5). BIPS satisfies it with
`c = 1 - λ` (Theorem 2) and BIPS with branching factor `1 + ρ` with `c = ρ₀ (1 - λ₀)`
(Theorem 3).

From `{src}`, Lemma 2 reaches size `m = ⌈4000 log n/c²⌉₊`, Lemma 3 then reaches `9n/10` and
Lemma 4 infects every vertex; the phases are chained at their first hitting times
(`round_first_hit`). Under `c ≥ 128 √(log n/n)` the three lengths add up to `60000 log n/c³`
(`phase_schedule`), and the failure probability is `≤ 3/n³` (`GrowthProcess.fail_le`). Restarting
from the current set every `⌈60000 log n/c³⌉₊` rounds bounds the tail sums of the infection
time (`GrowthProcess.tail_sum_le_log`), the paper's equation (1).
-/

namespace Epidemics
open Finset Dynamics Real

/-- **Chernoff lower tail from the moment generating function** (the computation of
`bips_chernoff_lower`, for any real observable `X` of one round): if
`E e^{-ψ X} ≤ exp(-(1 - e^{-ψ}) E X)` for every `ψ`, `μ ≤ E X` and `0 < δ < 1`, then
`P(X ≤ (1 - δ) μ) ≤ exp(-δ² μ/2)`. -/
lemma avg_lower_tail_of_mgf {R : Type*} [Fintype R] (X : R → ℝ)
    (hmgf : ∀ ψ : ℝ, avg (fun ρ => exp (-ψ * X ρ)) ≤ exp (-(1 - exp (-ψ)) * avg X))
    {δ μ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμ : μ ≤ avg X) :
    avg (fun ρ => if X ρ ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤ exp (-(δ ^ 2 * μ / 2)) := by
  by_cases hμ0 : μ ≤ 0
  · have hLHS : avg (fun ρ => if X ρ ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤ 1 := by
      by_cases hne : Nonempty R
      · calc avg (fun ρ => if X ρ ≤ (1 - δ) * μ then (1 : ℝ) else 0)
            ≤ avg (fun _ : R => (1 : ℝ)) := avg_le_avg fun ρ => by split_ifs <;> norm_num
          _ = 1 := avg_const 1
      · haveI : IsEmpty R := not_nonempty_iff.mp hne
        rw [avg_eq_zero_of_isEmpty]
        exact zero_le_one
    refine hLHS.trans (one_le_exp_iff.mpr ?_)
    have : δ ^ 2 * μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg δ) hμ0
    linarith
  · push Not at hμ0
    have h1δ : 0 < 1 - δ := by linarith
    set φ : ℝ := -log (1 - δ) with hφ
    have hφexp : exp (-φ) = 1 - δ := by rw [hφ, neg_neg, exp_log h1δ]
    have hφpos : 0 < φ := by
      have : log (1 - δ) < 0 := log_neg h1δ (by linarith)
      linarith
    have hpoint (ρ : R) : (if X ρ ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (φ * ((1 - δ) * μ)) * exp (-φ * X ρ) := by
      split_ifs with hle
      · rw [← exp_add, one_le_exp_iff]
        nlinarith
      · positivity
    calc avg (fun ρ => if X ρ ≤ (1 - δ) * μ then (1 : ℝ) else 0)
        ≤ avg (fun ρ => exp (φ * ((1 - δ) * μ)) * exp (-φ * X ρ)) := avg_le_avg hpoint
      _ = exp (φ * ((1 - δ) * μ)) * avg (fun ρ => exp (-φ * X ρ)) := avg_const_mul _ _
      _ ≤ exp (φ * ((1 - δ) * μ)) * exp (-(1 - exp (-φ)) * avg X) :=
          mul_le_mul_of_nonneg_left (hmgf φ) (exp_pos _).le
      _ ≤ exp (φ * ((1 - δ) * μ)) * exp (-δ * μ) := by
          refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (exp_pos _).le
          rw [hφexp]
          nlinarith
      _ = exp (μ * (-δ - (1 - δ) * log (1 - δ))) := by
          rw [← exp_add, hφ]
          ring_nf
      _ ≤ exp (-(δ ^ 2 * μ / 2)) := by
          refine exp_le_exp.mpr ?_
          have h := neg_sub_one_sub_mul_log_le hδ0.le hδ1
          nlinarith

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R]

/-- The one-round hypotheses of the generic phase lemmas: (H1) the source is always in the next
set, (H2) the moment generating function bound, (H3) growth `E|A'| ≥ |A| (1 + c (1 - |A|/n))`,
(H4) monotonicity, (H5) `univ` is absorbing. -/
structure GrowthProcess (step : Finset V → R → Finset V) (src : V) (c : ℝ) : Prop where
  src_mem : ∀ A ρ, src ∈ step A ρ
  mgf : ∀ (A : Finset V) (ψ : ℝ),
    avg (fun ρ => exp (-ψ * ((step A ρ).card : ℝ))) ≤
      exp (-(1 - exp (-ψ)) * avg (fun ρ => ((step A ρ).card : ℝ)))
  growth : ∀ A : Finset V,
    (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
      avg (fun ρ => ((step A ρ).card : ℝ))
  mono : ∀ (A B : Finset V) (ρ : R), A ⊆ B → step A ρ ⊆ step B ρ
  univ_eq : ∀ ρ, step univ ρ = univ

namespace GrowthProcess

variable {step : Finset V → R → Finset V} {src : V} {c : ℝ}

omit [DecidableEq V] in
/-- The Chernoff lower tail (H2'), from the moment generating function bound. -/
lemma chernoff (hP : GrowthProcess step src c) (A : Finset V) (δ μ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hμ : μ ≤ avg (fun ρ => ((step A ρ).card : ℝ))) :
    avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
      exp (-(δ ^ 2 * μ / 2)) :=
  avg_lower_tail_of_mgf (fun ρ => ((step A ρ).card : ℝ)) (hP.mgf A) hδ0 hδ1 hμ

omit [Fintype V] [DecidableEq V] [Fintype R] in
lemma run_mono (hmono : ∀ (A B : Finset V) (ρ : R), A ⊆ B → step A ρ ⊆ step B ρ)
    {A B : Finset V} (h : A ⊆ B) (l : List R) : roundRun step A l ⊆ roundRun step B l := by
  induction l generalizing A B with
  | nil => exact h
  | cons ρ l ih => exact ih (hmono A B ρ h)

omit [Fintype V] [DecidableEq V] [Fintype R] in
lemma src_mem_run (hsrc : ∀ A ρ, src ∈ step A ρ) {A : Finset V} (hA : src ∈ A) (l : List R) :
    src ∈ roundRun step A l := by
  induction l generalizing A with
  | nil => exact hA
  | cons ρ l ih => exact ih (hsrc A ρ)

/-- **The three phases chained** (proof of Theorem 2, generic form). If
`c ≥ 128 √(log n/n)` and `T ≥ 60000 log n/c³`, the process started from `{src}` has not covered
`V` at time `T` with probability at most `3/n³`. -/
theorem fail_le [Nonempty R] (hP : GrowthProcess step src c) (hc1 : c ≤ 1)
    (hn2 : 2 ≤ Fintype.card V)
    (hgap : 128 * √(log (Fintype.card V) / Fintype.card V) ≤ c) {T : ℕ}
    (hT : 60000 * log (Fintype.card V) / c ^ 3 ≤ T) :
    expList R T (fun l => if roundRun step {src} l = univ then (0 : ℝ) else 1) ≤
      3 / (Fintype.card V : ℝ) ^ 3 := by
  classical
  set n := Fintype.card V with hn_def
  have hlog0 : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc0 : 0 < c := by
    have hroot : 0 < √(log (n : ℝ) / n) :=
      sqrt_pos.mpr (div_pos hlog0 (by exact_mod_cast (show 0 < n by omega)))
    linarith [mul_pos (by norm_num : (0 : ℝ) < 128) hroot]
  let m := Nat.ceil (4000 * log (n : ℝ) / c ^ 2)
  let T₁ := Nat.ceil (13 * (m : ℝ) / c + 72 * log (n : ℝ) / c ^ 2)
  let T₂ := Nat.ceil (24 * log (n : ℝ) / c)
  let T₃ := Nat.ceil (8 * log (n : ℝ) / c)
  obtain ⟨_, htwo, hnat, hT2n, htime⟩ := phase_schedule hn2 hc0 hc1 hgap rfl rfl rfl rfl
  have hchern := hP.chernoff
  let Pmed : Finset V → Prop := fun A => m < A.card
  let Pbig : Finset V → Prop := fun A => 9 * n ≤ 10 * A.card
  let Q : Finset V → Prop := fun A => A = univ
  have hEnd : ∀ b, Pbig b → ∀ T', T₃ ≤ T' →
      expList R T' (fun l => if Q (l.foldl step b) then (0 : ℝ) else 1) ≤
        1 / (n : ℝ) ^ 5 := by
    intro b hb T' hT'
    have hTend : 8 * log (n : ℝ) / c ≤ T' :=
      (Nat.le_ceil _).trans (by exact_mod_cast hT')
    have hnreal : 4000 * log (n : ℝ) / c ^ 2 ≤ (9 / 10) * (n : ℝ) := by
      refine hnat.trans ?_
      have h : ((9 * n / 10 : ℕ) : ℝ) * 10 ≤ 9 * (n : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self (9 * n) 10
      linarith
    exact round_end_phase step hc0 hc1 hP.growth hchern hP.mono hP.univ_eq hn2 hnreal hb hTend
  have hLarge : ∀ b, Pmed b → ∀ T', T₂ + T₃ ≤ T' →
      expList R T' (fun l => if Q (l.foldl step b) then (0 : ℝ) else 1) ≤
        (T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5 := by
    intro b hb T' hT'
    have hhit := round_first_hit step Pbig Q (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 5) hEnd
      b T₂ (T' - T₂) (by omega)
    rw [show T₂ + (T' - T₂) = T' by omega] at hhit
    have hsize : 4000 * log (n : ℝ) / c ^ 2 ≤ (b.card : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hb.le)
    have hbig := round_large_phase step hc0 hc1 hP.growth hchern hn2 hsize
      (Nat.le_ceil (24 * log (n : ℝ) / c))
    have hnever : expList R T₂ (fun l =>
        if ∀ s ≤ T₂, ¬ Pbig ((l.take s).foldl step b) then (1 : ℝ) else 0) ≤
        (T₂ : ℝ) / (n : ℝ) ^ 5 := by
      refine le_of_eq_of_le ?_ hbig
      refine congrArg (expList R T₂) (funext fun l => if_congr ?_ rfl rfl)
      refine forall_congr' fun s => imp_congr_right fun _ => ?_
      simp only [Pbig, roundRun, Nat.not_le, hn_def]
    linarith
  have hTs : 13 * (m : ℝ) / c + 24 * (3 : ℝ) * log (n : ℝ) / c ^ 2 ≤ T₁ := by
    rw [show (24 : ℝ) * 3 = 72 by norm_num]
    exact Nat.le_ceil _
  have hsmall := round_small_phase step src hP.src_mem hP.mgf hc0 hc1 hP.growth htwo 3 hTs
  have hhit := round_first_hit step Pmed Q
    (by positivity : (0 : ℝ) ≤ (T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5)
    hLarge ({src} : Finset V) T₁ (T₂ + T₃) le_rfl
  have hnever : expList R T₁ (fun l =>
      if ∀ s ≤ T₁, ¬ Pmed ((l.take s).foldl step ({src} : Finset V)) then (1 : ℝ) else 0) ≤
      (n : ℝ) ^ (-3 : ℝ) := by
    refine le_of_eq_of_le ?_ hsmall
    refine congrArg (expList R T₁) (funext fun l => if_congr ?_ rfl rfl)
    refine forall_congr' fun s => imp_congr_right fun _ => ?_
    simp only [Pmed, roundRun, Nat.not_lt]
    rfl
  have hpow : (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 := by
    rw [rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast,
      one_div]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnum : (T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 3 ≤
      3 / (n : ℝ) ^ 3 := by
    have h1 : (T₂ : ℝ) / n ^ 5 ≤ 1 / n ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hT2n' : (T₂ : ℝ) ≤ n := hT2n
      have h5 : (n : ℝ) ^ 3 * n * 1 ≤ n ^ 3 * n * n :=
        mul_le_mul_of_nonneg_left hone (mul_pos (pow_pos hn0 3) hn0).le
      have h4 : (T₂ : ℝ) * n ^ 3 ≤ n * n ^ 3 :=
        mul_le_mul_of_nonneg_right hT2n' (pow_pos hn0 3).le
      have : (n : ℝ) ^ 5 = n ^ 3 * n * n := by ring
      linarith
    have h2 : 1 / (n : ℝ) ^ 5 ≤ 1 / n ^ 3 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hone (by norm_num))
    have h3 : (1 : ℝ) / n ^ 3 + 1 / n ^ 3 + 1 / n ^ 3 = 3 / n ^ 3 := by ring
    linarith
  have hphase : expList R (T₁ + T₂ + T₃)
      (fun l => if roundRun step {src} l = univ then (0 : ℝ) else 1) ≤ 3 / (n : ℝ) ^ 3 := by
    have hsum := hhit.trans (add_le_add_left hnever _)
    rw [← Nat.add_assoc, hpow] at hsum
    exact hsum.trans (by linarith)
  have hsumle : T₁ + T₂ + T₃ ≤ T := by
    have hR : (T₁ : ℝ) + (T₂ : ℝ) + (T₃ : ℝ) ≤ (T : ℝ) := htime.trans hT
    exact_mod_cast hR
  rw [show T = (T₁ + T₂ + T₃) + (T - (T₁ + T₂ + T₃)) by omega, expList_append]
  refine le_trans (expList_le_expList fun l₁ => ?_) hphase
  refine (expList_le_expList fun l₂ => fail_append_le step hP.univ_eq {src} l₁ l₂).trans ?_
  rw [expList_const]

/-- **Restarting** (equation (1), generic form): if from `{src}` the failure probability at
time `T₀ > 0` is at most `1/2`, then every partial tail sum
`∑_{s < H} P(A_s ≠ V)` is at most `2 T₀`. From a state `A ∋ src` the process dominates the one
restarted from `{src}`, so `P(A_{s + T₀} ≠ V) ≤ P(A_s ≠ V)/2`. -/
theorem tail_sum_le [Nonempty R] (hP : GrowthProcess step src c) {T₀ : ℕ} (hT₀ : 0 < T₀)
    (hhalf : expList R T₀ (fun l => if roundRun step {src} l = univ then (0 : ℝ) else 1) ≤ 1 / 2)
    (H : ℕ) :
    ∑ s ∈ range H, expList R s (fun l => if roundRun step {src} l = univ then (0 : ℝ) else 1) ≤
      2 * T₀ := by
  classical
  let a : ℕ → ℝ := fun s =>
    expList R s (fun l => if roundRun step {src} l = univ then (0 : ℝ) else 1)
  have ha0 : ∀ s, 0 ≤ a s := fun s => expList_nonneg fun l => by split_ifs <;> norm_num
  have ha1 : ∀ s, a s ≤ 1 := fun s =>
    expList_fail_le_one s (fun l => roundRun step {src} l = univ)
  have hshift : ∀ s, a (s + T₀) ≤ (1 / 2) * a s := by
    intro s
    have happ : a (s + T₀) = expList R s fun l₁ => expList R T₀ fun l₂ =>
        if roundRun step {src} (l₁ ++ l₂) = univ then (0 : ℝ) else 1 := expList_append _ _ _
    rw [happ, show (1 / 2) * a s = expList R s (fun l₁ =>
      (1 / 2) * if roundRun step {src} l₁ = univ then (0 : ℝ) else 1) from
      (expList_const_mul _ _ _).symm]
    refine expList_le_expList fun l₁ => ?_
    simp_rw [roundRun_append]
    by_cases hA : roundRun step {src} l₁ = univ
    · rw [hA, if_pos rfl, mul_zero]
      have h0 : ∀ l₂ : List R, (if roundRun step univ l₂ = univ then (0 : ℝ) else 1) = 0 :=
        fun l₂ => by rw [roundRun_of_univ step hP.univ_eq, if_pos rfl]
      simp_rw [h0]
      rw [expList_const]
    · rw [if_neg hA, mul_one]
      refine le_trans (expList_le_expList fun l₂ => ?_) hhalf
      have hsub := run_mono hP.mono
        (singleton_subset_iff.mpr (src_mem_run hP.src_mem (mem_singleton_self src) l₁)) l₂
      by_cases hsmall : roundRun step {src} l₂ = univ
      · rw [hsmall, univ_subset_iff] at hsub
        rw [hsub, if_pos rfl, if_pos hsmall]
      · rw [if_neg hsmall]
        split_ifs <;> norm_num
  have hsum := sum_range_shift_le hT₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1) ha0 ha1 hshift H
  exact hsum.trans_eq (by ring)

omit [DecidableEq V] [Fintype R] in
/-- The gap hypothesis `c ≥ 128 √(log n/n)` with `c ≤ 1` forces `n ≥ 16385` (so `3/n² ≤ 1/2`
in the restarting arguments). -/
lemma card_ge_of_gap (hc1 : c ≤ 1) (hn2 : 2 ≤ Fintype.card V)
    (hgap : 128 * √(log (Fintype.card V) / Fintype.card V) ≤ c) : 16385 ≤ Fintype.card V := by
  have hlog0 : 0 < log (Fintype.card V : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Fintype.card V by omega))
  have hc0 : 0 < c := by
    have hroot : 0 < √(log (Fintype.card V : ℝ) / Fintype.card V) :=
      sqrt_pos.mpr (div_pos hlog0 (by exact_mod_cast (show 0 < Fintype.card V by omega)))
    linarith [mul_pos (by norm_num : (0 : ℝ) < 128) hroot]
  exact (phase_schedule hn2 hc0 hc1 hgap rfl rfl rfl rfl).1

/-- **Tail sums of the infection time** (generic form of Theorem 2 in expectation): under
`c ≥ 128 √(log n/n)`, every partial sum `∑_{s < H} P(A_s ≠ V)` from `{src}` is at most
`130000 log n/c³`. -/
theorem tail_sum_le_log [Nonempty R] (hP : GrowthProcess step src c) (hc1 : c ≤ 1)
    (hn2 : 2 ≤ Fintype.card V)
    (hgap : 128 * √(log (Fintype.card V) / Fintype.card V) ≤ c) (H : ℕ) :
    ∑ s ∈ range H, expList R s (fun l => if roundRun step {src} l = univ then (0 : ℝ) else 1) ≤
      130000 * log (Fintype.card V) / c ^ 3 := by
  set n := Fintype.card V with hn_def
  have hbig := card_ge_of_gap hc1 hn2 hgap
  have hlog0 : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc0 : 0 < c := by
    have hroot : 0 < √(log (n : ℝ) / n) :=
      sqrt_pos.mpr (div_pos hlog0 (by exact_mod_cast (show 0 < n by omega)))
    linarith [mul_pos (by norm_num : (0 : ℝ) < 128) hroot]
  set L := log (n : ℝ) / c ^ 3 with hL
  have hLge : log (n : ℝ) ≤ L := by
    rw [hL, le_div_iff₀ (pow_pos hc0 3)]
    have hpow : c ^ 3 ≤ 1 := pow_le_one₀ hc0.le hc1
    nlinarith
  have hlog2 : log 2 ≤ log (n : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hL1 : (1 / 2 : ℝ) ≤ L := by linarith [log_two_gt_d9]
  let T₀ := Nat.ceil (60000 * L)
  have hT₀ : 60000 * log (n : ℝ) / c ^ 3 ≤ T₀ := by
    rw [show 60000 * log (n : ℝ) / c ^ 3 = 60000 * L by rw [hL]; ring]
    exact Nat.le_ceil _
  have hT0pos : 0 < T₀ := Nat.ceil_pos.mpr (by linarith)
  have hhalf : expList R T₀ (fun l => if roundRun step {src} l = univ then (0 : ℝ) else 1) ≤
      1 / 2 := by
    refine (hP.fail_le hc1 hn2 hgap hT₀).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (16385 : ℝ) ≤ n := by exact_mod_cast hbig
    nlinarith [pow_le_pow_left₀ (by norm_num) this 3]
  have hceil : (T₀ : ℝ) < 60000 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  refine (hP.tail_sum_le hT0pos hhalf H).trans ?_
  rw [show 130000 * log (n : ℝ) / c ^ 3 = 130000 * L by rw [hL]; ring]
  linarith

end GrowthProcess

end Epidemics
