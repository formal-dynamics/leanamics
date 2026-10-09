import Epidemics.CobraCoverEngine
import Dynamics.Rounds

/-! # Generic large and end phases (EPI-4, Lemmas 3 and 4)

The same one-round hypotheses as the small phase, with `c` in place of `1 - λ`: relative growth
`E|A'| ≥ |A| (1 + c (1 - |A|/n))` and the Chernoff lower tail. Lemma 3 stops the process once
`|A| ≥ 9n/10` and applies `Dynamics.expList_escape`.
-/

namespace Epidemics

open Finset Dynamics Real

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R]

/-- Freeze the round once the infected set covers at least `9n/10`. -/
def stepFreeze (step : Finset V → R → Finset V) (n : ℕ) (A : Finset V) (ρ : R) : Finset V :=
  if 9 * n ≤ 10 * A.card then A else step A ρ

/-- States that have already reached `9n/10`, or have grown by `(1 + z)^t` from `A₀`. -/
def largeTarget (A₀ : Finset V) (z : ℝ) (t : ℕ) : Set (Finset V) :=
  {A | 9 * Fintype.card V ≤ 10 * A.card ∨
    (A₀.card : ℝ) * (1 + z) ^ t ≤ (A.card : ℝ)}

omit [Fintype V] [DecidableEq V] [Nonempty R] in
lemma expList_take (T : ℕ) (F : List R → ℝ) :
    expList R T (fun l => F (l.take T)) = expList R T F := by
  induction T generalizing F with
  | zero => simp [List.take_zero]
  | succ T ih =>
    rw [expList_succ, expList_succ]
    refine congrArg avg (funext fun a => ?_)
    have htake (l : List R) : (a :: l).take (T + 1) = a :: l.take T := by
      rw [List.take_cons (Nat.succ_pos _), Nat.succ_sub_one]
    simp_rw [htake]
    exact ih fun l => F (a :: l)

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
lemma freeze_eq_of_below (step : Finset V → R → Finset V) (n : ℕ) (A : Finset V) (m : List R)
    (h : ∀ s ≤ m.length, 10 * (roundRun step A (m.take s)).card < 9 * n) :
    roundRun (stepFreeze step n) A m = roundRun step A m := by
  induction m generalizing A with
  | nil => rfl
  | cons ρ m ih =>
    have h0 : 10 * A.card < 9 * n := by
      simpa [roundRun_nil, List.take_zero] using h 0 (Nat.zero_le _)
    have hfreeze : stepFreeze step n A ρ = step A ρ := by
      simp [stepFreeze, Nat.not_le.mpr h0]
    rw [roundRun_cons, hfreeze, roundRun_cons]
    refine ih (step A ρ) ?_
    intro s hs
    have hs' : s + 1 ≤ (ρ :: m).length := Nat.succ_le_of_lt (Nat.lt_succ_of_le hs)
    simpa [roundRun_take_succ] using h (s + 1) hs'

omit [DecidableEq V] [Nonempty R] in
/-- While `10|A| < 9n` and `|A| ≥ 4000 log n/c²`, one round fails to multiply the size by
`1 + c/23` with probability at most `n^{-5}`. -/
lemma round_slow_prob (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hchernoff : ∀ (A : Finset V) (δ μ : ℝ), 0 < δ → δ < 1 →
      μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) →
      avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (-(δ ^ 2 * μ / 2)))
    (hn : 2 ≤ Fintype.card V) {A : Finset V}
    (hA : 4000 * log (Fintype.card V) / c ^ 2 ≤ (A.card : ℝ))
    (hsmall : 10 * A.card < 9 * Fintype.card V) :
    avg (fun ρ => if ((step A ρ).card : ℝ) < (A.card : ℝ) * (1 + c / 23) then (1 : ℝ) else 0) ≤
      (Fintype.card V : ℝ) ^ (-5 : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  have hn0 : (0 : ℝ) < n := by
    unfold n
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hlog : 0 < log n := by
    have hone : (1 : ℝ) < n := by
      unfold n
      exact_mod_cast (show 1 < Fintype.card V by omega)
    exact log_pos hone
  have hcard0 : (0 : ℝ) < A.card := by
    have hc2 : 0 < c ^ 2 := by positivity
    have hpos : 0 < 4000 * log n / c ^ 2 := div_pos (mul_pos (by norm_num) hlog) hc2
    linarith
  have h10 : (10 : ℝ) * (A.card : ℝ) < 9 * n := by
    unfold n
    exact_mod_cast hsmall
  have hfrac : (A.card : ℝ) / n < 9 / 10 := by
    rw [div_lt_iff₀ hn0]
    nlinarith
  have hgap : (1 : ℝ) / 10 ≤ 1 - (A.card : ℝ) / n := by linarith
  let μ : ℝ := (A.card : ℝ) * (1 + c / 10)
  have hμE : μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) := by
    have hlin : 1 + c / 10 ≤ 1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V)) := by
      have : c / 10 ≤ c * (1 - (A.card : ℝ) / n) := by
        calc c / 10 = c * (1 / 10) := by ring
          _ ≤ c * (1 - (A.card : ℝ) / n) := mul_le_mul_of_nonneg_left hgap hc0.le
      linarith
    calc μ ≤ (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) :=
          mul_le_mul_of_nonneg_left hlin (by exact_mod_cast Nat.zero_le A.card)
      _ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) := hgrowth A
  let eps : ℝ := sqrt (10 * log n / (A.card : ℝ))
  have heps_sq : eps ^ 2 = 10 * log n / (A.card : ℝ) :=
    sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hlog.le) hcard0.le)
  have heps_le : eps ≤ c / 20 := by
    have h400 : 10 * log n / (A.card : ℝ) ≤ c ^ 2 / 400 := by
      have hc2 : 0 < c ^ 2 := by positivity
      have hbase : 4000 * log n ≤ (A.card : ℝ) * c ^ 2 := by
        rw [div_le_iff₀ hc2] at hA
        exact hA
      rw [div_le_div_iff₀ hcard0 (by norm_num)]
      nlinarith
    have hsq : eps ^ 2 ≤ (c / 20) ^ 2 := by
      rw [heps_sq]
      calc 10 * log n / (A.card : ℝ) ≤ c ^ 2 / 400 := h400
        _ = (c / 20) ^ 2 := by ring
    exact (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).1 hsq
  have heps0 : 0 < eps := by
    rw [sqrt_pos]
    exact div_pos (mul_pos (by norm_num) hlog) hcard0
  have heps1 : eps < 1 := by
    have : c / 20 ≤ 1 / 20 := by linarith
    linarith
  have hchern := hchernoff A eps μ heps0 heps1 hμE
  have hfactor : (A.card : ℝ) * (1 + c / 23) ≤ (1 - eps) * μ := by
    have h1 : (1 - c / 20) * (1 + c / 10) ≤ (1 - eps) * (1 + c / 10) := by
      have : 1 - c / 20 ≤ 1 - eps := by linarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    calc (A.card : ℝ) * (1 + c / 23)
        ≤ (A.card : ℝ) * ((1 - c / 20) * (1 + c / 10)) :=
          mul_le_mul_of_nonneg_left (one_step_factor_23 hc0.le hc1)
            (by exact_mod_cast Nat.zero_le A.card)
      _ ≤ (A.card : ℝ) * ((1 - eps) * (1 + c / 10)) :=
          mul_le_mul_of_nonneg_left h1 (by exact_mod_cast Nat.zero_le A.card)
      _ = (1 - eps) * μ := by ring
  have htail : 5 * log n ≤ eps ^ 2 * μ / 2 := by
    have hμcard : (A.card : ℝ) ≤ μ := by
      have : (1 : ℝ) ≤ 1 + c / 10 := by linarith
      have hmul : (A.card : ℝ) * 1 ≤ (A.card : ℝ) * (1 + c / 10) :=
        mul_le_mul_of_nonneg_left this hcard0.le
      simpa [μ, one_mul] using hmul
    have hleft : 5 * log n = eps ^ 2 * (A.card : ℝ) / 2 := by
      rw [heps_sq]
      field_simp
      ring
    have hcomp : eps ^ 2 * (A.card : ℝ) / 2 ≤ eps ^ 2 * μ / 2 := by
      have : eps ^ 2 * (A.card : ℝ) ≤ eps ^ 2 * μ :=
        mul_le_mul_of_nonneg_left hμcard (sq_nonneg eps)
      linarith
    linarith
  calc avg (fun ρ => if ((step A ρ).card : ℝ) < (A.card : ℝ) * (1 + c / 23) then (1 : ℝ) else 0)
      ≤ avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - eps) * μ then (1 : ℝ) else 0) := by
        refine avg_le_avg fun ρ => ?_
        by_cases hlt : ((step A ρ).card : ℝ) < (A.card : ℝ) * (1 + c / 23)
        · rw [if_pos hlt]
          have : ((step A ρ).card : ℝ) ≤ (1 - eps) * μ := by linarith [hfactor]
          simp [this]
        · rw [if_neg hlt]
          split_ifs <;> norm_num
    _ ≤ exp (-(eps ^ 2 * μ / 2)) := hchern
    _ ≤ exp (-(5 * log n)) := (exp_le_exp).mpr (by linarith)
    _ = n ^ (-5 : ℝ) := by
        rw [rpow_def_of_pos hn0]
        congr 1
        ring

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
/-- Prefixes of `l.take T` of length at most `T` are prefixes of `l`. -/
lemma take_take_of_le (l : List R) {s T : ℕ} (hs : s ≤ T) : (l.take T).take s = l.take s := by
  induction l generalizing s T with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => simp
    | succ s =>
      cases T with
      | zero => omega
      | succ T =>
        rw [List.take_succ_cons, List.take_succ_cons]
        exact congrArg (List.cons a) (ih (Nat.le_of_succ_le_succ hs))

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
/-- `(1 + c/23)^T ≥ n` for `T ≥ 24 log n / c`, using `log(1 + z) ≥ z/(1 + z) ≥ c/24`. -/
lemma one_add_c_div_pow_ge {c : ℝ} {n T : ℕ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hn : 2 ≤ n)
    (hT : 24 * log (n : ℝ) / c ≤ T) : (n : ℝ) ≤ (1 + c / 23) ^ T := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hz0 : (0 : ℝ) < c / 23 := by positivity
  have hden : 1 + c / 23 ≤ (24 : ℝ) / 23 := by
    have : c / 23 ≤ 1 / 23 := div_le_div_of_nonneg_right hc1 (by norm_num)
    linarith
  have hlogz : c / 24 ≤ log (1 + c / 23) := by
    have hfrac : (c / 23) / (1 + c / 23) ≤ log (1 + c / 23) := log_one_add_ge_div hz0.le
    have hcmp : c / 24 ≤ (c / 23) / (1 + c / 23) := by
      have hdiv : (c / 23) / ((24 : ℝ) / 23) ≤ (c / 23) / (1 + c / 23) :=
        div_le_div_of_nonneg_left hz0.le (by linarith) hden
      have heq : (c / 23) / ((24 : ℝ) / 23) = c / 24 := by
        field_simp
      linarith
    linarith
  have hTlog : log (n : ℝ) ≤ (T : ℝ) * log (1 + c / 23) := by
    have hprod : 24 * log (n : ℝ) / c * (c / 24) = log (n : ℝ) := by
      field_simp
    have hlow : log (n : ℝ) ≤ (T : ℝ) * (c / 24) := by
      have hmul : 24 * log (n : ℝ) / c * (c / 24) ≤ (T : ℝ) * (c / 24) :=
        mul_le_mul_of_nonneg_right hT (by positivity)
      linarith
    have : (T : ℝ) * (c / 24) ≤ (T : ℝ) * log (1 + c / 23) :=
      mul_le_mul_of_nonneg_left hlogz (Nat.cast_nonneg T)
    linarith
  have hposz : (0 : ℝ) < 1 + c / 23 := by linarith
  calc (n : ℝ) = exp (log (n : ℝ)) := (exp_log hn0).symm
    _ ≤ exp ((T : ℝ) * log (1 + c / 23)) := (exp_le_exp).mpr hTlog
    _ = exp (log (1 + c / 23) * (T : ℝ)) := by
        congr 1
        ring
    _ = (1 + c / 23) ^ (T : ℝ) := (rpow_def_of_pos hposz (T : ℝ)).symm
    _ = (1 + c / 23) ^ T := rpow_natCast _ _

omit [DecidableEq V] in
/-- **Lemma 3, generic form.** From `|A₀| ≥ 4000 log n/c²`, the probability that every prefix
has size `< 9n/10` through time `T ≥ 24 log n/c` is at most `T/n⁵`. -/
lemma round_large_phase (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hchernoff : ∀ (A : Finset V) (δ μ : ℝ), 0 < δ → δ < 1 →
      μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) →
      avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (-(δ ^ 2 * μ / 2)))
    (hn : 2 ≤ Fintype.card V) {A₀ : Finset V}
    (hA₀ : 4000 * log (Fintype.card V) / c ^ 2 ≤ (A₀.card : ℝ)) {T : ℕ}
    (hT : 24 * log (Fintype.card V) / c ≤ T) :
    expList R T (fun l =>
      if ∀ s ≤ T, 10 * (roundRun step A₀ (l.take s)).card < 9 * Fintype.card V
        then (1 : ℝ) else 0) ≤
      T / (Fintype.card V : ℝ) ^ 5 := by
  classical
  have hp0 : 0 ≤ (Fintype.card V : ℝ) ^ (-5 : ℝ) := by positivity
  have hcard1 : (1 : ℝ) ≤ (A₀.card : ℝ) := by
    have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    have hlogn : log 2 ≤ log (Fintype.card V : ℝ) :=
      (log_le_log_iff (by norm_num) (by linarith)).2 hnR
    have h4000 : (1 : ℝ) < 4000 * log 2 := by
      have hnum : (1 : ℝ) < 4000 * 0.6931471803 := by norm_num
      exact hnum.trans (mul_lt_mul_of_pos_left log_two_gt_d9 (by norm_num))
    have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1
    have hc2pos : 0 < c ^ 2 := by positivity
    have hscale : 4000 * log (Fintype.card V : ℝ) ≤
        4000 * log (Fintype.card V : ℝ) / c ^ 2 := by
      rw [le_div_iff₀ hc2pos]
      calc 4000 * log (Fintype.card V : ℝ) * c ^ 2
          = c ^ 2 * (4000 * log (Fintype.card V : ℝ)) := by ring
        _ ≤ 1 * (4000 * log (Fintype.card V : ℝ)) :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ = 4000 * log (Fintype.card V : ℝ) := by ring
    have hbig : (1 : ℝ) < 4000 * log (Fintype.card V : ℝ) := by
      have : 4000 * log 2 ≤ 4000 * log (Fintype.card V : ℝ) :=
        mul_le_mul_of_nonneg_left hlogn (by norm_num)
      linarith
    linarith [hA₀, hscale]
  have hbase : (Fintype.card V : ℝ) ≤ (1 + c / 23) ^ T :=
    one_add_c_div_pow_ge hc0 hc1 hn hT
  have hgrowT : (Fintype.card V : ℝ) ≤ (A₀.card : ℝ) * (1 + c / 23) ^ T := by
    calc (Fintype.card V : ℝ) ≤ (1 + c / 23) ^ T := hbase
      _ = 1 * (1 + c / 23) ^ T := (one_mul _).symm
      _ ≤ (A₀.card : ℝ) * (1 + c / 23) ^ T :=
          mul_le_mul_of_nonneg_right hcard1 (pow_nonneg (by linarith) _)
  have hstart : A₀ ∈ largeTarget A₀ (c / 23) 0 := by
    refine Or.inr ?_
    simp [pow_zero, mul_one]
  have hstep : ∀ t < T, ∀ y ∈ largeTarget A₀ (c / 23) t,
      avg (fun ρ => by classical exact
        (if stepFreeze step (Fintype.card V) y ρ ∈ largeTarget A₀ (c / 23) (t + 1)
          then (0 : ℝ) else 1)) ≤
        (Fintype.card V : ℝ) ^ (-5 : ℝ) := by
    intro t _h y hy
    simp only [largeTarget, Set.mem_setOf_eq] at hy
    by_cases hhit : 9 * Fintype.card V ≤ 10 * y.card
    · have hstay (ρ : R) : stepFreeze step (Fintype.card V) y ρ ∈
          largeTarget A₀ (c / 23) (t + 1) := by
        rw [stepFreeze, if_pos hhit]
        exact Or.inl hhit
      have hzero : avg (fun ρ => by classical exact
          (if stepFreeze step (Fintype.card V) y ρ ∈ largeTarget A₀ (c / 23) (t + 1)
            then (0 : ℝ) else 1)) = 0 := by
        have hfun : (fun ρ => by classical exact
            (if stepFreeze step (Fintype.card V) y ρ ∈ largeTarget A₀ (c / 23) (t + 1)
              then (0 : ℝ) else 1)) = fun _ => (0 : ℝ) := by
          funext ρ
          exact if_pos (hstay ρ)
        rw [hfun, avg_const]
      rw [hzero]
      exact hp0
    · have hbelow : 10 * y.card < 9 * Fintype.card V := Nat.not_le.mp hhit
      have hsize : (A₀.card : ℝ) * (1 + c / 23) ^ t ≤ (y.card : ℝ) := by
        rcases hy with hhit' | hgrow
        · exact absurd hhit' hhit
        · exact hgrow
      have hone_pow : (1 : ℝ) ≤ (1 + c / 23) ^ t := one_le_pow₀ (by linarith)
      have hAley : (A₀.card : ℝ) ≤ (y.card : ℝ) := by
        calc (A₀.card : ℝ) = (A₀.card : ℝ) * 1 := (mul_one _).symm
          _ ≤ (A₀.card : ℝ) * (1 + c / 23) ^ t :=
              mul_le_mul_of_nonneg_left hone_pow (Nat.cast_nonneg _)
          _ ≤ (y.card : ℝ) := hsize
      have hyA : 4000 * log (Fintype.card V) / c ^ 2 ≤ (y.card : ℝ) := le_trans hA₀ hAley
      have hslow := round_slow_prob step hc0 hc1 hgrowth hchernoff hn hyA hbelow
      refine (avg_le_avg fun ρ => ?_).trans hslow
      by_cases hmem : stepFreeze step (Fintype.card V) y ρ ∈ largeTarget A₀ (c / 23) (t + 1)
      · rw [if_pos hmem]
        split_ifs <;> norm_num
      · rw [if_neg hmem]
        have hfreeze : stepFreeze step (Fintype.card V) y ρ = step y ρ := by
          rw [stepFreeze, if_neg hhit]
        have hnot : step y ρ ∉ largeTarget A₀ (c / 23) (t + 1) := by rwa [hfreeze] at hmem
        simp only [largeTarget, Set.mem_setOf_eq] at hnot
        have hlt : ((step y ρ).card : ℝ) < (A₀.card : ℝ) * (1 + c / 23) ^ (t + 1) :=
          not_le.mp (not_or.mp hnot).2
        have hle : (A₀.card : ℝ) * (1 + c / 23) ^ (t + 1) ≤ (y.card : ℝ) * (1 + c / 23) := by
          have hmul := mul_le_mul_of_nonneg_right hsize (by linarith : (0 : ℝ) ≤ 1 + c / 23)
          simpa [pow_succ, mul_assoc] using hmul
        have hstrict : ((step y ρ).card : ℝ) < (y.card : ℝ) * (1 + c / 23) :=
          lt_of_lt_of_le hlt hle
        rw [if_pos hstrict]
  have hesc := expList_escape (stepFreeze step (Fintype.card V)) hp0 T (largeTarget A₀ (c / 23))
    A₀ hstart hstep
  have hpoint : ∀ l : List R,
      (if ∀ s ≤ T, 10 * (roundRun step A₀ (l.take s)).card < 9 * Fintype.card V
        then (1 : ℝ) else 0) ≤
      (if roundRun (stepFreeze step (Fintype.card V)) A₀ (l.take T) ∈
          largeTarget A₀ (c / 23) T then (0 : ℝ) else 1) := by
    intro l
    by_cases hall : ∀ s ≤ T, 10 * (roundRun step A₀ (l.take s)).card < 9 * Fintype.card V
    · rw [if_pos hall]
      have hpref : ∀ s ≤ (l.take T).length,
          10 * (roundRun step A₀ ((l.take T).take s)).card < 9 * Fintype.card V := by
        intro s hs
        have hlen : (l.take T).length ≤ T := by
          rw [List.length_take]
          exact Nat.min_le_left T l.length
        have hsT : s ≤ T := le_trans hs hlen
        rw [take_take_of_le l hsT]
        exact hall s hsT
      have heqrun := freeze_eq_of_below step (Fintype.card V) A₀ (l.take T) hpref
      have hcardlt : (roundRun step A₀ (l.take T)).card < Fintype.card V := by
        have h10 := hall T le_rfl
        omega
      have hltgrow : ((roundRun step A₀ (l.take T)).card : ℝ) <
          (A₀.card : ℝ) * (1 + c / 23) ^ T := by
        have : ((roundRun step A₀ (l.take T)).card : ℝ) < (Fintype.card V : ℝ) := by
          exact_mod_cast hcardlt
        linarith [hgrowT]
      have hnotin : roundRun (stepFreeze step (Fintype.card V)) A₀ (l.take T) ∉
          largeTarget A₀ (c / 23) T := by
        rw [heqrun]
        refine not_or.mpr ⟨Nat.not_le.mpr (hall T le_rfl), not_le.mpr hltgrow⟩
      rw [if_neg hnotin]
    · rw [if_neg hall]
      split_ifs <;> norm_num
  have htake := expList_take (R := R) T (fun l =>
    if roundRun (stepFreeze step (Fintype.card V)) A₀ l ∈ largeTarget A₀ (c / 23) T
      then (0 : ℝ) else 1)
  have hfold : expList R T (fun l =>
        if roundRun (stepFreeze step (Fintype.card V)) A₀ l ∈ largeTarget A₀ (c / 23) T
          then (0 : ℝ) else 1) =
      expList R T (fun l => by classical exact
        (if l.foldl (stepFreeze step (Fintype.card V)) A₀ ∈ largeTarget A₀ (c / 23) T
          then (0 : ℝ) else 1)) := by
    refine congrArg (expList R T) (funext fun l => ?_)
    simp [roundRun]
  calc expList R T (fun l =>
        if ∀ s ≤ T, 10 * (roundRun step A₀ (l.take s)).card < 9 * Fintype.card V
          then (1 : ℝ) else 0)
      ≤ expList R T (fun l =>
          if roundRun (stepFreeze step (Fintype.card V)) A₀ (l.take T) ∈
              largeTarget A₀ (c / 23) T then (0 : ℝ) else 1) :=
        expList_le_expList hpoint
    _ = expList R T (fun l =>
          if roundRun (stepFreeze step (Fintype.card V)) A₀ l ∈ largeTarget A₀ (c / 23) T
            then (0 : ℝ) else 1) := htake
    _ = expList R T (fun l => by classical exact
          (if l.foldl (stepFreeze step (Fintype.card V)) A₀ ∈ largeTarget A₀ (c / 23) T
            then (0 : ℝ) else 1)) := hfold
    _ ≤ T * (Fintype.card V : ℝ) ^ (-5 : ℝ) := hesc
    _ = T / (Fintype.card V : ℝ) ^ 5 := by
        have hpow : (Fintype.card V : ℝ) ^ (-5 : ℝ) = ((Fintype.card V : ℝ) ^ 5)⁻¹ := by
          have hsign : (-5 : ℝ) = -((5 : ℕ) : ℝ) := by norm_num
          rw [hsign, rpow_neg (Nat.cast_nonneg _), rpow_natCast]
        rw [hpow]
        exact (div_eq_mul_inv (T : ℝ) _).symm

end Epidemics
