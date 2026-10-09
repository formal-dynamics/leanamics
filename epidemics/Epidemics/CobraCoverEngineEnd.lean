import Epidemics.CobraCoverEngineLarge

/-! # Generic end phase (EPI-4, Lemma 4)

Once `|A| ≥ 9n/10` and `4000 log n/c² ≤ 9n/10`, one round stays above `9n/10` except with
probability `n^{-8}`, and the expected number of healthy vertices contracts by
`θ = 1 - (9/10) c`. The scalar bounds are in `CobraCoverNumerics`.
-/

namespace Epidemics

open Finset Dynamics Real

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R]

omit [DecidableEq V] [Nonempty R] in
/-- From `|A| ≥ 9n/10`, one round falls below `9n/10` with probability at most `n^{-8}`. -/
lemma round_drop_prob (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hchernoff : ∀ (A : Finset V) (δ μ : ℝ), 0 < δ → δ < 1 →
      μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) →
      avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (-(δ ^ 2 * μ / 2)))
    (hmono : ∀ (A B : Finset V) (ρ : R), A ⊆ B → step A ρ ⊆ step B ρ)
    (hn : 2 ≤ Fintype.card V)
    (hgap : 4000 * log (Fintype.card V) / c ^ 2 ≤ (9 / 10) * (Fintype.card V : ℝ))
    {A : Finset V} (hA : 9 * Fintype.card V ≤ 10 * A.card) :
    avg (fun ρ => if 10 * (step A ρ).card < 9 * Fintype.card V then (1 : ℝ) else 0) ≤
      (Fintype.card V : ℝ) ^ (-8 : ℝ) := by
  classical
  have hnbig : 32769 ≤ Fintype.card V := end_n_ge hc0 hc1 hn hgap
  let n : ℕ := Fintype.card V
  have hnR : (32769 : ℝ) ≤ (n : ℝ) := by
    unfold n
    exact_mod_cast hnbig
  have hn0 : (0 : ℝ) < n := by
    unfold n
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hlog : 0 < log (n : ℝ) := log_pos (by
    unfold n
    exact_mod_cast (show 1 < Fintype.card V by omega))
  have hAreal : (9 : ℝ) * (n : ℝ) / 10 ≤ (A.card : ℝ) := by
    have hcast : (9 : ℝ) * (n : ℝ) ≤ (10 : ℝ) * (A.card : ℝ) := by
      unfold n
      exact_mod_cast hA
    rw [div_le_iff₀ (by norm_num)]
    linarith
  let s : ℕ := Nat.ceil ((9 : ℝ) * (n : ℝ) / 10)
  have hsA : s ≤ A.card := by
    rw [Nat.ceil_le]
    exact hAreal
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hsA
  have hSge : (9 : ℝ) * (n : ℝ) / 10 ≤ (S.card : ℝ) := by
    rw [hScard]
    exact Nat.le_ceil _
  have hS4000 : 4000 * log (n : ℝ) / c ^ 2 ≤ (S.card : ℝ) := by
    unfold n at hSge ⊢
    refine le_trans ?_ hSge
    have heq : (9 / 10) * (Fintype.card V : ℝ) = (9 : ℝ) * (Fintype.card V : ℝ) / 10 := by ring
    rw [← heq]
    exact hgap
  have hS0 : (0 : ℝ) < (S.card : ℝ) := by
    have hpos : (0 : ℝ) < (9 : ℝ) * (n : ℝ) / 10 := div_pos (mul_pos (by norm_num) hn0) (by norm_num)
    linarith
  have hSlt : (S.card : ℝ) < (9 : ℝ) * (n : ℝ) / 10 + 1 := by
    rw [hScard]
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hn0.le) (by norm_num))
  have hfrac : 1 / 10 - 1 / (n : ℝ) ≤ 1 - (S.card : ℝ) / (n : ℝ) := by
    have hSle : (S.card : ℝ) ≤ (9 / 10) * (n : ℝ) + 1 := by
      have heq : (9 : ℝ) * (n : ℝ) / 10 = (9 / 10) * (n : ℝ) := by ring
      linarith
    have hdiv : (S.card : ℝ) / (n : ℝ) ≤ 9 / 10 + 1 / (n : ℝ) := by
      rw [div_le_iff₀ hn0]
      have heq : (9 / 10 + 1 / (n : ℝ)) * (n : ℝ) = (9 / 10) * (n : ℝ) + 1 := by
        field_simp
      linarith
    linarith
  let μ : ℝ := (S.card : ℝ) * (1 + c * (1 / 10 - 1 / (n : ℝ)))
  have hμE : μ ≤ avg (fun ρ => ((step S ρ).card : ℝ)) := by
    have hlin : 1 + c * (1 / 10 - 1 / (n : ℝ)) ≤
        1 + c * (1 - (S.card : ℝ) / (n : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hfrac hc0.le
      linarith
    calc μ ≤ (S.card : ℝ) * (1 + c * (1 - (S.card : ℝ) / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg _)
      _ ≤ avg (fun ρ => ((step S ρ).card : ℝ)) := by
          unfold n
          exact hgrowth S
  let eps : ℝ := sqrt (16 * log (n : ℝ) / (S.card : ℝ))
  have heps_sq : eps ^ 2 = 16 * log (n : ℝ) / (S.card : ℝ) :=
    sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hlog.le) hS0.le)
  have heps_le : eps ≤ (8 / 125) * c := eps_le_eight hc0 hlog hS4000
  have heps0 : 0 < eps := by
    rw [sqrt_pos]
    exact div_pos (mul_pos (by norm_num) hlog) hS0
  have heps1 : eps < 1 := by
    have h8 : (8 / 125) * c ≤ 8 / 125 := by
      calc (8 / 125) * c ≤ (8 / 125) * 1 :=
            mul_le_mul_of_nonneg_left hc1 (by norm_num : (0 : ℝ) ≤ 8 / 125)
        _ = 8 / 125 := by ring
    linarith [show (8 : ℝ) / 125 < 1 by norm_num]
  have hch := hchernoff S eps μ heps0 heps1 hμE
  have hratio : (S.card : ℝ) ≤ μ := by
    have h10 : (10 : ℝ) ≤ n := by
      have hnat : 10 ≤ n := by
        unfold n
        omega
      exact_mod_cast hnat
    have hinv : (1 : ℝ) / (n : ℝ) ≤ 1 / 10 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h10
    have hfactor : (1 : ℝ) ≤ 1 + c * (1 / 10 - 1 / (n : ℝ)) := by
      have hnonneg : 0 ≤ c * (1 / 10 - 1 / (n : ℝ)) := mul_nonneg hc0.le (by linarith)
      linarith
    simpa [μ] using mul_le_mul_of_nonneg_left hfactor hS0.le
  have hrate : 8 * log (n : ℝ) ≤ eps ^ 2 * μ / 2 := by
    rw [heps_sq]
    have hrewrite : (16 * log (n : ℝ) / (S.card : ℝ)) * μ / 2 =
        8 * log (n : ℝ) * (μ / (S.card : ℝ)) := by
      field_simp
      ring
    rw [hrewrite]
    have hdiv : (1 : ℝ) ≤ μ / (S.card : ℝ) := by
      rw [le_div_iff₀ hS0]
      simpa [one_mul] using hratio
    simpa [mul_one] using
      mul_le_mul_of_nonneg_left hdiv (mul_nonneg (by norm_num) hlog.le)
  have hexp : exp (-(eps ^ 2 * μ / 2)) ≤ (n : ℝ) ^ (-8 : ℝ) := by
    have hle : exp (-(eps ^ 2 * μ / 2)) ≤ exp (-(8 * log (n : ℝ))) :=
      (exp_le_exp).mpr (by linarith)
    have heq : exp (-(8 * log (n : ℝ))) = (n : ℝ) ^ (-8 : ℝ) := by
      have : -(8 * log (n : ℝ)) = log (n : ℝ) * (-8) := by ring
      rw [this, ← rpow_def_of_pos hn0]
    exact hle.trans (le_of_eq heq)
  have hfac := stay_factor hc0.le hc1 hnR
  have hprodS : (S.card : ℝ) ≤ (1 - (8 / 125) * c) * μ := by
    have heq : (1 - (8 / 125) * c) * μ =
        (S.card : ℝ) *
          ((1 - (8 / 125) * c) * (1 + c * (1 / 10 - 1 / (n : ℝ)))) := by
      simp only [μ]
      ring
    rw [heq]
    have hmul : (S.card : ℝ) * 1 ≤
        (S.card : ℝ) * ((1 - (8 / 125) * c) * (1 + c * (1 / 10 - 1 / (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg S.card)
    simpa [mul_one] using hmul
  have hcomp : (1 - (8 / 125) * c) * μ ≤ (1 - eps) * μ := by
    exact mul_le_mul_of_nonneg_right (by linarith : 1 - (8 / 125) * c ≤ 1 - eps)
      (le_trans (Nat.cast_nonneg _) hratio)
  have hcut : (9 : ℝ) * (n : ℝ) / 10 ≤ (1 - eps) * μ := by linarith
  unfold n at hexp
  refine (avg_le_avg fun ρ => ?_).trans (hch.trans hexp)
  by_cases hdrop : 10 * (step A ρ).card < 9 * Fintype.card V
  · rw [if_pos hdrop]
    have hcard : (step S ρ).card ≤ (step A ρ).card :=
      Finset.card_le_card (hmono S A ρ hSsub)
    have hdropS : 10 * (step S ρ).card < 9 * Fintype.card V := by omega
    have hreal : ((step S ρ).card : ℝ) < (9 : ℝ) * (n : ℝ) / 10 := by
      have h10 : (10 : ℝ) * ((step S ρ).card : ℝ) < (9 : ℝ) * (n : ℝ) := by
        unfold n
        exact_mod_cast hdropS
      rw [lt_div_iff₀ (by norm_num)]
      linarith
    have hleρ : ((step S ρ).card : ℝ) ≤ (1 - eps) * μ := by linarith
    rw [if_pos hleρ]
  · rw [if_neg hdrop]
    split_ifs <;> norm_num

omit [DecidableEq V] in
/-- After `t` rounds starting from `|A₀| ≥ 9n/10`, `P(10|A_t| < 9n) ≤ t n^{-8}`. -/
lemma round_below_prob (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hchernoff : ∀ (A : Finset V) (δ μ : ℝ), 0 < δ → δ < 1 →
      μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) →
      avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (-(δ ^ 2 * μ / 2)))
    (hmono : ∀ (A B : Finset V) (ρ : R), A ⊆ B → step A ρ ⊆ step B ρ)
    (hn : 2 ≤ Fintype.card V)
    (hgap : 4000 * log (Fintype.card V) / c ^ 2 ≤ (9 / 10) * (Fintype.card V : ℝ))
    (t : ℕ) {A₀ : Finset V} (hA₀ : 9 * Fintype.card V ≤ 10 * A₀.card) :
    expList R t (fun l =>
      if 9 * Fintype.card V ≤ 10 * (roundRun step A₀ l).card then (0 : ℝ) else 1) ≤
      (t : ℝ) * (Fintype.card V : ℝ) ^ (-8 : ℝ) := by
  classical
  have hp : 0 ≤ (Fintype.card V : ℝ) ^ (-8 : ℝ) := by positivity
  let Gset : ℕ → Set (Finset V) := fun _ => {A | 9 * Fintype.card V ≤ 10 * A.card}
  have hstart : A₀ ∈ Gset 0 := by simpa [Gset] using hA₀
  refine le_of_eq_of_le ?eq (expList_escape step hp t Gset A₀ hstart ?step)
  case eq =>
    refine congrArg (expList R t) (funext fun l => ?_)
    simp only [roundRun, Gset, Set.mem_setOf_eq]
    by_cases h : 9 * Fintype.card V ≤ 10 * (l.foldl step A₀).card
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  case step =>
    intro s _h y hy
    have hy' : 9 * Fintype.card V ≤ 10 * y.card := by simpa [Gset] using hy
    have hdrop := round_drop_prob step hc0 hc1 hgrowth hchernoff hmono hn hgap hy'
    refine (le_of_eq ?_).trans hdrop
    refine congrArg avg (funext fun ρ => ?_)
    by_cases hmem : 9 * Fintype.card V ≤ 10 * (step y ρ).card
    · have hin : step y ρ ∈ Gset (s + 1) := by simpa [Gset] using hmem
      rw [if_pos hin, if_neg (Nat.not_lt.mpr hmem)]
    · have hout : step y ρ ∉ Gset (s + 1) := by simpa [Gset] using hmem
      rw [if_neg hout, if_pos (Nat.not_le.mp hmem)]

/-- Expected number of healthy vertices. -/
noncomputable def endHealthy (step : Finset V → R → Finset V) (A₀ : Finset V) (t : ℕ) : ℝ :=
  expList R t fun l => (Fintype.card V : ℝ) - ((roundRun step A₀ l).card : ℝ)

omit [DecidableEq V] [Nonempty R] in
lemma endHealthy_succ (step : Finset V → R → Finset V) (A₀ : Finset V) (t : ℕ) :
    endHealthy step A₀ (t + 1) =
      expList R t (fun l =>
        avg (fun ρ => (Fintype.card V : ℝ) - ((step (roundRun step A₀ l) ρ).card : ℝ))) := by
  unfold endHealthy
  rw [expList_append t 1]
  refine congrArg (expList R t) (funext fun l => ?_)
  rw [expList_succ]
  simp only [expList_zero]
  refine congrArg avg (funext fun ρ => ?_)
  rw [roundRun_append, roundRun_cons, roundRun_nil]

omit [DecidableEq V] in
/-- One round: `E(n - |A'|) ≤ θ (n - |A|) + n 1_{10|A| < 9n}`, with `θ = 1 - (9/10) c`. -/
lemma endGap_step (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hn : 0 < Fintype.card V) (A : Finset V) :
    avg (fun ρ => (Fintype.card V : ℝ) - ((step A ρ).card : ℝ)) ≤
      (1 - (9 / 10) * c) * ((Fintype.card V : ℝ) - A.card) +
        (Fintype.card V : ℝ) * (if 9 * Fintype.card V ≤ 10 * A.card then (0 : ℝ) else 1) := by
  let n : ℝ := Fintype.card V
  have hn0 : (0 : ℝ) < n := by
    unfold n
    exact_mod_cast hn
  have hcard_le : (A.card : ℝ) ≤ n := by
    unfold n
    exact_mod_cast Finset.card_le_univ A
  have hnn : 0 ≤ n - (A.card : ℝ) := by linarith
  have havg : avg (fun ρ => n - ((step A ρ).card : ℝ)) =
      n - avg (fun ρ => ((step A ρ).card : ℝ)) := by
    rw [avg_sub (fun _ => n) (fun ρ => ((step A ρ).card : ℝ)), avg_const]
  have hsub : n - avg (fun ρ => ((step A ρ).card : ℝ)) ≤
      n - (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / n)) := by
    linarith [hgrowth A]
  have hlin : n - (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / n)) =
      (n - (A.card : ℝ)) * (1 - c * (A.card : ℝ) / n) := by
    field_simp
    ring
  have hleft : avg (fun ρ => n - ((step A ρ).card : ℝ)) ≤
      (n - (A.card : ℝ)) * (1 - c * (A.card : ℝ) / n) := by
    rw [havg]
    exact hsub.trans_eq hlin
  by_cases habove : 9 * Fintype.card V ≤ 10 * A.card
  · rw [if_pos habove, mul_zero, add_zero]
    have hfrac : (9 : ℝ) / 10 ≤ (A.card : ℝ) / n := by
      have hcast : (9 : ℝ) * n ≤ (10 : ℝ) * (A.card : ℝ) := by
        unfold n
        exact_mod_cast habove
      rw [le_div_iff₀ hn0]
      linarith
    have hcoef : 1 - c * (A.card : ℝ) / n ≤ 1 - (9 / 10) * c := by
      have : (9 / 10) * c ≤ c * (A.card : ℝ) / n := by
        calc (9 / 10) * c = c * (9 / 10) := by ring
          _ ≤ c * ((A.card : ℝ) / n) := mul_le_mul_of_nonneg_left hfrac hc0.le
          _ = c * (A.card : ℝ) / n := by ring
      linarith
    have hmul := mul_le_mul_of_nonneg_left hcoef hnn
    have hcomm : (n - (A.card : ℝ)) * (1 - (9 / 10) * c) =
        (1 - (9 / 10) * c) * ((Fintype.card V : ℝ) - (A.card : ℝ)) := by
      unfold n
      ring
    exact le_trans hleft (hcomm ▸ hmul)
  · rw [if_neg habove, mul_one]
    have hcardnn : 0 ≤ avg (fun ρ => ((step A ρ).card : ℝ)) :=
      avg_nonneg fun ρ => by exact_mod_cast Nat.zero_le (step A ρ).card
    have hle_n : avg (fun ρ => n - ((step A ρ).card : ℝ)) ≤ n := by
      rw [havg]
      linarith
    have hθ : 0 ≤ (1 - (9 / 10) * c) * (n - (A.card : ℝ)) := by
      have hle : (9 / 10) * c ≤ (9 / 10) * 1 :=
        mul_le_mul_of_nonneg_left hc1 (by norm_num : (0 : ℝ) ≤ 9 / 10)
      have hθ0 : 0 ≤ 1 - (9 / 10) * c := by
        linarith [show (9 : ℝ) / 10 * 1 ≤ 1 by norm_num]
      exact mul_nonneg hθ0 hnn
    linarith

omit [DecidableEq V] in
lemma endHealthy_rec (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hchernoff : ∀ (A : Finset V) (δ μ : ℝ), 0 < δ → δ < 1 →
      μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) →
      avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (-(δ ^ 2 * μ / 2)))
    (hmono : ∀ (A B : Finset V) (ρ : R), A ⊆ B → step A ρ ⊆ step B ρ)
    (hn : 2 ≤ Fintype.card V)
    (hgap : 4000 * log (Fintype.card V) / c ^ 2 ≤ (9 / 10) * (Fintype.card V : ℝ))
    {A₀ : Finset V} (hA₀ : 9 * Fintype.card V ≤ 10 * A₀.card) (t : ℕ) :
    endHealthy step A₀ (t + 1) ≤
      (1 - (9 / 10) * c) * endHealthy step A₀ t + (t : ℝ) * (Fintype.card V : ℝ) ^ (-7 : ℝ) := by
  let n : ℝ := Fintype.card V
  have hn0 : (0 : ℝ) < n := by
    unfold n
    exact_mod_cast (show 0 < Fintype.card V by omega)
  rw [endHealthy_succ]
  have hpoint (l : List R) :
      avg (fun ρ => (Fintype.card V : ℝ) - ((step (roundRun step A₀ l) ρ).card : ℝ)) ≤
        (1 - (9 / 10) * c) * ((Fintype.card V : ℝ) - ((roundRun step A₀ l).card : ℝ)) +
          (Fintype.card V : ℝ) *
            (if 9 * Fintype.card V ≤ 10 * (roundRun step A₀ l).card then (0 : ℝ) else 1) :=
    endGap_step step hc0 hc1 hgrowth (by omega) (roundRun step A₀ l)
  refine (expList_le_expList hpoint).trans ?_
  have hsplit :
      expList R t (fun l =>
        (1 - (9 / 10) * c) * ((Fintype.card V : ℝ) - ((roundRun step A₀ l).card : ℝ)) +
          (Fintype.card V : ℝ) *
            (if 9 * Fintype.card V ≤ 10 * (roundRun step A₀ l).card then (0 : ℝ) else 1)) =
        (1 - (9 / 10) * c) * endHealthy step A₀ t +
          (Fintype.card V : ℝ) * expList R t (fun l =>
            if 9 * Fintype.card V ≤ 10 * (roundRun step A₀ l).card then (0 : ℝ) else 1) := by
    rw [expList_add, expList_const_mul, expList_const_mul]
    rfl
  rw [hsplit]
  have hbelow := round_below_prob step hc0 hc1 hgrowth hchernoff hmono hn hgap t hA₀
  have hnpos : (0 : ℝ) ≤ Fintype.card V := by exact_mod_cast Nat.zero_le (Fintype.card V)
  have hmul := mul_le_mul_of_nonneg_left hbelow hnpos
  have hpow : n * (n ^ (-8 : ℝ)) = n ^ (-7 : ℝ) := by
    have h := (rpow_add hn0 (1 : ℝ) (-8 : ℝ)).symm
    have hexp : (1 : ℝ) + (-8) = -7 := by norm_num
    simpa [rpow_one, hexp] using h
  have hscale : (Fintype.card V : ℝ) * ((t : ℝ) * (Fintype.card V : ℝ) ^ (-8 : ℝ)) =
      (t : ℝ) * (Fintype.card V : ℝ) ^ (-7 : ℝ) := by
    unfold n at hpow
    calc (Fintype.card V : ℝ) * ((t : ℝ) * (Fintype.card V : ℝ) ^ (-8 : ℝ))
        = (t : ℝ) * ((Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (-8 : ℝ)) := by ring
      _ = (t : ℝ) * (Fintype.card V : ℝ) ^ (-7 : ℝ) := by rw [hpow]
  linarith

omit [DecidableEq V] in
lemma endHealthy_le (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hchernoff : ∀ (A : Finset V) (δ μ : ℝ), 0 < δ → δ < 1 →
      μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) →
      avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (-(δ ^ 2 * μ / 2)))
    (hmono : ∀ (A B : Finset V) (ρ : R), A ⊆ B → step A ρ ⊆ step B ρ)
    (hn : 2 ≤ Fintype.card V)
    (hgap : 4000 * log (Fintype.card V) / c ^ 2 ≤ (9 / 10) * (Fintype.card V : ℝ))
    {A₀ : Finset V} (hA₀ : 9 * Fintype.card V ≤ 10 * A₀.card) (t : ℕ) :
    endHealthy step A₀ t ≤
      (1 - (9 / 10) * c) ^ t * ((Fintype.card V : ℝ) / 10) +
        (t : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (-7 : ℝ) := by
  induction t with
  | zero =>
    rw [endHealthy]
    simp [roundRun_nil, pow_zero]
    have : (9 : ℝ) * (Fintype.card V : ℝ) ≤ (10 : ℝ) * (A₀.card : ℝ) := by exact_mod_cast hA₀
    linarith
  | succ t ih =>
    have hrec := endHealthy_rec step hc0 hc1 hgrowth hchernoff hmono hn hgap hA₀ t
    have hθ0 : 0 ≤ 1 - (9 / 10) * c := by
      have hle : (9 / 10) * c ≤ (9 / 10) * 1 :=
        mul_le_mul_of_nonneg_left hc1 (by norm_num : (0 : ℝ) ≤ 9 / 10)
      linarith [show (9 : ℝ) / 10 * 1 ≤ 1 by norm_num]
    have hθ1 : 1 - (9 / 10) * c ≤ 1 := by
      have : 0 ≤ (9 / 10) * c := mul_nonneg (by norm_num) hc0.le
      linarith
    have hsq : (t : ℝ) ^ 2 + (t : ℝ) ≤ ((t + 1 : ℕ) : ℝ) ^ 2 := by
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by norm_cast
      nlinarith
    have hneg : 0 ≤ (Fintype.card V : ℝ) ^ (-7 : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left ih hθ0
    have hexpand : (1 - (9 / 10) * c) *
          ((1 - (9 / 10) * c) ^ t * ((Fintype.card V : ℝ) / 10) +
            (t : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (-7 : ℝ)) =
        (1 - (9 / 10) * c) ^ (t + 1) * ((Fintype.card V : ℝ) / 10) +
          (1 - (9 / 10) * c) * ((t : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (-7 : ℝ)) := by
      rw [mul_add, pow_succ']
      ring
    have hdrop : (1 - (9 / 10) * c) * ((t : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (-7 : ℝ)) ≤
        (t : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (-7 : ℝ) := by
      have := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg (sq_nonneg (t : ℝ)) hneg)
      linarith
    have hsquare := mul_le_mul_of_nonneg_right hsq hneg
    linarith

lemma fail_le_gap (A : Finset V) :
    (if A = univ then (0 : ℝ) else 1) ≤ (Fintype.card V : ℝ) - (A.card : ℝ) := by
  classical
  by_cases h : A = univ
  · simp [h, Finset.card_univ]
  · rw [if_neg h]
    have hlt : A.card < Fintype.card V := (Finset.card_lt_iff_ne_univ A).2 h
    have : (A.card : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith

omit [DecidableEq V] [Fintype R] [Nonempty R] in
lemma roundRun_of_univ (step : Finset V → R → Finset V) (huniv : ∀ ρ, step univ ρ = univ)
    (l : List R) : roundRun step univ l = univ := by
  induction l with
  | nil => rfl
  | cons ρ l ih => rw [roundRun_cons, huniv, ih]

omit [Fintype R] [Nonempty R] in
lemma fail_append_le (step : Finset V → R → Finset V) (huniv : ∀ ρ, step univ ρ = univ)
    (A₀ : Finset V) (l₁ l₂ : List R) :
    (if roundRun step A₀ (l₁ ++ l₂) = univ then (0 : ℝ) else 1) ≤
      (if roundRun step A₀ l₁ = univ then (0 : ℝ) else 1) := by
  classical
  by_cases h : roundRun step A₀ l₁ = univ
  · rw [if_pos h, roundRun_append, h, roundRun_of_univ step huniv, if_pos rfl]
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- **Lemma 4, generic form.** From `|A₀| ≥ 9n/10`, under `4000 log n/c² ≤ (9/10) n`, the
probability that time `T ≥ 8 log n/c` has not infected every vertex is at most `n^{-5}`. -/
lemma round_end_phase (step : Finset V → R → Finset V) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hgrowth : ∀ A : Finset V,
      (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ => ((step A ρ).card : ℝ)))
    (hchernoff : ∀ (A : Finset V) (δ μ : ℝ), 0 < δ → δ < 1 →
      μ ≤ avg (fun ρ => ((step A ρ).card : ℝ)) →
      avg (fun ρ => if ((step A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
        exp (-(δ ^ 2 * μ / 2)))
    (hmono : ∀ (A B : Finset V) (ρ : R), A ⊆ B → step A ρ ⊆ step B ρ)
    (huniv : ∀ ρ, step univ ρ = univ)
    (hn : 2 ≤ Fintype.card V)
    (hgap : 4000 * log (Fintype.card V) / c ^ 2 ≤ (9 / 10) * (Fintype.card V : ℝ))
    {A₀ : Finset V} (hA₀ : 9 * Fintype.card V ≤ 10 * A₀.card) {T : ℕ}
    (hT : 8 * log (Fintype.card V) / c ≤ T) :
    expList R T (fun l => if roundRun step A₀ l = univ then (0 : ℝ) else 1) ≤
      1 / (Fintype.card V : ℝ) ^ 5 := by
  classical
  let T₀ : ℕ := Nat.ceil (8 * log (Fintype.card V) / c)
  have hT₀ : T₀ ≤ T := by
    rw [Nat.ceil_le]
    exact hT
  have hfail : expList R T₀ (fun l => if roundRun step A₀ l = univ then (0 : ℝ) else 1) ≤
      endHealthy step A₀ T₀ :=
    expList_le_expList fun l => fail_le_gap (roundRun step A₀ l)
  have hhealthy := endHealthy_le step hc0 hc1 hgrowth hchernoff hmono hn hgap hA₀ T₀
  have hnum := end_tail_small hc0 hc1 hn hgap (n := Fintype.card V) rfl
  have hT₀bound : expList R T₀ (fun l => if roundRun step A₀ l = univ then (0 : ℝ) else 1) ≤
      1 / (Fintype.card V : ℝ) ^ 5 := by
    linarith
  have hsplit : expList R T (fun l => if roundRun step A₀ l = univ then (0 : ℝ) else 1) =
      expList R T₀ (fun l₁ => expList R (T - T₀) (fun l₂ =>
        if roundRun step A₀ (l₁ ++ l₂) = univ then (0 : ℝ) else 1)) := by
    have hTeq : T = T₀ + (T - T₀) := by omega
    conv_lhs => rw [hTeq]
    exact expList_append T₀ (T - T₀) _
  rw [hsplit]
  refine (expList_le_expList fun l₁ => ?_).trans hT₀bound
  refine le_trans (expList_le_expList fun l₂ => fail_append_le step huniv A₀ l₁ l₂) ?_
  rw [expList_const]

end Epidemics
