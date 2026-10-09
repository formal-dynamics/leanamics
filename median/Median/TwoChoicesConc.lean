import Median.TwoChoicesExpect
import Dynamics.Concentration

/-! # One-round Bernstein bounds for 2-Choices

The variance of a node's contribution to a colour count, or to the gap between two colours, is of
order `a²/n` when every colour has at most `a` nodes (a node of the tracked colour moves with
probability at most `a/n`, and a node of another colour joins with probability at most `a²/n²`).
Bernstein's inequality with this variance replaces the paper's multiplicative Chernoff bounds and
needs no restriction on the number of colours.
-/

namespace Median.TwoChoices
open Finset Dynamics Real

/-- `𝔼[(f - y₀)²] = Var(f) + (𝔼f - y₀)²`, so the variance is at most the second moment about any
constant. -/
lemma avg_sq_sub_eq {γ : Type*} [Fintype γ] [Nonempty γ] (f : γ → ℝ) (y₀ : ℝ) :
    avg (fun y => (f y - y₀) ^ 2) = variance f + (avg f - y₀) ^ 2 := by
  have h (y : γ) : (f y - y₀) ^ 2
      = (f y - avg f) ^ 2 + 2 * (avg f - y₀) * (f y - avg f) + (avg f - y₀) ^ 2 := by ring
  simp_rw [h, avg_add, avg_const_mul, avg_const]
  have hc : avg (fun y => f y - avg f) = 0 := by rw [avg_sub, avg_const, sub_self]
  rw [hc, mul_zero, add_zero]
  rfl

lemma variance_le_avg_sub {γ : Type*} [Fintype γ] [Nonempty γ] (f : γ → ℝ) (y₀ : ℝ) :
    variance f ≤ avg (fun y => (f y - y₀) ^ 2) := by
  rw [avg_sq_sub_eq]
  exact le_add_of_nonneg_right (sq_nonneg _)

variable {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α] [NeZero n]

/-- The probability that one fixed node adopts colour `i`. -/
lemma avg_rule (x : Config n α) (i : α) (v : Fin n) :
    avg (fun p : Fin n × Fin n => if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
      = ((count x i : ℝ) / n) ^ 2
        + (if x v = i then (1 : ℝ) else 0) * (1 - ∑ j : α, ((count x j : ℝ) / n) ^ 2) := by
  have hmarg := Dynamics.avg_eval n v
    (fun p : Fin n × Fin n => if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
  exact hmarg.symm.trans (avg_step_node x i v)

/-- A node that already holds `i` leaves it with probability `∑_{j ≠ i} (c_j/n)²`. -/
lemma avg_leave (x : Config n α) (i : α) (v : Fin n) (hv : x v = i) :
    avg (fun p : Fin n × Fin n => if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0)
      = ∑ j ∈ univ.erase i, ((count x j : ℝ) / n) ^ 2 := by
  haveI : Nonempty (Fin n × Fin n) := ⟨((0 : Fin n), (0 : Fin n))⟩
  have hstay := avg_rule x i v
  rw [if_pos hv, one_mul] at hstay
  have hrest : ∑ j : α, ((count x j : ℝ) / n) ^ 2
      = ((count x i : ℝ) / n) ^ 2 + ∑ j ∈ univ.erase i, ((count x j : ℝ) / n) ^ 2 :=
    (add_sum_erase (univ : Finset α) _ (mem_univ i)).symm
  have hstay' : avg (fun (p : Fin n × Fin n) =>
      if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
      = 1 - ∑ j ∈ univ.erase i, ((count x j : ℝ) / n) ^ 2 := by
    rw [hstay, hrest]
    ring
  have hone (p : Fin n × Fin n) :
      (if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
        + (if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0) = 1 := by
    by_cases h : rule (x v) (x p.1) (x p.2) = i
    · simp [h]
    · simp [h]
  have havg := congrArg avg (funext hone)
  rw [avg_add, avg_const] at havg
  linarith

omit [DecidableEq α] [Fintype α] [NeZero n] in
lemma sum_sq_div (s : Finset α) (f : α → ℕ) :
    ∑ j ∈ s, ((f j : ℝ) / n) ^ 2 = (∑ j ∈ s, (f j : ℝ) ^ 2) / n ^ 2 := by
  simp_rw [div_pow, ← sum_div]

omit [NeZero n] in
/-- `∑_{j ≠ i} c_j² ≤ a n` when `a` bounds every count. -/
lemma sum_sq_erase_le (x : Config n α) (i : α) {a : ℝ}
    (ha : ∀ l, (count x l : ℝ) ≤ a) (ha0 : 0 ≤ a) :
    ∑ j ∈ univ.erase i, (count x j : ℝ) ^ 2 ≤ a * n := by
  have hsum : ∑ j ∈ univ.erase i, (count x j : ℝ) ≤ (n : ℝ) := by
    have hs : (count x i : ℝ) + ∑ j ∈ univ.erase i, (count x j : ℝ) = (n : ℝ) := by
      have h := sum_count x
      rw [← add_sum_erase (univ : Finset α) (fun j => count x j) (mem_univ i)] at h
      exact_mod_cast h
    have hle_sum : ∑ j ∈ univ.erase i, (count x j : ℝ)
        ≤ (count x i : ℝ) + ∑ j ∈ univ.erase i, (count x j : ℝ) :=
      le_add_of_nonneg_left (Nat.cast_nonneg _)
    exact hle_sum.trans_eq hs
  have hle : ∑ j ∈ univ.erase i, (count x j : ℝ) ^ 2
      ≤ ∑ j ∈ univ.erase i, a * (count x j : ℝ) := by
    refine sum_le_sum fun l _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_right (ha l) (Nat.cast_nonneg _)
  rw [← mul_sum] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left hsum ha0)

/-- Lower tail of the gap `c_i' - c_j'`. If `a = c_i` bounds every colour and `a > 0`, then
`P(c_i' - c_j' ≤ 𝔼[c_i' - c_j'] - λ) ≤ exp(-λ² / (20 a²/n + 4λ/3))`. -/
lemma gap_dev_le (x : Config n α) (i j : α) (hij : j ≠ i)
    (ha : ∀ l, count x l ≤ count x i) (hpos : 0 < count x i) {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun r : Round n =>
        if (count (step x r) i : ℝ) - count (step x r) j
            ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ) - count (step x ρ) j) - lam
          then (1 : ℝ) else 0)
      ≤ exp (-(lam ^ 2 / (20 * (count x i : ℝ) ^ 2 / n + 4 * lam / 3))) := by
  haveI : Nonempty (Fin n × Fin n) := ⟨((0 : Fin n), (0 : Fin n))⟩
  haveI : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set a : ℝ := (count x i : ℝ) with ha_def
  have ha0 : 0 < a := by rw [ha_def]; exact_mod_cast hpos
  have hbound : ∀ l, (count x l : ℝ) ≤ a := fun l => by rw [ha_def]; exact_mod_cast ha l
  let Y : Fin n → Fin n × Fin n → ℝ := fun v p =>
    (if rule (x v) (x p.1) (x p.2) = j then (1 : ℝ) else 0)
      - (if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
  have hYge (v) (p) : -1 ≤ Y v p := by
    have h1 : (0 : ℝ) ≤ (if rule (x v) (x p.1) (x p.2) = j then 1 else 0) := by
      split_ifs <;> norm_num
    have h2 : (if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    linarith
  have hYle (v) (p) : Y v p ≤ 1 := by
    have h1 : (if rule (x v) (x p.1) (x p.2) = j then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ (if rule (x v) (x p.1) (x p.2) = i then 1 else 0) := by
      split_ifs <;> norm_num
    linarith
  have havg (v) : -1 ≤ avg (Y v) := by
    calc -1 = avg (fun _ : Fin n × Fin n => (-1 : ℝ)) := (avg_const _).symm
      _ ≤ avg (Y v) := avg_le_avg (hYge v)
  have hYb (v) (p) : Y v p - avg (Y v) ≤ 2 := by linarith [hYle v p, havg v]
  have hleave_le (col : α) (v : Fin n) (hv : x v = col) :
      avg (fun (p : Fin n × Fin n) => if rule (x v) (x p.1) (x p.2) ≠ col then (1 : ℝ) else 0) ≤ a / n := by
    rw [avg_leave x col v hv, sum_sq_div]
    have hsq := sum_sq_erase_le x col hbound ha0.le
    have hdiv : (∑ l ∈ univ.erase col, (count x l : ℝ) ^ 2) / n ^ 2 ≤ a * n / n ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have heq : a * n / n ^ 2 = a / n := by field_simp
    linarith
  have hvar (v : Fin n) : variance (Y v) ≤
      (if x v = i then 4 * a / n else 0) + (if x v = j then 4 * a / n else 0)
        + (if x v ≠ i ∧ x v ≠ j then 2 * a ^ 2 / n ^ 2 else 0) := by
    by_cases hvi : x v = i
    · have hvj : x v ≠ j := fun h => hij (h.symm.trans hvi)
      have hnot : ¬ (x v ≠ i ∧ x v ≠ j) := fun h => h.1 hvi
      rw [if_pos hvi, if_neg hvj, if_neg hnot, add_zero, add_zero]
      have hpt (p : Fin n × Fin n) : (Y v p + 1) ^ 2
          ≤ 4 * (if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0) := by
        by_cases hρ : rule (x v) (x p.1) (x p.2) = i
        · have hne : rule (x v) (x p.1) (x p.2) ≠ j := fun h => hij (h.symm.trans hρ)
          have hstay : ¬ (rule (x v) (x p.1) (x p.2) ≠ i) := fun h => h hρ
          have hY : Y v p = -1 := by
            simp only [Y, if_neg hne, if_pos hρ]
            norm_num
          rw [hY, if_neg hstay]
          norm_num
        · have hsq : (Y v p + 1) ^ 2 ≤ 4 := by nlinarith [hYge v p, hYle v p]
          rw [if_pos hρ, mul_one]
          exact hsq
      calc variance (Y v) ≤ avg (fun (p : Fin n × Fin n) => (Y v p - (-1)) ^ 2) :=
            variance_le_avg_sub (Y v) (-1)
        _ ≤ avg (fun (p : Fin n × Fin n) =>
            4 * (if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0)) := by
            refine avg_le_avg fun p => ?_
            rw [show Y v p - (-1) = Y v p + 1 by ring]
            exact hpt p
        _ = 4 * avg (fun (p : Fin n × Fin n) =>
            if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0) := by
            rw [avg_const_mul]
        _ ≤ 4 * (a / n) := mul_le_mul_of_nonneg_left (hleave_le i v hvi) (by norm_num)
        _ = 4 * a / n := by ring
    · by_cases hvj : x v = j
      · have hnot : ¬ (x v ≠ i ∧ x v ≠ j) := fun h => h.2 hvj
        rw [if_neg hvi, if_pos hvj, if_neg hnot, zero_add, add_zero]
        have hpt (p : Fin n × Fin n) : (Y v p - 1) ^ 2
            ≤ 4 * (if rule (x v) (x p.1) (x p.2) ≠ j then (1 : ℝ) else 0) := by
          by_cases hρ : rule (x v) (x p.1) (x p.2) = j
          · have hne : rule (x v) (x p.1) (x p.2) ≠ i := fun h => hij (hρ.symm.trans h)
            have hstay : ¬ (rule (x v) (x p.1) (x p.2) ≠ j) := fun h => h hρ
            have hY : Y v p = 1 := by
              simp only [Y, if_pos hρ, if_neg hne]
              norm_num
            rw [hY, if_neg hstay]
            norm_num
          · have hsq : (Y v p - 1) ^ 2 ≤ 4 := by nlinarith [hYge v p, hYle v p]
            rw [if_pos hρ, mul_one]
            exact hsq
        calc variance (Y v) ≤ avg (fun (p : Fin n × Fin n) => (Y v p - 1) ^ 2) :=
              variance_le_avg_sub (Y v) 1
          _ ≤ 4 * avg (fun (p : Fin n × Fin n) =>
              if rule (x v) (x p.1) (x p.2) ≠ j then (1 : ℝ) else 0) := by
              rw [← avg_const_mul]
              exact avg_le_avg hpt
          _ ≤ 4 * (a / n) := mul_le_mul_of_nonneg_left (hleave_le j v hvj) (by norm_num)
          _ = 4 * a / n := by ring
      · have hother : x v ≠ i ∧ x v ≠ j := ⟨hvi, hvj⟩
        rw [if_neg hvi, if_neg hvj, if_pos hother, zero_add, zero_add]
        have hsq (p : Fin n × Fin n) : Y v p ^ 2
            = (if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
              + (if rule (x v) (x p.1) (x p.2) = j then 1 else 0) := by
          by_cases hρi : rule (x v) (x p.1) (x p.2) = i
          · have hρj : rule (x v) (x p.1) (x p.2) ≠ j := fun h => hij (h.symm.trans hρi)
            simp only [Y, if_pos hρi, if_neg hρj]
            norm_num
          · by_cases hρj : rule (x v) (x p.1) (x p.2) = j
            · simp only [Y, if_neg hρi, if_pos hρj]
              norm_num
            · simp only [Y, if_neg hρi, if_neg hρj]
              norm_num
        have havg_i : avg (fun (p : Fin n × Fin n) =>
            if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
            = ((count x i : ℝ) / n) ^ 2 := by
          have hrule := avg_rule x i v
          rwa [if_neg hvi, zero_mul, add_zero] at hrule
        have havg_j : avg (fun (p : Fin n × Fin n) =>
            if rule (x v) (x p.1) (x p.2) = j then (1 : ℝ) else 0)
            = ((count x j : ℝ) / n) ^ 2 := by
          have hrule := avg_rule x j v
          rwa [if_neg hvj, zero_mul, add_zero] at hrule
        have hqi : ((count x i : ℝ) / n) ^ 2 ≤ a ^ 2 / n ^ 2 :=
          le_of_eq (by rw [ha_def, div_pow])
        have hqj : ((count x j : ℝ) / n) ^ 2 ≤ a ^ 2 / n ^ 2 := by
          rw [div_pow]
          gcongr
          exact hbound j
        calc variance (Y v) ≤ avg (fun (p : Fin n × Fin n) => Y v p ^ 2) :=
              variance_le_avg_sq (Y v)
          _ = avg (fun (p : Fin n × Fin n) =>
                if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
              + avg (fun (p : Fin n × Fin n) =>
                if rule (x v) (x p.1) (x p.2) = j then 1 else 0) := by
              rw [← avg_add]
              exact congrArg avg (funext hsq)
          _ ≤ a ^ 2 / n ^ 2 + a ^ 2 / n ^ 2 := by linarith
          _ = 2 * a ^ 2 / n ^ 2 := by ring
  have hσ : ∑ v, variance (Y v) ≤ 10 * a ^ 2 / n := by
    calc ∑ v, variance (Y v) ≤ ∑ v, ((if x v = i then 4 * a / n else 0)
          + (if x v = j then 4 * a / n else 0)
          + (if x v ≠ i ∧ x v ≠ j then 2 * a ^ 2 / n ^ 2 else 0)) :=
          sum_le_sum fun v _ => hvar v
      _ = ∑ v, (if x v = i then 4 * a / n else 0)
          + ∑ v, (if x v = j then 4 * a / n else 0)
          + ∑ v, (if x v ≠ i ∧ x v ≠ j then 2 * a ^ 2 / n ^ 2 else 0) := by
          simp_rw [sum_add_distrib]
      _ ≤ 4 * a ^ 2 / n + 4 * a ^ 2 / n + 2 * a ^ 2 / n := by
          have hi : ∑ v, (if x v = i then 4 * a / n else 0) = 4 * a / n * a := by
            have hf : (fun v : Fin n => if x v = i then 4 * a / n else 0)
                = fun v => (4 * a / n) * (if x v = i then (1 : ℝ) else 0) := by
              funext v; split_ifs <;> ring
            rw [hf, ← mul_sum, ← count_eq_sum]
          have hj : ∑ v, (if x v = j then 4 * a / n else 0) = 4 * a / n * count x j := by
            have hf : (fun v : Fin n => if x v = j then 4 * a / n else 0)
                = fun v => (4 * a / n) * (if x v = j then (1 : ℝ) else 0) := by
              funext v; split_ifs <;> ring
            rw [hf, ← mul_sum, ← count_eq_sum]
          have hother : ∑ v, (if x v ≠ i ∧ x v ≠ j then 2 * a ^ 2 / n ^ 2 else 0)
              ≤ n * (2 * a ^ 2 / n ^ 2) := by
            calc _ ≤ ∑ _v : Fin n, 2 * a ^ 2 / n ^ 2 := by
                  refine sum_le_sum fun v _ => ?_
                  by_cases hv : x v ≠ i ∧ x v ≠ j
                  · exact le_of_eq (if_pos hv)
                  · rw [if_neg hv]; positivity
              _ = n * (2 * a ^ 2 / n ^ 2) := by
                  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hcj : (count x j : ℝ) ≤ a := hbound j
          have hcoef : 0 ≤ 4 * a / n := by positivity
          have hrest : n * (2 * a ^ 2 / n ^ 2) = 2 * a ^ 2 / n := by field_simp
          have heqa : 4 * a / n * a = 4 * a ^ 2 / n := by ring
          rw [hi, hj]
          have hjle : 4 * a / n * count x j ≤ 4 * a ^ 2 / n := by
            calc 4 * a / n * count x j ≤ 4 * a / n * a :=
                  mul_le_mul_of_nonneg_left hcj hcoef
              _ = 4 * a ^ 2 / n := by ring
          linarith [hjle, hother, hrest, heqa]
      _ = 10 * a ^ 2 / n := by ring
  have hσ0 : (0 : ℝ) < 10 * a ^ 2 / n := by positivity
  have hsumY (r : Round n) : ∑ v, Y v (r v)
      = (count (step x r) j : ℝ) - count (step x r) i := by
    simp_rw [count_eq_sum (step x r), ← sum_sub_distrib]
    refine sum_congr rfl fun v _ => ?_
    rfl
  have hEY : ∑ v, avg (Y v)
      = avg (fun r : Round n => (count (step x r) j : ℝ))
        - avg (fun r : Round n => (count (step x r) i : ℝ)) := by
    simp_rw [show ∀ v, avg (Y v) = avg (fun r : Round n => Y v (r v)) from
      fun v => (Dynamics.avg_eval n v (Y v)).symm]
    rw [← avg_sum, ← avg_sub]
    simp_rw [← hsumY]
  have hden : 2 * (10 * a ^ 2 / n) * (1 + 2 * lam / (3 * (10 * a ^ 2 / n)))
      = 20 * a ^ 2 / n + 4 * lam / 3 := by
    field_simp
    ring
  have hB := avg_bernstein (b := 2) (σ2 := 10 * a ^ 2 / n) (lam := lam) Y
    (by norm_num) hYb hσ hσ0 hlam
  have hiff (r : Round n) :
      ((count (step x r) i : ℝ) - count (step x r) j
          ≤ avg (fun ρ => (count (step x ρ) i : ℝ) - count (step x ρ) j) - lam)
        ↔ (∑ v, avg (Y v)) + lam ≤ ∑ v, Y v (r v) := by
    rw [hsumY, hEY, avg_sub]
    constructor <;> intro h <;> linarith
  simp_rw [hiff]
  rw [← hden]
  exact hB

/-- Lower tail of a single count. If `a = c_i` bounds every colour and `a > 0`, then
`P(c_i' ≤ 𝔼c_i' - λ) ≤ exp(-λ² / (4 a²/n + 2λ/3))`. -/
lemma count_dev_le (x : Config n α) (i : α) (ha : ∀ l, count x l ≤ count x i)
    (hpos : 0 < count x i) {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun r : Round n =>
        if (count (step x r) i : ℝ)
            ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam then (1 : ℝ) else 0)
      ≤ exp (-(lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3))) := by
  haveI : Nonempty (Fin n × Fin n) := ⟨((0 : Fin n), (0 : Fin n))⟩
  haveI : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set a : ℝ := (count x i : ℝ) with ha_def
  have ha0 : 0 < a := by rw [ha_def]; exact_mod_cast hpos
  have hbound : ∀ l, (count x l : ℝ) ≤ a := fun l => by rw [ha_def]; exact_mod_cast ha l
  let Y : Fin n → Fin n × Fin n → ℝ := fun v p =>
    -(if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
  have hYge (v) (p) : -1 ≤ Y v p := by
    have : (if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    linarith
  have hYle (v) (p) : Y v p ≤ 0 := by
    have : (0 : ℝ) ≤ (if rule (x v) (x p.1) (x p.2) = i then 1 else 0) := by
      split_ifs <;> norm_num
    linarith
  have havg (v) : -1 ≤ avg (Y v) := by
    calc -1 = avg (fun _ : Fin n × Fin n => (-1 : ℝ)) := (avg_const _).symm
      _ ≤ avg (Y v) := avg_le_avg (hYge v)
  have hYb (v) (p) : Y v p - avg (Y v) ≤ 1 := by linarith [hYle v p, havg v]
  have hleave_le (v : Fin n) (hv : x v = i) :
      avg (fun (p : Fin n × Fin n) => if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0) ≤ a / n := by
    rw [avg_leave x i v hv, sum_sq_div]
    have hsq := sum_sq_erase_le x i hbound ha0.le
    have hdiv : (∑ l ∈ univ.erase i, (count x l : ℝ) ^ 2) / n ^ 2 ≤ a * n / n ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have heq : a * n / n ^ 2 = a / n := by field_simp
    linarith
  have hvar (v : Fin n) : variance (Y v) ≤ if x v = i then a / n else a ^ 2 / n ^ 2 := by
    by_cases hv : x v = i
    · rw [if_pos hv]
      have hpt (p : Fin n × Fin n) : (Y v p + 1) ^ 2
          = if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0 := by
        by_cases hρ : rule (x v) (x p.1) (x p.2) = i
        · have hstay : ¬ (rule (x v) (x p.1) (x p.2) ≠ i) := fun h => h hρ
          simp only [Y, if_pos hρ, if_neg hstay]
          norm_num
        · simp only [Y, if_neg hρ, if_pos hρ]
          norm_num
      calc variance (Y v) ≤ avg (fun (p : Fin n × Fin n) => (Y v p - (-1)) ^ 2) :=
            variance_le_avg_sub (Y v) (-1)
        _ = avg (fun (p : Fin n × Fin n) =>
            if rule (x v) (x p.1) (x p.2) ≠ i then (1 : ℝ) else 0) := by
            refine congrArg avg (funext fun p => ?_)
            rw [show Y v p - (-1) = Y v p + 1 by ring, hpt]
        _ ≤ a / n := hleave_le v hv
    · rw [if_neg hv]
      have hsq (p : Fin n × Fin n) : Y v p ^ 2
          = if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0 := by
        by_cases hρ : rule (x v) (x p.1) (x p.2) = i
        · simp only [Y, if_pos hρ]
          norm_num
        · simp only [Y, if_neg hρ]
          norm_num
      have havg_i := avg_rule x i v
      rw [if_neg hv, zero_mul, add_zero] at havg_i
      have hq : ((count x i : ℝ) / n) ^ 2 ≤ a ^ 2 / n ^ 2 :=
        le_of_eq (by rw [ha_def, div_pow])
      calc variance (Y v) ≤ avg (fun (p : Fin n × Fin n) => Y v p ^ 2) := variance_le_avg_sq (Y v)
        _ = ((count x i : ℝ) / n) ^ 2 := by
            rw [congrArg avg (funext hsq), havg_i]
        _ ≤ a ^ 2 / n ^ 2 := hq
  have hσ : ∑ v, variance (Y v) ≤ 2 * a ^ 2 / n := by
    calc ∑ v, variance (Y v) ≤ ∑ v, (if x v = i then a / n else a ^ 2 / n ^ 2) :=
          sum_le_sum fun v _ => hvar v
      _ = ∑ v, ((if x v = i then a / n else 0) + (if x v ≠ i then a ^ 2 / n ^ 2 else 0)) := by
          refine sum_congr rfl fun v _ => ?_
          by_cases hv : x v = i <;> simp [hv]
      _ = (a / n) * a + (a ^ 2 / n ^ 2) * (n - a) := by
          rw [sum_add_distrib]
          have hi : ∑ v, (if x v = i then a / n else 0) = a / n * a := by
            have hf : (fun v : Fin n => if x v = i then a / n else 0)
                = fun v => (a / n) * (if x v = i then (1 : ℝ) else 0) := by
              funext v; split_ifs <;> ring
            rw [hf, ← mul_sum, ← count_eq_sum]
          have hcompl : ∑ v, (if x v ≠ i then (1 : ℝ) else 0) = n - a := by
            have hone (v : Fin n) : (if x v = i then (1 : ℝ) else 0)
                + (if x v ≠ i then 1 else 0) = 1 := by
              by_cases hv : x v = i <;> simp [hv]
            have hsum : ∑ v, (if x v = i then (1 : ℝ) else 0)
                + ∑ v, (if x v ≠ i then (1 : ℝ) else 0) = n := by
              rw [← sum_add_distrib, sum_congr rfl fun v _ => hone v, sum_const, card_univ,
                Fintype.card_fin, nsmul_eq_mul, mul_one]
            rw [← count_eq_sum] at hsum
            linarith
          have ho : ∑ v, (if x v ≠ i then a ^ 2 / n ^ 2 else 0)
              = a ^ 2 / n ^ 2 * (n - a) := by
            have hf : (fun v : Fin n => if x v ≠ i then a ^ 2 / n ^ 2 else 0)
                = fun v => (a ^ 2 / n ^ 2) * (if x v ≠ i then (1 : ℝ) else 0) := by
              funext v; split_ifs <;> ring
            rw [hf, ← mul_sum, hcompl]
          rw [hi, ho]
      _ ≤ a ^ 2 / n + a ^ 2 / n := by
          have hna : n - a ≤ n := by linarith [ha0.le]
          have hcoef : 0 ≤ a ^ 2 / n ^ 2 := by positivity
          have hsec : (a ^ 2 / n ^ 2) * (n - a) ≤ (a ^ 2 / n ^ 2) * n :=
            mul_le_mul_of_nonneg_left hna hcoef
          have heq : (a ^ 2 / n ^ 2) * n = a ^ 2 / n := by field_simp
          have heq1 : a / n * a = a ^ 2 / n := by ring
          linarith
      _ = 2 * a ^ 2 / n := by ring
  have hσ0 : (0 : ℝ) < 2 * a ^ 2 / n := by positivity
  have hsumY (r : Round n) : ∑ v, Y v (r v) = -((count (step x r) i : ℝ)) := by
    simp_rw [count_eq_sum (step x r)]
    rw [← sum_neg_distrib]
    rfl
  have hEY : ∑ v, avg (Y v) = -avg (fun r : Round n => (count (step x r) i : ℝ)) := by
    simp_rw [show ∀ v, avg (Y v) = avg (fun r : Round n => Y v (r v)) from
      fun v => (Dynamics.avg_eval n v (Y v)).symm]
    rw [← avg_sum]
    have hneg : avg (fun r : Round n => -((count (step x r) i : ℝ)))
        = -avg (fun r : Round n => (count (step x r) i : ℝ)) := by
      unfold avg
      rw [sum_neg_distrib, neg_div]
    simp_rw [hsumY]
    exact hneg
  have hden : 2 * (2 * a ^ 2 / n) * (1 + 1 * lam / (3 * (2 * a ^ 2 / n)))
      = 4 * a ^ 2 / n + 2 * lam / 3 := by
    field_simp
    ring
  have hB := avg_bernstein (b := 1) (σ2 := 2 * a ^ 2 / n) (lam := lam) Y
    (by norm_num) hYb hσ hσ0 hlam
  have hiff (r : Round n) :
      ((count (step x r) i : ℝ) ≤ avg (fun ρ => (count (step x ρ) i : ℝ)) - lam)
        ↔ (∑ v, avg (Y v)) + lam ≤ ∑ v, Y v (r v) := by
    rw [hsumY, hEY]
    constructor <;> intro h <;> linarith
  simp_rw [hiff]
  rw [← hden]
  exact hB

/-- With `λ = g a / (8 n)` and `g ≥ 128 √(n L)`, the gap exponent is at least `12 L`. -/
lemma gap_exponent_ge {n a g L : ℝ} (hn : 0 < n) (ha : 0 < a) (hg : 0 ≤ g) (hga : g ≤ a)
    (hL : 0 ≤ L) (hgsq : (128 : ℝ) ^ 2 * n * L ≤ g ^ 2) :
    12 * L ≤ (g * a / (8 * n)) ^ 2 / (20 * a ^ 2 / n + 4 * (g * a / (8 * n)) / 3) := by
  have hden : 0 < 20 * a ^ 2 / n + 4 * (g * a / (8 * n)) / 3 := by positivity
  rw [le_div_iff₀ hden]
  have h4 : 4 * (g * a / (8 * n)) / 3 ≤ a ^ 2 / n := by
    have e : 4 * (g * a / (8 * n)) / 3 = g * a / (6 * n) := by field_simp; ring
    rw [e]
    have h1 : g * a / (6 * n) ≤ a * a / (6 * n) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hga ha.le
    have h2 : a * a / (6 * n) ≤ a ^ 2 / n := by
      have : a * a = a ^ 2 := by ring
      rw [this]
      apply div_le_div_of_nonneg_left (sq_nonneg a) hn
      linarith
    linarith
  have hdenle : 20 * a ^ 2 / n + 4 * (g * a / (8 * n)) / 3 ≤ 21 * a ^ 2 / n := by
    have h := add_le_add (le_refl (20 * a ^ 2 / n)) h4
    have heq : 20 * a ^ 2 / n + a ^ 2 / n = 21 * a ^ 2 / n := by ring
    exact h.trans_eq heq
  have hstep : 12 * L * (20 * a ^ 2 / n + 4 * (g * a / (8 * n)) / 3)
      ≤ 12 * L * (21 * a ^ 2 / n) := mul_le_mul_of_nonneg_left hdenle (by linarith)
  refine hstep.trans ?_
  have hlam : (g * a / (8 * n)) ^ 2 = g ^ 2 * a ^ 2 / (64 * n ^ 2) := by field_simp; ring
  rw [hlam]
  have e2 : 12 * L * (21 * a ^ 2 / n) = 252 * L * a ^ 2 / n := by ring
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hnum : (252 : ℝ) * 64 ≤ 128 ^ 2 := by norm_num
  have hclear : 252 * L * a ^ 2 * (64 * n ^ 2) ≤ g ^ 2 * a ^ 2 * n := by
    have hmain : 252 * 64 * n * L * a ^ 2 ≤ g ^ 2 * a ^ 2 := by
      have hcoef : 252 * 64 * (n * L) ≤ 128 ^ 2 * (n * L) := by nlinarith [hnum, mul_nonneg hn.le hL]
      have hsq : 128 ^ 2 * (n * L) * a ^ 2 ≤ g ^ 2 * a ^ 2 := by
        have := mul_le_mul_of_nonneg_right hgsq (sq_nonneg a)
        linarith
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 252 * 64) (mul_nonneg hn.le hL))
        (sq_nonneg a)]
    nlinarith
  linarith

/-- With `λ = a g / (4 n)` and `g ≥ 128 √(n L)`, the count exponent is at least `12 L`. -/
lemma count_exponent_ge {n a g L : ℝ} (hn : 0 < n) (ha : 0 < a) (hg : 0 ≤ g) (hga : g ≤ a)
    (hL : 0 ≤ L) (hgsq : (128 : ℝ) ^ 2 * n * L ≤ g ^ 2) :
    12 * L ≤ (a * g / (4 * n)) ^ 2 / (4 * a ^ 2 / n + 2 * (a * g / (4 * n)) / 3) := by
  have hden : 0 < 4 * a ^ 2 / n + 2 * (a * g / (4 * n)) / 3 := by positivity
  rw [le_div_iff₀ hden]
  have h2 : 2 * (a * g / (4 * n)) / 3 ≤ a ^ 2 / n := by
    have e : 2 * (a * g / (4 * n)) / 3 = a * g / (6 * n) := by field_simp; ring
    rw [e]
    have h1 : a * g / (6 * n) ≤ a * a / (6 * n) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hga ha.le
    have h2' : a * a / (6 * n) ≤ a ^ 2 / n := by
      have : a * a = a ^ 2 := by ring
      rw [this]
      apply div_le_div_of_nonneg_left (sq_nonneg a) hn
      linarith
    linarith
  have hdenle : 4 * a ^ 2 / n + 2 * (a * g / (4 * n)) / 3 ≤ 5 * a ^ 2 / n := by
    have h := add_le_add (le_refl (4 * a ^ 2 / n)) h2
    have heq : 4 * a ^ 2 / n + a ^ 2 / n = 5 * a ^ 2 / n := by ring
    exact h.trans_eq heq
  have hstep : 12 * L * (4 * a ^ 2 / n + 2 * (a * g / (4 * n)) / 3)
      ≤ 12 * L * (5 * a ^ 2 / n) := mul_le_mul_of_nonneg_left hdenle (by linarith)
  refine hstep.trans ?_
  have hlam : (a * g / (4 * n)) ^ 2 = a ^ 2 * g ^ 2 / (16 * n ^ 2) := by field_simp; ring
  rw [hlam]
  have e2 : 12 * L * (5 * a ^ 2 / n) = 60 * L * a ^ 2 / n := by ring
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hnum : (60 : ℝ) * 16 ≤ 128 ^ 2 := by norm_num
  have hmain : 60 * 16 * n * L * a ^ 2 ≤ g ^ 2 * a ^ 2 := by
    have hcoef : 60 * 16 * (n * L) ≤ 128 ^ 2 * (n * L) := by nlinarith [hnum, mul_nonneg hn.le hL]
    have := mul_le_mul_of_nonneg_right hgsq (sq_nonneg a)
    nlinarith
  nlinarith

/-- `exp(-(12 log n)) = 1/n¹²`. -/
lemma exp_neg_twelve_log {n : ℕ} (hn : 1 ≤ n) :
    exp (-(12 * log n)) = 1 / (n : ℝ) ^ 12 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [exp_neg, show (12 : ℝ) * log n = (12 : ℕ) • log n by simp [nsmul_eq_mul], exp_nsmul,
    exp_log hn0, inv_eq_one_div]

/-- `1/n¹² ≤ 1/n²` for `n ≥ 1`. -/
lemma one_div_pow_twelve_le {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) ^ 12 ≤ 1 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 12 :=
    pow_le_pow_right₀ (by exact_mod_cast hn) (by norm_num : (2 : ℕ) ≤ 12)
  exact div_le_div_of_nonneg_left zero_le_one (pow_pos hn0 2) hpow

/-- For `a ≤ n/2` the gap drift `1 + (a/n)(1 − a/n)` stays strictly above `1 + a/(4n)` after the
deviation `λ = g a/(8n)` is removed. -/
lemma distance_margin {n a g : ℝ} (hn : 0 < n) (ha : 0 < a) (hg : 0 < g) (han : a ≤ n / 2) :
    g * (1 + a / (4 * n))
      < g * (1 + (a / n) * (1 - a / n)) - g * a / (8 * n) := by
  have hhalf : a / n ≤ (1 : ℝ) / 2 := by
    rw [div_le_div_iff₀ hn (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hpos_an : 0 < a / n := div_pos ha hn
  have hsq : (a / n) ^ 2 ≤ (a / n) * (1 / 2) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left hhalf hpos_an.le
  have htwo : a / (2 * n) = (a / n) * (1 / 2) := by field_simp
  have hlow : a / (2 * n) ≤ (a / n) * (1 - a / n) := by
    have hre : (a / n) * (1 - a / n) = a / n - (a / n) ^ 2 := by ring
    have hsum : a / (2 * n) + (a / n) ^ 2 ≤ a / n := by
      calc a / (2 * n) + (a / n) ^ 2 = (a / n) * (1 / 2) + (a / n) ^ 2 := by rw [htwo]
        _ ≤ (a / n) * (1 / 2) + (a / n) * (1 / 2) := by linarith [hsq]
        _ = a / n := by ring
    linarith [hre]
  have heq : a / (4 * n) + a / (8 * n) = 3 * a / (8 * n) := by field_simp; ring
  have hstrict : a / (4 * n) + a / (8 * n) < a / (2 * n) := by
    rw [heq, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [ha, hn]
  have hstep : a / (4 * n) + a / (8 * n) < (a / n) * (1 - a / n) := lt_of_lt_of_le hstrict hlow
  have hmul : g * (a / (4 * n) + a / (8 * n)) < g * ((a / n) * (1 - a / n)) :=
    mul_lt_mul_of_pos_left hstep hg
  have hkey : g * (a / (4 * n)) + g * a / (8 * n) < g * ((a / n) * (1 - a / n)) := by
    calc g * (a / (4 * n)) + g * a / (8 * n)
        = g * (a / (4 * n) + a / (8 * n)) := by ring
      _ < g * ((a / n) * (1 - a / n)) := hmul
  linarith [hkey]

/-- For `a ≤ 3n/4` the same drift dominates the weaker factor `1 + a/(8n)`. -/
lemma three_quarter_margin {n a g : ℝ} (hn : 0 < n) (ha : 0 ≤ a) (hg : 0 ≤ g)
    (han : a ≤ 3 * n / 4) :
    g * (1 + a / (8 * n))
      ≤ g * (1 + (a / n) * (1 - a / n)) - g * a / (8 * n) := by
  have hfrac : a / n ≤ 3 / 4 := by
    rw [div_le_div_iff₀ hn (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hone : (1 : ℝ) / 4 ≤ 1 - a / n := by linarith
  have hcoef : 0 ≤ a / n := div_nonneg ha hn.le
  have hmul : (a / n) * ((1 : ℝ) / 4) ≤ (a / n) * (1 - a / n) :=
    mul_le_mul_of_nonneg_left hone hcoef
  have heq : (a / n) * ((1 : ℝ) / 4) = a / (4 * n) := by field_simp
  have hfour : a / (4 * n) ≤ (a / n) * (1 - a / n) := by rwa [heq] at hmul
  have hsum : a / (8 * n) + a / (8 * n) = a / (4 * n) := by field_simp; ring
  have hdiff : a / (8 * n) ≤ (a / n) * (1 - a / n) - a / (8 * n) := by
    have hle : a / (8 * n) + a / (8 * n) ≤ (a / n) * (1 - a / n) := by rw [hsum]; exact hfour
    linarith
  have hmulg : g * (a / (8 * n)) ≤ g * ((a / n) * (1 - a / n) - a / (8 * n)) :=
    mul_le_mul_of_nonneg_left hdiff hg
  have hsplit : g * ((a / n) * (1 - a / n) - a / (8 * n))
      = g * ((a / n) * (1 - a / n)) - g * (a / (8 * n)) := by ring
  have hcomm : g * a / (8 * n) = g * (a / (8 * n)) := by ring
  linarith [hmulg, hsplit, hcomm]

/-- The gap lower tail is at most `1/n¹²` once the gap is at least `128 √(n log n)`. -/
lemma gap_tail_twelve (x : Config n α) (i j : α) (hij : j ≠ i)
    (ha : ∀ l, count x l ≤ count x i) (hpos : 0 < count x i)
    {g : ℝ} (hg0 : 0 ≤ g) (hga : g ≤ (count x i : ℝ)) (hL : 0 ≤ Real.log n) (hn1 : 1 ≤ n)
    (hgsq : (128 : ℝ) ^ 2 * (n : ℝ) * Real.log n ≤ g ^ 2) :
    avg (fun r : Round n =>
        if (count (step x r) i : ℝ) - count (step x r) j
            ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ) - count (step x ρ) j)
              - g * (count x i : ℝ) / (8 * n)
          then (1 : ℝ) else 0)
      ≤ 1 / (n : ℝ) ^ 12 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have ha0 : (0 : ℝ) < count x i := by exact_mod_cast hpos
  let lam : ℝ := g * (count x i : ℝ) / (8 * n)
  have hlam : 0 ≤ lam := div_nonneg (mul_nonneg hg0 (Nat.cast_nonneg _)) (by positivity)
  have hB := gap_dev_le x i j hij ha hpos hlam
  have hpow := gap_exponent_ge (n := (n : ℝ)) (a := (count x i : ℝ)) (g := g) (L := Real.log n)
    hn ha0 hg0 hga hL hgsq
  have hexp : exp (-(lam ^ 2 / (20 * (count x i : ℝ) ^ 2 / n + 4 * lam / 3)))
      ≤ exp (-(12 * Real.log n)) := exp_le_exp.mpr (neg_le_neg hpow)
  exact hB.trans (hexp.trans (le_of_eq (exp_neg_twelve_log hn1)))

/-- The count lower tail is at most `1/n¹²` for the deviation `λ = a g/(4n)`. -/
lemma count_tail_twelve (x : Config n α) (i : α) (ha : ∀ l, count x l ≤ count x i)
    (hpos : 0 < count x i) {g : ℝ} (hg0 : 0 ≤ g) (hga : g ≤ (count x i : ℝ))
    (hL : 0 ≤ Real.log n) (hn1 : 1 ≤ n)
    (hgsq : (128 : ℝ) ^ 2 * (n : ℝ) * Real.log n ≤ g ^ 2) :
    avg (fun r : Round n =>
        if (count (step x r) i : ℝ)
            ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ))
              - (count x i : ℝ) * g / (4 * n)
          then (1 : ℝ) else 0)
      ≤ 1 / (n : ℝ) ^ 12 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have ha0 : (0 : ℝ) < count x i := by exact_mod_cast hpos
  let lam : ℝ := (count x i : ℝ) * g / (4 * n)
  have hlam : 0 ≤ lam := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hg0) (by positivity)
  have hB := count_dev_le x i ha hpos hlam
  have hpow := count_exponent_ge (n := (n : ℝ)) (a := (count x i : ℝ)) (g := g) (L := Real.log n)
    hn ha0 hg0 hga hL hgsq
  have hexp : exp (-(lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3)))
      ≤ exp (-(12 * Real.log n)) := exp_le_exp.mpr (neg_le_neg hpow)
  exact hB.trans (hexp.trans (le_of_eq (exp_neg_twelve_log hn1)))

end Median.TwoChoices
