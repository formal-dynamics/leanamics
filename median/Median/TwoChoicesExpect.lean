import Median.TwoChoicesDefs

/-! # The k-party 2-Choices dynamics: one-round expectations

Elsässer, Friedetzky, Kaaser, Mallmann-Trenn and Trinker, *Efficient k-party voting with two
choices* (arXiv:1602.04667v5), Section 2.1. Write `c_j` for the number of nodes of colour `j`
and `S = ∑_j c_j²`. A node of colour `i` leaves `i` if and only if its two samples hold the same
other colour (probability `∑_{j ≠ i} c_j²/n²`), and a node of another colour joins `i` if and only
if both samples hold `i` (probability `c_i²/n²`). Hence (the paper's equation (1))
`𝔼[c_i'] = c_i + (n − c_i) c_i²/n² − (c_i/n²) ∑_{j ≠ i} c_j² = c_i (1 + c_i/n − S/n²)`,
which is monotone in `c_i` (Observation 1), and the gap between two colours evolves as
`𝔼[c_i' − c_j'] = (c_i − c_j)(1 + (c_i + c_j)/n − S/n²)` (proof of Lemma 1).

The aggregation of the minority colours (proof of Lemma 1): if `b` bounds every colour other
than `i`, then `S ≤ c_i² + (n − c_i) b`; and `S ≤ a n` if `a` bounds every colour. With these,
`𝔼[a' − b'] ≥ (a − b)(1 + (a/n)(1 − a/n))` for the largest colour `a` and the second largest
`b`.
-/

namespace Median.TwoChoices
open Finset Dynamics

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-! ### Indicators and pair probabilities -/

/-- A count as a real sum of indicators. -/
lemma count_eq_sum (x : Config n α) (i : α) :
    (count x i : ℝ) = ∑ v : Fin n, if x v = i then (1 : ℝ) else 0 := by
  rw [sum_boole]
  rfl

/-- The fraction of nodes of colour `j` is the probability that one uniform sample holds `j`. -/
lemma avg_sample (x : Config n α) (j : α) :
    avg (fun w : Fin n => if x w = j then (1 : ℝ) else 0) = (count x j : ℝ) / n := by
  rw [avg_indicator, Fintype.card_fin]
  rfl

/-- **Two samples of the same colour**: both samples of a node hold `j` with probability
`(c_j/n)²`. -/
theorem avg_pair (x : Config n α) (j : α) :
    avg (fun p : Fin n × Fin n => if x p.1 = j ∧ x p.2 = j then (1 : ℝ) else 0)
      = ((count x j : ℝ) / n) ^ 2 := by
  have h : (fun p : Fin n × Fin n => if x p.1 = j ∧ x p.2 = j then (1 : ℝ) else 0)
      = fun p : Fin n × Fin n =>
          (fun w : Fin n => if x w = j then (1 : ℝ) else 0) p.1
            * (fun w : Fin n => if x w = j then (1 : ℝ) else 0) p.2 := by
    funext p
    by_cases h1 : x p.1 = j <;> by_cases h2 : x p.2 = j <;> simp [h1, h2]
  rw [h, avg_mul_prod (fun w : Fin n => if x w = j then (1 : ℝ) else 0)
    (fun w : Fin n => if x w = j then (1 : ℝ) else 0), avg_sample, sq]

variable [Fintype α]

/-- The indicator of the 2-Choices rule landing on `i`, as a polynomial in the indicators of the
samples: `[rule own a b = i] = [a = i][b = i] + [own = i](1 − ∑_j [a = j][b = j])`. -/
lemma rule_ind (own a b i : α) :
    (if rule own a b = i then (1 : ℝ) else 0)
      = (if a = i ∧ b = i then 1 else 0)
        + (if own = i then 1 else 0) * (1 - ∑ j : α, if a = j ∧ b = j then 1 else 0) := by
  have hsum : (∑ j : α, if a = j ∧ b = j then (1 : ℝ) else 0) = if a = b then 1 else 0 := by
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg hab]
      refine sum_eq_zero fun j _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hab (h1.trans h2.symm)
  rw [hsum]
  unfold rule
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = i <;> simp [ha]
  · simp only [if_neg hab]
    have : ¬ (a = i ∧ b = i) := fun h => hab (h.1.trans h.2.symm)
    simp [this]

/-- The probability that a fixed node ends with colour `i` after one round:
`(c_i/n)² + [x v = i] (1 − ∑_j (c_j/n)²)`. -/
theorem avg_step_node [NeZero n] (x : Config n α) (i : α) (v : Fin n) :
    avg (fun r : Round n => if step x r v = i then (1 : ℝ) else 0)
      = ((count x i : ℝ) / n) ^ 2
        + (if x v = i then 1 else 0) * (1 - ∑ j : α, ((count x j : ℝ) / n) ^ 2) := by
  have h := Dynamics.avg_eval n v
    (fun p : Fin n × Fin n => if rule (x v) (x p.1) (x p.2) = i then (1 : ℝ) else 0)
  change avg (fun r : Round n => if rule (x v) (x (r v).1) (x (r v).2) = i then (1 : ℝ) else 0)
    = _
  rw [h]
  simp_rw [rule_ind]
  rw [avg_add, avg_const_mul, avg_pair]
  congr 2
  have hs : avg (fun p : Fin n × Fin n => 1 - ∑ j : α, if x p.1 = j ∧ x p.2 = j then (1 : ℝ) else 0)
      = 1 - ∑ j : α, avg (fun p : Fin n × Fin n =>
          if x p.1 = j ∧ x p.2 = j then (1 : ℝ) else 0) := by
    rw [avg_sub, avg_const, avg_sum]
  rw [hs]
  simp_rw [avg_pair]

/-- **Expected count, product form** (proof of Observation 1):
`𝔼[c_i'] = c_i (1 + c_i/n − S/n²)` with `S = ∑_j c_j²`. -/
theorem expected_count_mul [NeZero n] (x : Config n α) (i : α) :
    avg (fun r : Round n => (count (step x r) i : ℝ))
      = count x i * (1 + count x i / n - (∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp_rw [count_eq_sum (step _ _) i]
  rw [avg_sum]
  simp_rw [avg_step_node]
  rw [sum_add_distrib, ← sum_mul, ← count_eq_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hS : ∑ j : α, ((count x j : ℝ) / n) ^ 2 = (∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2 := by
    rw [sum_div]
    simp_rw [div_pow]
  rw [hS]
  field_simp
  ring

/-- **Equation (1)** of the paper: `𝔼[c_i'] = c_i + (n − c_i) c_i²/n² − (c_i/n²) ∑_{j ≠ i} c_j²`. -/
theorem expected_count [NeZero n] (x : Config n α) (i : α) :
    avg (fun r : Round n => (count (step x r) i : ℝ))
      = count x i + (n - count x i) * (count x i : ℝ) ^ 2 / n ^ 2
        - count x i / n ^ 2 * ∑ j ∈ univ.erase i, (count x j : ℝ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [expected_count_mul, ← add_sum_erase _ _ (mem_univ i)]
  field_simp
  ring

/-- **Expected gap** (proof of Lemma 1):
`𝔼[c_i' − c_j'] = (c_i − c_j)(1 + (c_i + c_j)/n − S/n²)`. -/
theorem expected_gap [NeZero n] (x : Config n α) (i j : α) :
    avg (fun r : Round n => (count (step x r) i : ℝ) - count (step x r) j)
      = ((count x i : ℝ) - count x j)
        * (1 + ((count x i : ℝ) + count x j) / n - (∑ l : α, (count x l : ℝ) ^ 2) / n ^ 2) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [avg_sub, expected_count_mul, expected_count_mul]
  field_simp
  ring

/-- The counts add up to `n`. -/
theorem sum_count (x : Config n α) : ∑ j : α, count x j = n := by
  unfold count
  rw [← card_eq_sum_card_fiberwise (f := x) (fun v _ => mem_univ (x v)), card_univ,
    Fintype.card_fin]

omit [Fintype α] in
/-- A count is at most `n`. -/
theorem count_le (x : Config n α) (i : α) : count x i ≤ n := by
  unfold count
  exact (card_filter_le _ _).trans (by rw [card_univ, Fintype.card_fin])

/-- `∑_j c_j² ≤ a n` when `a` bounds every count (proof of Lemma 1). -/
theorem sum_sq_le_max (x : Config n α) {a : ℝ} (ha : ∀ j, (count x j : ℝ) ≤ a) :
    ∑ j : α, (count x j : ℝ) ^ 2 ≤ a * n := by
  have h : ∑ j : α, (count x j : ℝ) = n := by exact_mod_cast sum_count x
  calc ∑ j : α, (count x j : ℝ) ^ 2 ≤ ∑ j : α, (count x j : ℝ) * a :=
        sum_le_sum fun j _ => by
          rw [sq]; exact mul_le_mul_of_nonneg_left (ha j) (Nat.cast_nonneg _)
    _ = a * n := by rw [← sum_mul, h, mul_comm]

/-- `S = ∑_j c_j² ≤ n²`. -/
theorem sum_sq_count_le (x : Config n α) : ∑ j : α, (count x j : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
  rw [sq (n : ℝ)]
  exact sum_sq_le_max x fun j => by exact_mod_cast count_le x j

/-- **Observation 1**: the expected next count is monotone in the current count:
`c_r ≤ c_s ⇒ 𝔼[c_r'] ≤ 𝔼[c_s']`. -/
theorem expected_count_mono [NeZero n] (x : Config n α) {r s : α}
    (h : count x r ≤ count x s) :
    avg (fun ρ : Round n => (count (step x ρ) r : ℝ))
      ≤ avg (fun ρ : Round n => (count (step x ρ) s : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [expected_count_mul, expected_count_mul]
  have hS := sum_sq_count_le x
  have hh : (count x r : ℝ) ≤ count x s := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ count x r := Nat.cast_nonneg _
  have hq : 0 ≤ 1 - (∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hS
  have e1 : (count x r : ℝ) * (1 + count x r / n - (∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2)
      = count x r * (1 - (∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2) + (count x r) ^ 2 / n := by
    ring
  have e2 : (count x s : ℝ) * (1 + count x s / n - (∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2)
      = count x s * (1 - (∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2) + (count x s) ^ 2 / n := by
    ring
  rw [e1, e2]
  have h1 := mul_le_mul_of_nonneg_right hh hq
  have h2 : (count x r : ℝ) ^ 2 / n ≤ (count x s) ^ 2 / n :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 hh 2) hn.le
  linarith

/-! ### Aggregating the minority colours -/

/-- **Aggregation of the minority colours** (proof of Lemma 1): if `b` bounds the count of every
colour other than `i`, then `∑_j c_j² ≤ c_i² + (n − c_i) b`. -/
theorem sum_sq_le_aggregate (x : Config n α) (i : α) {b : ℝ}
    (hb : ∀ j ≠ i, (count x j : ℝ) ≤ b) :
    ∑ j : α, (count x j : ℝ) ^ 2 ≤ (count x i : ℝ) ^ 2 + (n - count x i) * b := by
  rw [← add_sum_erase _ _ (mem_univ i)]
  have hrest : ∑ j ∈ univ.erase i, (count x j : ℝ) = n - count x i := by
    have h : ∑ j : α, (count x j : ℝ) = n := by exact_mod_cast sum_count x
    rw [← add_sum_erase _ _ (mem_univ i)] at h
    linarith
  have hle : ∑ j ∈ univ.erase i, (count x j : ℝ) ^ 2 ≤ ∑ j ∈ univ.erase i, (count x j : ℝ) * b := by
    refine sum_le_sum fun j hj => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (hb j (ne_of_mem_erase hj)) (Nat.cast_nonneg _)
  rw [← sum_mul, hrest] at hle
  linarith

/-- **Expected growth of the gap** (proof of Lemma 1): if `i` is the largest colour and `j` the
second largest, `𝔼[c_i' − c_j'] ≥ (c_i − c_j)(1 + (c_i/n)(1 − c_i/n))`. -/
theorem expected_gap_ge [NeZero n] (x : Config n α) {i j : α} (hji : count x j ≤ count x i)
    (hj : ∀ l ≠ i, count x l ≤ count x j) :
    ((count x i : ℝ) - count x j) * (1 + (count x i / n) * (1 - count x i / n))
      ≤ avg (fun r : Round n => (count (step x r) i : ℝ) - count (step x r) j) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [expected_gap]
  have hagg := sum_sq_le_aggregate x i (b := count x j) (fun l hl => by exact_mod_cast hj l hl)
  have hd : (0 : ℝ) ≤ (count x i : ℝ) - count x j := by
    have : (count x j : ℝ) ≤ count x i := by exact_mod_cast hji
    linarith
  apply mul_le_mul_of_nonneg_left _ hd
  have hj0 : (0 : ℝ) ≤ count x j := Nat.cast_nonneg _
  have key : (∑ l : α, (count x l : ℝ) ^ 2) / n ^ 2
      ≤ ((count x i : ℝ) ^ 2 + (n - count x i) * count x j) / n ^ 2 :=
    div_le_div_of_nonneg_right hagg (by positivity)
  have e : 1 + ((count x i : ℝ) + count x j) / n
        - ((count x i : ℝ) ^ 2 + (n - count x i) * count x j) / n ^ 2
      = 1 + (count x i / n) * (1 - count x i / n) + count x i * count x j / n ^ 2 := by
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ count x i * count x j / n ^ 2 := by positivity
  linarith

end Median.TwoChoices
