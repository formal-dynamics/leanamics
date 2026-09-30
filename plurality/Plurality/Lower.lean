import Plurality.Growth
import Dynamics.Rounds

/-!
# The lower bound for 3-majority (Section 4.1)

From a balanced coloring, where every color has at most `n/k + b` nodes, no
color can gain much in one round: its count exceeds `n/k + (1 + 3/k) b` with
probability at most `1/n²` (**Lemma 4.1**, `lemma_4_1`). The expectation
bound uses `∑ₕ cₕ² ≥ n²/k` (Cauchy–Schwarz), and the deviation bound is
Hoeffding's inequality.

**Theorem 4.2** (`theorem_4_2`): following the schedule
`b_t = (1 + 3/k)^t b`, a union bound over rounds (`Dynamics.expList_escape`)
and colors shows that as long as `b (1 + 3/k)^T ≤ n/k`, no color has more than
`2n/k` nodes after `T` rounds except with probability `k T / n²`; in
particular the coloring is not monochromatic when `k ≥ 3`.
`theorem_4_2_log` turns the condition into `T ≤ (k/3) log (n / (k b))`.

## Range of `k`

Lemma 4.1 needs `b ≥ k √(n log n)`, so the schedule starts at
`b ≥ max ((n/k)^{1-ε}, k √(n log n))`, and the number of rounds obtained is
`(k/3) log (n / (k b))`. This is `Ω(k log n)` when `k ≤ n^{1/4 - δ}`, but it
degenerates as `k` approaches `(n / log n)^{1/4}`, where `n/k = k √(n log n)`.
The paper states the theorem for all `k ≤ (n / log n)^{1/4}`; see
`FORMALIZATION_DIFFERENCES.md`.
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

variable {n k : ℕ}

/-- `∑ₕ cₕ² ≥ n²/k`, by Cauchy–Schwarz. -/
lemma sq_div_le_sum_sq (hk : 1 ≤ k) (x : Config n k) :
    (n : ℝ) ^ 2 / k ≤ ∑ h, (count x h : ℝ) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin k)))
    (f := fun h => (count x h : ℝ))
  rw [sum_count_real, card_univ, Fintype.card_fin] at h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hk0]
  linarith

/-- The expected count of a color with at most `n/k + b` nodes is at most
`n/k + (1 + 2/k) b`, for `0 ≤ b ≤ n/k`. -/
lemma mu_le_of_count_le (hn : 1 ≤ n) (hk : 1 ≤ k) (x : Config n k) (j : Fin k) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ n / k) (hx : (count x j : ℝ) ≤ n / k + b) :
    mu n (count x) j ≤ n / k + (1 + 2 / k) * b := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := (count x j : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hsq := sq_div_le_sum_sq hk x
  -- `μ ≤ c (1 + c/n - 1/k)`
  have h1 : mu n (count x) j ≤ c * (1 + c / n - 1 / k) := by
    unfold mu
    rw [← hc]
    apply mul_le_mul_of_nonneg_left _ hc0
    have : ((n : ℝ) * c - ∑ h, (count x h : ℝ) ^ 2) / (n : ℝ) ^ 2
        ≤ ((n : ℝ) * c - (n : ℝ) ^ 2 / k) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have e : ((n : ℝ) * c - (n : ℝ) ^ 2 / k) / (n : ℝ) ^ 2 = c / n - 1 / k := by
      field_simp
    linarith
  -- write `c = n/k + a` with `a ≤ b`
  set a : ℝ := c - n / k with ha
  have hab : a ≤ b := by rw [ha]; linarith
  have ha0 : -((n : ℝ) / k) ≤ a := by rw [ha]; linarith
  have e : c * (1 + c / n - 1 / k) = n / k + a + a / k + a ^ 2 / n := by
    rw [show c = n / k + a by rw [ha]; ring]
    field_simp
    ring
  have hmono : n / k + a + a / k + a ^ 2 / n ≤ n / k + b + b / k + b ^ 2 / n := by
    have hdiff : (n / k + b + b / k + b ^ 2 / n) - (n / k + a + a / k + a ^ 2 / n)
        = (b - a) * (1 + 1 / k + (a + b) / n) := by
      field_simp
      ring
    have hpos : 0 ≤ 1 + 1 / k + (a + b) / n := by
      have : -(1 / (k : ℝ)) ≤ (a + b) / n := by
        rw [le_div_iff₀ hn0]
        have : -(1 / (k : ℝ)) * n = -((n : ℝ) / k) := by ring
        linarith
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hpos]
  have hb2 : b ^ 2 / n ≤ b / k := by
    rw [div_le_div_iff₀ hn0 hk0]
    have : b * k ≤ n := by rwa [le_div_iff₀ hk0] at hb1
    nlinarith
  have e2 : (n : ℝ) / k + (1 + 2 / k) * b = n / k + b + b / k + b / k := by ring
  linarith

/-- **Lemma 4.1.** If color `j` has at most `n/k + b` nodes, where
`k √(n log n) ≤ b ≤ n/k`, then after one round it has at least
`n/k + (1 + 3/k) b` nodes with probability at most `1/n²`. -/
theorem lemma_4_1 (hn : 1 ≤ n) (hk : 1 ≤ k) (x : Config n k) (j : Fin k) {b : ℝ}
    (hb0 : k * √(n * Real.log n) ≤ b) (hb1 : b ≤ n / k) (hx : (count x j : ℝ) ≤ n / k + b) :
    avg (fun r : Tgt3 n =>
        if (n : ℝ) / k + (1 + 3 / k) * b ≤ count (step x r) j then (1 : ℝ) else 0)
      ≤ 1 / (n : ℝ) ^ 2 := by
  haveI : Nonempty (Fin n × Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hb : 0 ≤ b := le_trans (by positivity) hb0
  have hμ := mu_le_of_count_le hn hk x j hb hb1 hx
  have hsum : ∑ _v : Fin n, avg (adopt maj3 x j) = mu n (count x) j := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, n_mul_avg_adopt hn]
  have hH := avg_hoeffding (fun (_ : Fin n) t => adopt maj3 x j t)
    (fun _ t => adopt_zero_one maj3 x j t) (lam := b / k) (by positivity)
  rw [hsum] at hH
  refine le_trans ?_ (hH.trans ?_)
  · refine avg_le_avg fun r => ?_
    have hc : (count (step x r) j : ℝ) = ∑ v, adopt maj3 x j (r v) :=
      count_stepWith_eq_sum maj3 x r j
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      apply h2
      rw [← hc]
      have : (n : ℝ) / k + (1 + 3 / k) * b = n / k + (1 + 2 / k) * b + b / k := by ring
      linarith
    · norm_num
    · exact le_rfl
  · -- `(b/k)² ≥ n log n`
    have hs : √(n * Real.log n) ≤ b / k := by rw [le_div_iff₀ hk0]; linarith
    have hsq : (n : ℝ) * Real.log n ≤ (b / k) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
      rwa [Real.sq_sqrt (by positivity)] at this
    rw [← exp_neg_two_log hn]
    apply exp_le_exp.mpr
    rw [neg_le_neg_iff, le_div_iff₀ hn0]
    nlinarith

/-- The threshold of round `t`: `n/k + b (1 + 3/k)^t`. -/
def balancedSet (n : ℕ) {k : ℕ} (j : Fin k) (b : ℝ) (t : ℕ) : Set (Config n k) :=
  {x | (count x j : ℝ) ≤ n / k + b * (1 + 3 / k) ^ t}

/-- **One color stays small.** If color `j` starts with at most `n/k + b`
nodes, `b ≥ k √(n log n)` and `b (1 + 3/k)^T ≤ n/k`, then after `T` rounds it
has more than `n/k + b (1 + 3/k)^T` nodes with probability at most `T/n²`. -/
theorem color_stays_small (hn : 1 ≤ n) (hk : 1 ≤ k) (x : Config n k) (j : Fin k) {b : ℝ}
    (hb0 : k * √(n * Real.log n) ≤ b) (hx : (count x j : ℝ) ≤ n / k + b) {T : ℕ}
    (hT : b * (1 + 3 / k) ^ T ≤ n / k) :
    expList (Tgt3 n) T (fun l => by
        classical exact if run x l ∈ balancedSet n j b T then (0 : ℝ) else 1)
      ≤ T * (1 / (n : ℝ) ^ 2) := by
  haveI := tgt3_nonempty hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : 1 ≤ 1 + 3 / (k : ℝ) := by
    have : 0 ≤ 3 / (k : ℝ) := by positivity
    linarith
  have hb : 0 ≤ b := le_trans (by positivity) hb0
  refine expList_escape (stepWith maj3) (by positivity) T (balancedSet n j b) x
    (by simpa [balancedSet] using hx) fun t ht y hy => ?_
  -- one round of Lemma 4.1 at scale `b_t = b (1 + 3/k)^t`
  have hbt0 : k * √(n * Real.log n) ≤ b * (1 + 3 / k) ^ t :=
    hb0.trans (le_mul_of_one_le_right hb (one_le_pow₀ hq))
  have hbt1 : b * (1 + 3 / k) ^ t ≤ n / k :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq ht.le) hb) hT
  have h41 := lemma_4_1 hn hk y j hbt0 hbt1 hy
  refine le_trans (avg_le_avg fun r => ?_) h41
  simp only [balancedSet, Set.mem_setOf_eq]
  split_ifs with h1 h2 h2
  · norm_num
  · norm_num
  · exact le_rfl
  · exfalso
    apply h1
    change (count (step y r) j : ℝ) ≤ _
    rw [pow_succ]
    push Not at h2
    have e : b * ((1 + 3 / k) ^ t * (1 + 3 / k)) = (1 + 3 / k) * (b * (1 + 3 / k) ^ t) := by ring
    rw [e]
    linarith

/-- **Theorem 4.2 (lower bound for 3-majority).** Let `k ≥ 3` and suppose every
color starts with at most `n/k + b` nodes, where `b ≥ k √(n log n)`. If
`b (1 + 3/k)^T ≤ n/k`, then the coloring after `T` rounds is monochromatic with
probability at most `k T / n²`. -/
theorem theorem_4_2 (hn : 1 ≤ n) (hk : 3 ≤ k) (x : Config n k) {b : ℝ}
    (hb0 : k * √(n * Real.log n) ≤ b) (hx : ∀ j, (count x j : ℝ) ≤ n / k + b) {T : ℕ}
    (hT : b * (1 + 3 / k) ^ T ≤ n / k) :
    expList (Tgt3 n) T (fun l => if Monochromatic (run x l) then (1 : ℝ) else 0)
      ≤ k * T / (n : ℝ) ^ 2 := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  -- a monochromatic coloring has a color above its threshold
  have hpt (l : List (Tgt3 n)) : (if Monochromatic (run x l) then (1 : ℝ) else 0)
      ≤ ∑ j, (if run x l ∈ balancedSet n j b T then (0 : ℝ) else 1) := by
    split_ifs with hm
    · obtain ⟨j, hj⟩ := hm
      have hcn : (count (run x l) j : ℝ) = n := by exact_mod_cast (mono_iff_count _ _).mp hj
      have hnot : run x l ∉ balancedSet n j b T := by
        simp only [balancedSet, Set.mem_setOf_eq, hcn, not_le]
        -- `n > 2n/k ≥ n/k + b_T`
        have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
        have : 2 * (n : ℝ) / k < n := by
          rw [div_lt_iff₀ hk0]; nlinarith
        have : (n : ℝ) / k + n / k = 2 * n / k := by ring
        linarith
      calc (1 : ℝ) = if run x l ∈ balancedSet n j b T then 0 else 1 := by rw [if_neg hnot]
        _ ≤ _ := single_le_sum (f := fun j => if run x l ∈ balancedSet n j b T then (0 : ℝ)
            else 1) (fun j _ => by split <;> norm_num) (mem_univ j)
    · exact sum_nonneg fun j _ => by split <;> norm_num
  calc _ ≤ expList (Tgt3 n) T
        (fun l => ∑ j, (if run x l ∈ balancedSet n j b T then (0 : ℝ) else 1)) :=
        expList_le_expList hpt
    _ = ∑ j, expList (Tgt3 n) T
        (fun l => if run x l ∈ balancedSet n j b T then (0 : ℝ) else 1) := expList_sum _ _ _
    _ ≤ ∑ _j : Fin k, (T : ℝ) * (1 / (n : ℝ) ^ 2) := by
        refine sum_le_sum fun j _ => ?_
        have h := color_stays_small hn (by omega) x j hb0 (hx j) hT
        convert h using 3
    _ = k * T / (n : ℝ) ^ 2 := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Theorem 4.2, logarithmic form.** Under the hypotheses of `theorem_4_2`,
the coloring is still not monochromatic after `T ≤ (k/3) log (n / (k b))`
rounds, except with probability `k T / n²`. With `b = max ((n/k)^{1-ε},
k √(n log n))` and `k ≤ n^{1/4-δ}`, this is `Ω(k log n)` rounds. -/
theorem theorem_4_2_log (hn : 1 ≤ n) (hk : 3 ≤ k) (x : Config n k) {b : ℝ}
    (hb0 : k * √(n * Real.log n) ≤ b) (hbpos : 0 < b)
    (hx : ∀ j, (count x j : ℝ) ≤ n / k + b) {T : ℕ}
    (hT : (T : ℝ) ≤ k / 3 * Real.log (n / (k * b))) :
    expList (Tgt3 n) T (fun l => if Monochromatic (run x l) then (1 : ℝ) else 0)
      ≤ k * T / (n : ℝ) ^ 2 := by
  refine theorem_4_2 hn hk x hb0 hx ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `(1 + 3/k)^T ≤ exp (3T/k) ≤ n / (k b)`
  have h1 : (1 + 3 / (k : ℝ)) ^ T ≤ exp (3 * T / k) := by
    calc (1 + 3 / (k : ℝ)) ^ T ≤ exp (3 / k) ^ T :=
          pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp (3 / (k : ℝ))]) T
      _ = exp (3 * T / k) := by rw [← exp_nat_mul]; ring_nf
  have h2 : exp (3 * T / k) ≤ n / (k * b) := by
    have hpos : 0 < (n : ℝ) / (k * b) := by positivity
    rw [← exp_log hpos]
    apply exp_le_exp.mpr
    rw [div_le_iff₀ hk0]
    linarith
  calc b * (1 + 3 / k) ^ T ≤ b * (n / (k * b)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hbpos.le
    _ = n / k := by field_simp

end Plurality
