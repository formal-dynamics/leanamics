import Undecided.Basic
import Dynamics.Concentration

/-! # One round of the undecided-state dynamics: concentration (UND-1)

After one round from `x`, the number of nodes in state `o` is a sum over the nodes `v` of
indicators that depend only on the node `r v` sampled by `v`, so Hoeffding's inequality
(`Dynamics.avg_hoeffding`) applies. A round is *good* when the numbers of `a`-, `b`- and
undecided nodes are within `Λ` of their expectations in the four directions used by the
analysis; `bad_round` bounds the probability of a bad round by `4 exp(-2Λ²/n)`, which is
`4/n²` for `Λ = √(n log n)` (`bad_round_sqrt`).
-/

namespace Undecided
open Finset Dynamics Real

variable {n : ℕ}

/-- The indicator that node `v`, sampling node `w`, is in state `o` after the round. -/
noncomputable def ind (x : Config n) (o : Op) (v w : Fin n) : ℝ :=
  if update (x v) (x w) = o then 1 else 0

lemma ind_01 (x : Config n) (o : Op) (v w : Fin n) : ind x o v w = 0 ∨ ind x o v w = 1 := by
  unfold ind
  split <;> simp

lemma count_step_ind (x : Config n) (r : Fin n → Fin n) (o : Op) :
    (count (step x r) o : ℝ) = ∑ v, ind x o v (r v) :=
  count_step_eq_sum x r o

variable [NeZero n]

/-- The expected count after one round is the sum of the per-node probabilities. -/
lemma avg_count_step (x : Config n) (o : Op) :
    avg (fun r : Fin n → Fin n => (count (step x r) o : ℝ)) = ∑ v, avg (ind x o v) := by
  simp_rw [count_step_ind]
  rw [avg_sum]
  exact sum_congr rfl fun v _ => avg_eval n v (ind x o v)

/-- **Upper tail** of a count after one round (Hoeffding). -/
lemma tail_upper (x : Config n) (o : Op) {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun r : Fin n → Fin n =>
      if avg (fun r' : Fin n → Fin n => (count (step x r') o : ℝ)) + lam ≤ count (step x r) o
      then (1 : ℝ) else 0) ≤ exp (-(2 * lam ^ 2 / n)) := by
  rw [avg_count_step]
  simp_rw [count_step_ind]
  exact avg_hoeffding (ind x o) (ind_01 x o) hlam

/-- **Lower tail** of a count after one round (Hoeffding applied to the complements). -/
lemma tail_lower (x : Config n) (o : Op) {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun r : Fin n → Fin n =>
      if (count (step x r) o : ℝ) + lam ≤ avg (fun r' : Fin n → Fin n => (count (step x r') o : ℝ))
      then (1 : ℝ) else 0) ≤ exp (-(2 * lam ^ 2 / n)) := by
  have h01 : ∀ v w, (fun v w => 1 - ind x o v w) v w = 0 ∨ (fun v w => 1 - ind x o v w) v w = 1 :=
    fun v w => by rcases ind_01 x o v w with h | h <;> simp [h]
  have key := avg_hoeffding (fun v w => 1 - ind x o v w) h01 hlam
  have hmean : ∑ v, avg (fun w => 1 - ind x o v w)
      = n - avg (fun r' : Fin n → Fin n => (count (step x r') o : ℝ)) := by
    rw [avg_count_step]
    simp_rw [avg_sub, avg_const]
    rw [sum_sub_distrib]
    simp
  refine le_trans (avg_le_avg fun r => ?_) key
  have hsum : ∑ v, (fun v w => 1 - ind x o v w) v (r v) = n - count (step x r) o := by
    rw [count_step_ind]
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hmean, hsum]
  split_ifs with h1 h2 <;> first | (exfalso; apply h2; linarith) | norm_num

/-- **Bad rounds.** If every configuration whose counts are within `Λ` of the expected counts
(from below for `a`, from above for `b`, both ways for the undecided nodes) lies in `B`, then one
round from `x` misses `B` with probability at most `4 exp(-2Λ²/n)`. -/
lemma bad_round (x : Config n) (B : Set (Config n)) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hB : ∀ y : Config n,
      avg (fun r : Fin n → Fin n => (count (step x r) .a : ℝ)) < count y .a + Λ →
      (count y .b : ℝ) < avg (fun r : Fin n → Fin n => (count (step x r) .b : ℝ)) + Λ →
      avg (fun r : Fin n → Fin n => (count (step x r) .u : ℝ)) < count y .u + Λ →
      (count y .u : ℝ) < avg (fun r : Fin n → Fin n => (count (step x r) .u : ℝ)) + Λ →
      y ∈ B) :
    avg (fun r : Fin n → Fin n => by classical exact if step x r ∈ B then (0 : ℝ) else 1)
      ≤ 4 * exp (-(2 * Λ ^ 2 / n)) := by
  classical
  set Ea := avg (fun r : Fin n → Fin n => (count (step x r) .a : ℝ))
  set Eb := avg (fun r : Fin n → Fin n => (count (step x r) .b : ℝ))
  set Eu := avg (fun r : Fin n → Fin n => (count (step x r) .u : ℝ))
  have hpt (r : Fin n → Fin n) : (if step x r ∈ B then (0 : ℝ) else 1)
      ≤ (if (count (step x r) .a : ℝ) + Λ ≤ Ea then 1 else 0)
        + (if Eb + Λ ≤ (count (step x r) .b : ℝ) then 1 else 0)
        + (if (count (step x r) .u : ℝ) + Λ ≤ Eu then 1 else 0)
        + (if Eu + Λ ≤ (count (step x r) .u : ℝ) then 1 else 0) := by
    have h1 := ite_nonneg (α := ℝ) zero_le_one le_rfl (p := (count (step x r) .a : ℝ) + Λ ≤ Ea)
    have h2 := ite_nonneg (α := ℝ) zero_le_one le_rfl (p := Eb + Λ ≤ (count (step x r) .b : ℝ))
    have h3 := ite_nonneg (α := ℝ) zero_le_one le_rfl (p := (count (step x r) .u : ℝ) + Λ ≤ Eu)
    have h4 := ite_nonneg (α := ℝ) zero_le_one le_rfl (p := Eu + Λ ≤ (count (step x r) .u : ℝ))
    by_cases hmem : step x r ∈ B
    · rw [if_pos hmem]
      linarith
    · rw [if_neg hmem]
      by_cases ha : (count (step x r) .a : ℝ) + Λ ≤ Ea
      · rw [if_pos ha]; linarith
      by_cases hb : Eb + Λ ≤ (count (step x r) .b : ℝ)
      · rw [if_pos hb]; linarith
      by_cases hu1 : (count (step x r) .u : ℝ) + Λ ≤ Eu
      · rw [if_pos hu1]; linarith
      by_cases hu2 : Eu + Λ ≤ (count (step x r) .u : ℝ)
      · rw [if_pos hu2]; linarith
      exact absurd (hB _ (by linarith) (by linarith) (by linarith) (by linarith)) hmem
  refine le_trans (avg_le_avg hpt) ?_
  rw [avg_add, avg_add, avg_add]
  have t1 := tail_lower x .a hΛ
  have t2 := tail_upper x .b hΛ
  have t3 := tail_lower x .u hΛ
  have t4 := tail_upper x .u hΛ
  linarith

omit [NeZero n] in
/-- `exp (-2 log n) = 1/n²`. -/
lemma exp_neg_two_log {n : ℕ} (hn : 1 ≤ n) : exp (-(2 * log n)) = 1 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [exp_neg, show 2 * log n = log ((n : ℝ) ^ 2) by
    rw [log_pow]; norm_num, exp_log (by positivity), one_div]

omit [NeZero n] in
/-- With `Λ = √(n log n)` the bad-round bound is `4/n²`. -/
lemma four_exp_sqrt (hn : 1 ≤ n) :
    4 * exp (-(2 * √((n : ℝ) * log n) ^ 2 / n)) = 4 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
  rw [sq_sqrt (mul_nonneg hn0.le hL), show 2 * ((n : ℝ) * log n) / n = 2 * log n by
    field_simp, exp_neg_two_log hn]
  ring

end Undecided
