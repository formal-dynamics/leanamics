import Undecided.MajorityStages
import Undecided.SequentialMartingale

/-! # Assembling the phases of the majority dynamics (UND-1)

`majority_explicit` is the explicit form of `Undecided.majority_whp`: if `log n ≥ 10⁴` and the
`a`-nodes outnumber the `b`-nodes by at least `10⁴ √(n log n)`, then the probability that not
all nodes hold `a` after `⌈10⁴ log n⌉` rounds is at most `2/n`.

With `Λ = √(n log n)` a round is bad with probability at most `p = 4/n²` (`four_exp_sqrt`).
The rounds are split as `T = (T₁ + 1) + 18 + T₃`:

* growth (`growth_stage`), `T₁ + 1` rounds with `T₁ = ⌈log n / log (201/200)⌉₊ ≤ 201 log n + 1`,
  so that `400Λ (201/200)^T₁ ≥ 7n/10`: the bias reaches `7n/10`;
* bridge (`bridge_stage`), `18` rounds: the potential `12 count b + count u` drops to `n/3`;
* final (`fin_stage`), `T₃ ≥ 12 log n` rounds: `(5/6)^T₃ ≤ 1/n²`.

The failure probability is at most `T p + (5/6)^T₃ n/3 ≤ 1/n + 1/(3n)`.
-/

namespace Undecided
open Finset Dynamics Real

/-- `n ≤ q ^ ⌈log n / log q⌉₊` for `q > 1`. -/
lemma le_pow_ceil {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 1 < q) :
    (n : ℝ) ≤ q ^ ⌈log n / log q⌉₊ := by
  have hlq : 0 < log q := log_pos hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← log_le_log_iff hn0 (by positivity), log_pow]
  have := Nat.le_ceil (log n / log q)
  rwa [div_le_iff₀ hlq] at this

/-- `log n ≥ 10⁴` forces `n ≥ 1`. -/
lemma one_le_of_log {n : ℕ} (hL : (10000 : ℝ) ≤ log n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp at hL
    linarith
  · exact h

/-- With `log n ≥ 10⁴`, `n ≥ 4·10⁶ log n` (from `exp x ≥ x³/6`). -/
lemma big_n {n : ℕ} (hL : (10000 : ℝ) ≤ log n) : 4000000 * log n ≤ (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast one_le_of_log hL
  have hL0 : (0 : ℝ) ≤ log n := by linarith
  have h1 := pow_div_factorial_le_exp (log (n : ℝ)) hL0 3
  rw [exp_log hn0] at h1
  norm_num [Nat.factorial] at h1
  have h2 : (10000 : ℝ) * 10000 ≤ log n * log n := mul_le_mul hL hL (by norm_num) hL0
  have h3 : (10000 : ℝ) * 10000 * log n ≤ log n * log n * log n :=
    mul_le_mul_of_nonneg_right h2 hL0
  nlinarith

variable {n : ℕ}

/-- The probability that all nodes hold `a` is one minus the miss probability. -/
lemma prob_allA_eq [NeZero n] (T : ℕ) (x : Config n) :
    expList (Fin n → Fin n) T
        (fun l => if l.foldl step x = (fun _ => Op.a) then (1 : ℝ) else 0)
      = 1 - missP (allA n) T x := by
  classical
  have h (l : List (Fin n → Fin n)) :
      (if l.foldl step x = (fun _ => Op.a) then (1 : ℝ) else 0)
        = 1 - (if l.foldl step x ∈ allA n then (0 : ℝ) else 1) := by
    by_cases hl : l.foldl step x = fun _ => .a
    · rw [if_pos hl, if_pos (show l.foldl step x ∈ allA n from hl)]
      norm_num
    · rw [if_neg hl, if_neg (show l.foldl step x ∉ allA n from hl)]
      norm_num
  simp_rw [h]
  rw [Sequential.expList_one_sub]
  rfl

/-- **UND-1, explicit form.** If `log n ≥ 10⁴` and the `a`-nodes outnumber the `b`-nodes by at
least `10⁴ √(n log n)` (any number of undecided nodes), then after `⌈10⁴ log n⌉` rounds not all
nodes hold `a` with probability at most `2/n`. -/
theorem majority_explicit (hL : (10000 : ℝ) ≤ log n) (x : Config n)
    (hx : 10000 * √(n * log n) ≤ (count x .a : ℝ) - count x .b) :
    missP (allA n) ⌈10000 * log n⌉₊ x ≤ 2 / n := by
  -- the size of `n`
  have hn1 : 1 ≤ n := one_le_of_log hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  haveI : NeZero n := ⟨by omega⟩
  have hL0 : (0 : ℝ) ≤ log n := by linarith
  have hbig := big_n hL
  -- the deviation `Λ = √(n log n)`
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = √((n : ℝ) * log n) := ⟨_, rfl⟩
  rw [← hΛdef] at hx
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; exact sqrt_nonneg _
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛdef]
    refine one_le_sqrt.mpr ?_
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hΛn : 2000 * Λ ≤ n := by
    have hle : (n : ℝ) * log n ≤ ((n : ℝ) / 2000) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hbig hn0.le]
    have := sqrt_le_sqrt hle
    rw [sqrt_sq (by positivity), ← hΛdef] at this
    linarith
  have hp := four_exp_sqrt hn1
  rw [← hΛdef] at hp
  set p := 4 * exp (-(2 * Λ ^ 2 / n)) with hpdef
  have hp0 : 0 ≤ p := by positivity
  -- growth: `T₁ + 1` rounds
  set T₁ := ⌈log n / log ((201 : ℝ) / 200)⌉₊ with hT₁def
  have hq : (1 : ℝ) < 201 / 200 := by norm_num
  have hpow : (n : ℝ) ≤ (201 / 200) ^ T₁ := le_pow_ceil hn1 hq
  have hlogq : (1 : ℝ) / 201 ≤ log (201 / 200) := by
    have := one_sub_inv_le_log_of_pos (x := (201 / 200 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  have hT₁ : (T₁ : ℝ) ≤ 201 * log n + 1 := by
    have h1 := Nat.ceil_lt_add_one (div_nonneg hL0 (log_pos hq).le)
    have h2 : log n / log ((201 : ℝ) / 200) ≤ 201 * log n := by
      rw [div_le_iff₀ (log_pos hq)]
      nlinarith
    rw [hT₁def]
    linarith
  have hθ : 7 * n / 10 ≤ theta n Λ T₁ := by
    rcases theta_reach (n := n) hΛ0 (by linarith) T₁ with h | h
    · exact h
    · have : (n : ℝ) ≤ Λ * (201 / 200) ^ T₁ := by nlinarith
      linarith
  have hA : missP {y | 7 * n / 10 ≤ bias y} (T₁ + 1) x ≤ ((T₁ + 1 : ℕ) : ℝ) * p :=
    le_trans (missP_mono (fun y hy => le_trans hθ hy.1) _ x)
      (growth_stage hn0 hΛ0 hΛn T₁ x (by unfold bias; linarith))
  -- bridge: `18` more rounds
  have hB : missP (finSet n) (T₁ + 1 + 18) x ≤ ((T₁ + 1 : ℕ) : ℝ) * p + ((18 : ℕ) : ℝ) * p := by
    have := missP_comp (B := {y | 7 * n / 10 ≤ bias y}) (D := finSet n) (T₁ := T₁ + 1)
      (T₂ := 18) (by positivity) (fun y hy => bridge_stage hn0 hΛ0 hΛn y hy) x
    rw [← hpdef] at this
    exact le_trans this (add_le_add hA le_rfl)
  -- final: `T₃` more rounds
  set T := ⌈10000 * log (n : ℝ)⌉₊ with hTdef
  have hTlo : 10000 * log (n : ℝ) ≤ T := Nat.le_ceil _
  have hThi : (T : ℝ) < 10000 * log n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsplit : T₁ + 1 + 18 ≤ T := by
    have : ((T₁ + 1 + 18 : ℕ) : ℝ) ≤ T := by
      push_cast
      linarith
    exact_mod_cast this
  obtain ⟨T₃, hT₃def⟩ : ∃ T₃, T = T₁ + 1 + 18 + T₃ := ⟨T - (T₁ + 1 + 18), by omega⟩
  have hT₃cast : (T : ℝ) = T₁ + 1 + 18 + T₃ := by rw [hT₃def]; push_cast; ring
  have hT₃ : 12 * log (n : ℝ) ≤ T₃ := by linarith
  have h56 : (5 / 6 : ℝ) ^ T₃ ≤ 1 / (n : ℝ) ^ 2 := by
    have hlog6 : (1 : ℝ) / 6 ≤ log (6 / 5) := by
      have := one_sub_inv_le_log_of_pos (x := (6 / 5 : ℝ)) (by norm_num)
      norm_num at this ⊢
      linarith
    have hn2 : (n : ℝ) ^ 2 ≤ (6 / 5) ^ T₃ := by
      rw [← log_le_log_iff (by positivity) (by positivity), log_pow, log_pow]
      have : (0 : ℝ) ≤ T₃ := Nat.cast_nonneg _
      push_cast
      nlinarith
    rw [show (5 / 6 : ℝ) ^ T₃ = 1 / (6 / 5) ^ T₃ by rw [one_div, ← inv_pow]; norm_num]
    exact one_div_le_one_div_of_le (by positivity) hn2
  have hC := missP_comp (B := finSet n) (D := allA n) (T₁ := T₁ + 1 + 18) (T₂ := T₃)
    (e := (5 / 6) ^ T₃ * ((n : ℝ) / 3) + T₃ * p) (by positivity)
    (fun y hy => le_trans (fin_stage hn0 hΛ0 (by linarith) T₃ y hy)
      (by have := mul_le_mul_of_nonneg_left (show pot y ≤ (n : ℝ) / 3 from hy)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 6) T₃)
          linarith)) x
  rw [← hT₃def] at hC
  -- the failure budget
  have hTp : (T : ℝ) * p ≤ 1 / n := by
    rw [hp, show (T : ℝ) * (4 / (n : ℝ) ^ 2) = 4 * T / n / n by field_simp,
      div_le_div_iff_of_pos_right hn0]
    rw [div_le_iff₀ hn0]
    nlinarith
  have hfin : (5 / 6 : ℝ) ^ T₃ * ((n : ℝ) / 3) ≤ 1 / n := by
    have := mul_le_mul_of_nonneg_right h56 (by positivity : (0 : ℝ) ≤ (n : ℝ) / 3)
    have e : 1 / (n : ℝ) ^ 2 * ((n : ℝ) / 3) = 1 / (3 * n) := by field_simp
    have : 1 / (3 * (n : ℝ)) ≤ 1 / n :=
      one_div_le_one_div_of_le hn0 (by linarith)
    linarith
  have hsum : ((T₁ + 1 : ℕ) : ℝ) * p + ((18 : ℕ) : ℝ) * p + T₃ * p = T * p := by
    rw [hT₃cast]
    push_cast
    ring
  have : 2 / (n : ℝ) = 1 / n + 1 / n := by ring
  linarith

end Undecided
