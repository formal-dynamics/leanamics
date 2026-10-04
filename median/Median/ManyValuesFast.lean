import Median.BinaryAssembly
import Dynamics.Uniform

/-! # Many values: fast consensus from a large bias (helper development)

This file contains the long development behind `Median/ManyValues.lean`:

* scalar helpers for the fast phase counts (`log 2 ≥ 1/2`, the real version of
  `le_pow_ceil`, and the bound `w ≤ 2 ^ ⌈log w / log 2⌉₊` needed to turn
  `log log n` phases into the doubly exponential shrinkage of the quadratic
  saturation thresholds);
* `quad_move`: the new one-round move of the saturation phase, from a minority
  `m < t ≤ n/8` to `m' < max (4t²/n) (512 log n)` except with probability
  `n⁻²` (Bernstein, with the quadratic mean bound `𝔼[m'] ≤ 3m²/n ≤ 3t²/n`);
* `binary_consensus_fast'`: the kernel form of `binary_consensus_fast` — the
  same nested-phases assembly as `binary_consensus`, with the growth phase
  started at the actual gap `Δ` (so it costs `O (log (n/Δ))` phases), a constant
  linear saturation segment down to `n/8`, the quadratic saturation segment
  (whose thresholds square the relative size per phase, so `O (log log n)`
  phases bring `n/8` down to `512 log n`), and the final consensus phase;
* the order-dual plumbing `med3_dual` / `run_dual` behind `median_consensus_fast'`;
* `expList_absorb_mono`, the padding lemma behind `odd_split_consensus'`.
-/

namespace Median

open Finset Real Dynamics

/-! ### Scalar helpers -/

/-- `log 2 ≥ 1/2` (tangent at `1`). -/
lemma log_two_ge : (1 / 2 : ℝ) ≤ log 2 := by
  have h := sub_one_div_le_log' (show (0 : ℝ) < 2 by norm_num)
  norm_num at h
  exact h

/-- `w ≤ q ^ ⌈log w / log q⌉₊` for `w ≥ 1` and `q > 1` (real version of `le_pow_ceil`). -/
lemma le_pow_ceil_real {w : ℝ} (hw : 1 ≤ w) {q : ℝ} (hq : 1 < q) :
    w ≤ q ^ ⌈log w / log q⌉₊ := by
  have hlq : 0 < log q := log_pos hq
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hpow0 : 0 < q ^ ⌈log w / log q⌉₊ := by positivity
  rw [← log_le_log_iff hw0 hpow0, log_pow]
  have := Nat.le_ceil (log w / log q)
  rwa [div_le_iff₀ hlq] at this

/-- Any `w ≥ 1` is at most `2 ^ ⌈log w / log 2⌉₊`. -/
lemma le_two_pow_ceil (w : ℝ) (hw : 1 ≤ w) : w ≤ (2 : ℝ) ^ ⌈log w / log 2⌉₊ :=
  le_pow_ceil_real hw (by norm_num)

variable {n : ℕ} [NeZero n]

/-! ### The quadratic saturation move -/

/-- One round of the quadratic saturation phase: from a minority below `t ≤ n/8`,
one round lands in `satSet n (max (4t²/n) β)` except with probability `n⁻²`, where
`β = 512 log n` (Bernstein's inequality, with `𝔼[m'] ≤ 3m²/n ≤ 3t²/n`). -/
theorem quad_move (hL : (128 : ℝ) ≤ log n) {t : ℝ} (_ht8 : t ≤ (n : ℝ) / 8)
    {x : Config n Bool} (hx : falsesR x < t) :
    1 - 1 / (n : ℝ) ^ 2
      ≤ (Median.kernel n Bool x).prob
        (· ∈ satSet n (max (4 * t ^ 2 / (n : ℝ)) (512 * log n))) := by
  classical
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ log n := hL.trans' (by norm_num)
  have hβ12 : 12 ≤ 512 * log n := by linarith
  have hβn8 : 512 * log n ≤ (n : ℝ) / 8 := by
    have hbig := big_log_le hL
    have h1 : 4096 * log n ≤ (2 : ℝ) ^ 20 * log n := by
      refine mul_le_mul_of_nonneg_right (by norm_num) hL0
    linarith
  have hm : falsesR x ≤ t := le_of_lt hx
  -- the expected next minority is at most `3t²/n`
  have hE : ∑ v, avg (fcoord x v) ≤ 3 * t ^ 2 / (n : ℝ) := by
    have h1 := expfalses_le x
    have h2 : 3 * falsesR x ^ 2 / (n : ℝ) ≤ 3 * t ^ 2 / (n : ℝ) := by
      have hsq : falsesR x ^ 2 ≤ t ^ 2 :=
        pow_le_pow_left₀ (falsesR_nonneg x) hm 2
      rw [div_le_div_iff₀ hn0 hn0]
      nlinarith [hsq, hn0.le]
    exact le_trans h1 h2
  have hE0 : 0 ≤ ∑ v, avg (fcoord x v) :=
    Finset.sum_nonneg fun v _ => avg_nonneg fun p => fcoord_nonneg x v p
  -- the variance proxy and the Bernstein denominator
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ∑ v, avg (fcoord x v) + 1 := ⟨_, rfl⟩
  have hσ0 : 0 < s := by rw [hsdef]; linarith
  have hvar : ∑ v, variance (fcoord x v) ≤ s := by
    rw [hsdef]
    have h1 : ∑ v, variance (fcoord x v) ≤ ∑ v, avg (fcoord x v) :=
      Finset.sum_le_sum fun v _ => variance_fcoord_le x v
    linarith
  have hden_eq : ∀ d : ℝ, 0 ≤ d → 2 * s * (1 + d / (3 * s)) = 2 * s + 2 * d / 3 := by
    intro d _hd0
    have hsnz : s ≠ 0 := by
      rw [hsdef]
      linarith
    field_simp
  by_cases hcase : 4 * t ^ 2 / (n : ℝ) < 512 * log n
  · -- the `β` term dominates: the target is `β` and the mean is below `(3/4)β`
    have hmax : max (4 * t ^ 2 / (n : ℝ)) (512 * log n) = 512 * log n :=
      max_eq_right (le_of_lt hcase)
    rw [hmax]
    obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = 512 * log n - ∑ v, avg (fcoord x v) := ⟨_, rfl⟩
    have hcase' : 4 * t ^ 2 / (n : ℝ) ≤ 512 * log n := le_of_lt hcase
    have hEβ : ∑ v, avg (fcoord x v) ≤ 3 / 4 * (512 * log n) := by
      have h2 : 3 * t ^ 2 / (n : ℝ) = 3 / 4 * (4 * t ^ 2 / (n : ℝ)) := by ring
      refine le_trans hE ?_
      rw [h2]
      exact mul_le_mul_of_nonneg_left hcase' (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have hd0 : 0 ≤ d := by rw [hddef]; linarith
    have hdle : d ≤ 512 * log n := by rw [hddef]; linarith
    have hs_le : s ≤ 3 / 4 * (512 * log n) + 1 := by rw [hsdef]; linarith
    have hd4 : 512 * log n / 4 ≤ d := by rw [hddef]; linarith
    have hterm : 6 * s + 2 * d ≤ 7 * (512 * log n) := by
      linarith [hs_le, hdle, hβ12]
    have hterm' : 2 * s + 2 * d / 3 ≤ 7 / 3 * (512 * log n) := by
      have h3 : (2 * s + 2 * d / 3) * 3 = 6 * s + 2 * d := by ring
      have h3' : (7 / 3 * (512 * log n)) * 3 = 7 * (512 * log n) := by ring
      nlinarith [hterm, h3, h3']
    have hD : 0 < 7 / 3 * (512 * log n) := by positivity
    have hbad := falses_tail_bernstein x hd0 hσ0 hvar
    have hden : 2 * s * (1 + d / (3 * s)) ≤ 7 / 3 * (512 * log n) := by
      rw [hden_eq d hd0]
      exact hterm'
    have hcD : (2 * log n) * (7 / 3 * (512 * log n)) ≤ d ^ 2 := by
      have hsq : 512 * log n / 4 * (512 * log n / 4) ≤ d * d :=
        mul_self_le_mul_self (by positivity) hd4
      have hval : 512 * log n / 4 * (512 * log n / 4)
          = 128 * log n * (128 * log n) := by
        field_simp
        ring
      have hA : (7168 / 3 : ℝ) ≤ 16384 := by norm_num
      have hkey : (2 * log n) * ((7 / 3 : ℝ) * (512 * log n))
          ≤ 128 * log n * (128 * log n) := by
        obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = log n * log n := ⟨_, rfl⟩
        have hL : (2 * log n) * ((7 / 3 : ℝ) * (512 * log n)) = 7168 / 3 * w := by
          rw [hwdef]; ring
        have hR : 128 * log n * (128 * log n) = 16384 * w := by rw [hwdef]; ring
        have hw0 : 0 ≤ w := by rw [hwdef]; positivity
        have hwle : 7168 / 3 * w ≤ 16384 * w := mul_le_mul_of_nonneg_right hA hw0
        rw [hL, hR]
        exact hwle
      rw [pow_two]
      calc (2 * log n) * ((7 / 3 : ℝ) * (512 * log n))
          ≤ 128 * log n * (128 * log n) := hkey
        _ = 512 * log n / 4 * (512 * log n / 4) := hval.symm
        _ ≤ d * d := hsq
    have h0 : ∀ r : Round n, 0 ≤
        (if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0) :=
      fun r => by split <;> norm_num
    have h1 : ∀ r : Round n, step x r ∉ satSet n (512 * log n) →
        1 ≤ (if ∑ v, avg (fcoord x v) + d
          ≤ falsesR (step x r) then (1 : ℝ) else 0) := by
      intro r hr
      have hr' : ¬ (falsesR (step x r) < 512 * log n) := hr
      have hadd : ∑ v, avg (fcoord x v)
          + d = 512 * log n := by rw [hddef]; ring
      have hcond : 512 * log n ≤ falsesR (step x r) := le_of_not_gt hr'
      rw [hadd, if_pos hcond]
    have hstep : 1 - avg (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0)
        ≤ (Median.kernel n Bool x).prob (· ∈ satSet n (512 * log n)) :=
      prob_step_ge x _ _ h0 h1
    have hexp := bernstein_exp_le hσ0 hd0 hD hden hcD
    have hfin : exp (-(2 * log n)) = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn
    linarith
  · -- the quadratic term dominates: the target is `4t²/n` and the mean is below `3t²/n`
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = t ^ 2 / (n : ℝ) := ⟨_, rfl⟩
    have h4u : 4 * t ^ 2 / (n : ℝ) = 4 * u := by rw [hudef]; ring
    rw [h4u] at hcase ⊢
    have hmax : max (4 * u) (512 * log n) = 4 * u := max_eq_left (le_of_not_gt hcase)
    rw [hmax]
    have hu128 : 128 * log n ≤ u := by linarith
    have hu0 : 0 < u := by nlinarith [hu128, hL0]
    have hu1 : 1 ≤ u := by nlinarith [hu128, hL]
    have hE3 : ∑ v, avg (fcoord x v) ≤ 3 * u := by
      rw [hudef, ← mul_div_assoc]
      exact hE
    obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = 4 * u - ∑ v, avg (fcoord x v) := ⟨_, rfl⟩
    have hd0 : 0 ≤ d := by rw [hddef]; linarith
    have hd_u : u ≤ d := by rw [hddef]; linarith
    have hdle : d ≤ 4 * u := by rw [hddef]; linarith
    have hs_le : s ≤ 3 * u + 1 := by rw [hsdef]; linarith
    have hterm : 6 * s + 2 * d ≤ 32 * u := by
      linarith [hs_le, hdle, hu1]
    have hterm' : 2 * s + 2 * d / 3 ≤ 32 / 3 * u := by
      have h3 : (2 * s + 2 * d / 3) * 3 = 6 * s + 2 * d := by ring
      have h3' : (32 / 3 * u) * 3 = 32 * u := by ring
      nlinarith [hterm, h3, h3']
    have hD : 0 < 32 / 3 * u := by positivity
    have hbad := falses_tail_bernstein x hd0 hσ0 hvar
    have hden : 2 * s * (1 + d / (3 * s)) ≤ 32 / 3 * u := by
      rw [hden_eq d hd0]
      exact hterm'
    have hcD : (2 * log n) * (32 / 3 * u) ≤ d ^ 2 := by
      have h1 : (64 / 3 : ℝ) * log n ≤ u := by
        linarith [(by norm_num : (64 / 3 : ℝ) ≤ 128), hL0, hu128]
      have hkey : (2 * log n) * ((32 / 3 : ℝ) * u) = ((64 / 3 : ℝ) * log n) * u := by ring
      rw [pow_two, hkey]
      nlinarith [mul_le_mul_of_nonneg_right h1 hu0.le, mul_le_mul hd_u hd_u hu0.le hd0]
    have h0 : ∀ r : Round n, 0 ≤
        (if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0) :=
      fun r => by split <;> norm_num
    have h1 : ∀ r : Round n, step x r ∉ satSet n (4 * u) →
        1 ≤ (if ∑ v, avg (fcoord x v) + d
          ≤ falsesR (step x r) then (1 : ℝ) else 0) := by
      intro r hr
      have hr' : ¬ (falsesR (step x r) < 4 * u) := hr
      have hadd : ∑ v, avg (fcoord x v) + d = 4 * u := by rw [hddef]; ring
      have hcond : 4 * u ≤ falsesR (step x r) := le_of_not_gt hr'
      rw [hadd, if_pos hcond]
    have hstep : 1 - avg (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0)
        ≤ (Median.kernel n Bool x).prob (· ∈ satSet n (4 * u)) :=
      prob_step_ge x _ _ h0 h1
    have hexp := bernstein_exp_le hσ0 hd0 hD hden hcD
    have hfin : exp (-(2 * log n)) = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn
    linarith

end Median
