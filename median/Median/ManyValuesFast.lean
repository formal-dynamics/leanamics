import Median.BinaryMoves

/-! # Many values: the quadratic saturation move

The one-round move behind the `O(log log n)` saturation phase of `binary_consensus_fast`
(`Median/ManyValues.lean`). Below a constant fraction of `false` nodes, the expected next minority
is quadratic, `𝔼[m'] ≤ 3m²/n` (`expfalses_le`), so the minority squares its relative size each
round until it reaches `β = 512 log n`:

* `bernstein_move`: if the expected next minority is at most `(3/4) τ` for a threshold
  `τ ≥ 512 log n`, then one round brings the minority below `τ` except with probability `n⁻²`
  (Bernstein's inequality, `falses_tail_bernstein`);
* `quad_move`: from a minority `m < t`, one round gives `m' < max (4t²/n) (512 log n)` except
  with probability `n⁻²`.
-/

namespace Median

open Finset Real Dynamics

variable {n : ℕ} [NeZero n]

/-- **Bernstein move.** If the expected number of `false` nodes after one round is at most
`(3/4) τ` for a threshold `τ ≥ 512 log n`, then after one round fewer than `τ` nodes are `false`
except with probability `n⁻²`. -/
lemma bernstein_move (hL : (128 : ℝ) ≤ log n) {τ : ℝ} (hτ : 512 * log n ≤ τ)
    {y : Config n Bool} (hμ : ∑ v, avg (fcoord y v) ≤ 3 / 4 * τ) :
    1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool y).prob (· ∈ satSet n τ) := by
  classical
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hτ0 : 0 < τ := by linarith only [hL, hτ]
  have hμ0 : 0 ≤ ∑ v, avg (fcoord y v) :=
    Finset.sum_nonneg fun v _ => avg_nonneg fun p => fcoord_nonneg y v p
  -- Bernstein with variance proxy `s = 𝔼[m'] + 1` and deviation `d = τ - 𝔼[m'] ≥ τ/4`
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ∑ v, avg (fcoord y v) + 1 := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = τ - ∑ v, avg (fcoord y v) := ⟨_, rfl⟩
  have hs0 : 0 < s := by linarith only [hsdef, hμ0]
  have hvar : ∑ v, variance (fcoord y v) ≤ s := by
    have h1 : ∑ v, variance (fcoord y v) ≤ ∑ v, avg (fcoord y v) :=
      Finset.sum_le_sum fun v _ => variance_le_avg_of_zero_one (fcoord_zero_one y v)
    linarith only [h1, hsdef]
  have hd0 : 0 ≤ d := by linarith only [hddef, hμ, hτ0]
  have hd4 : τ / 4 ≤ d := by linarith only [hddef, hμ]
  -- the Bernstein denominator is at most `3τ`, and `(2 log n) (3τ) ≤ (τ/4)² ≤ d²`
  have hden : 2 * s * (1 + d / (3 * s)) ≤ 3 * τ := by
    have e : 2 * s * (1 + d / (3 * s)) = 2 * s + 2 * d / 3 := by
      field_simp
    rw [e]
    linarith only [hsdef, hddef, hμ0, hμ, hτ, hL]
  have hcD : (2 * log n) * (3 * τ) ≤ d ^ 2 := by
    have p1 : τ / 4 * (τ / 4) ≤ d * d := mul_self_le_mul_self (by linarith only [hτ0]) hd4
    have p2 : 96 * log n * τ ≤ τ * τ :=
      mul_le_mul_of_nonneg_right (by linarith only [hτ, hL]) hτ0.le
    rw [pow_two]
    linarith only [p1, p2]
  have hexp := bernstein_exp_le hs0 hd0 (by linarith only [hτ0]) hden hcD
  have hbad := falses_tail_bernstein y hd0 hs0 hvar
  -- every round that misses `satSet n τ` is a Bernstein deviation
  have h0 : ∀ r : Round n, 0 ≤
      (if ∑ v, avg (fcoord y v) + d ≤ falsesR (step y r) then (1 : ℝ) else 0) :=
    fun r => by split <;> norm_num
  have h1 : ∀ r : Round n, step y r ∉ satSet n τ →
      1 ≤ (if ∑ v, avg (fcoord y v) + d ≤ falsesR (step y r) then (1 : ℝ) else 0) := by
    intro r hr
    have hr' : ¬ (falsesR (step y r) < τ) := hr
    have hadd : ∑ v, avg (fcoord y v) + d = τ := by rw [hddef]; ring
    rw [hadd, if_pos (le_of_not_gt hr')]
  have hstep : 1 - avg (fun r : Round n =>
      if ∑ v, avg (fcoord y v) + d ≤ falsesR (step y r) then (1 : ℝ) else 0)
      ≤ (Median.kernel n Bool y).prob (· ∈ satSet n τ) :=
    Kernel.one_sub_avg_le_prob_ofStep step _ y _ h0 h1
  linarith only [hstep, hbad, hexp, exp_neg_two_log hn]

/-- **Quadratic saturation move.** From a minority below `t`, one round lands in
`satSet n (max (4t²/n) β)` except with probability `n⁻²`, where `β = 512 log n`: the expected
next minority is at most `3t²/n ≤ (3/4) max (4t²/n) β` (`expfalses_le`). -/
theorem quad_move (hL : (128 : ℝ) ≤ log n) {t : ℝ} {x : Config n Bool} (hx : falsesR x < t) :
    1 - 1 / (n : ℝ) ^ 2
      ≤ (Median.kernel n Bool x).prob
        (· ∈ satSet n (max (4 * t ^ 2 / (n : ℝ)) (512 * log n))) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  refine bernstein_move hL (le_max_right _ _) ?_
  have hsq : falsesR x ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (falsesR_nonneg x) hx.le 2
  calc ∑ v, avg (fcoord x v) ≤ 3 * falsesR x ^ 2 / n := expfalses_le x
    _ ≤ 3 * t ^ 2 / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hn0.le
    _ = 3 / 4 * (4 * t ^ 2 / n) := by ring
    _ ≤ 3 / 4 * max (4 * t ^ 2 / (n : ℝ)) (512 * log n) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)

end Median
