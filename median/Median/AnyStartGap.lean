import Median.AnyStartAux
import Median.AnyStartMoments
import Median.AnyStartScalar

/-! # Any start: the gap of the binary dynamics through one round

The gap `g = #true - #false` (`gapR`) of a binary configuration:

* flipping every opinion commutes with the dynamics, negates the gap and preserves consensus
  (`step_flip`, `run_flip`, `gapR_flip`, `notConsensus_flip`), so negative gaps reduce to
  positive ones;
* after one round the gap is `2 ∑ᵥ coordᵥ - n`, a function of independent coordinates
  (`gapR_step`), with mean `meanGap y = g (3/2 - g²/(2n²))` (`meanGap_eq`): at least `g` for
  `g ≥ 0`, at least `11g/8` for `0 ≤ g ≤ n/2`, and at most `3|g|/2` in absolute value;
* near balance (`|g| ≤ n/4`) every coordinate has variance at least `1/10`
  (`one_tenth_le_variance_coord`).
-/

namespace Median
open Finset Real Dynamics

variable {n : ℕ}

/-! ### Flipping every opinion -/

/-- Flipping every opinion commutes with one round. -/
lemma step_flip (y : Config n Bool) (r : Round n) :
    step (fun v => !y v) r = fun v => !step y r v := by
  funext v
  show med3 (!y v) (!y (r v).1) (!y (r v).2) = !med3 (y v) (y (r v).1) (y (r v).2)
  cases y v <;> cases y (r v).1 <;> cases y (r v).2 <;> rfl

/-- Flipping every opinion commutes with any run. -/
lemma run_flip (y : Config n Bool) (l : List (Round n)) :
    run (fun v => !y v) l = fun v => !run y l v := by
  induction l generalizing y with
  | nil => rfl
  | cons r l ih => rw [run_cons, run_cons, step_flip, ih]

/-- Flipping every opinion negates the gap. -/
lemma gapR_flip (y : Config n Bool) : gapR (fun v => !y v) = -gapR y := by
  have h : (ones (fun v => !y v) : ℝ) = falsesR y := by
    rw [ones_eq_sum, falsesR_eq_sum]
    refine sum_congr rfl fun v _ => ?_
    cases y v <;> simp
  simp only [gapR, falsesR] at h ⊢
  rw [h]
  ring

/-- Flipping every opinion preserves consensus. -/
lemma consensus_flip_iff {y : Config n Bool} : Consensus (fun v => !y v) ↔ Consensus y := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨!c, fun v => by simp [← hc v]⟩
  · rintro ⟨c, hc⟩
    exact ⟨!c, fun v => by simp [hc v]⟩

/-- Flipping every opinion preserves `notConsensus`. -/
lemma notConsensus_flip (y : Config n Bool) : notConsensus (fun v => !y v) = notConsensus y := by
  by_cases h : Consensus y
  · rw [notConsensus_cons h, notConsensus_cons (consensus_flip_iff.mpr h)]
  · rw [notConsensus_noncons h, notConsensus_noncons (mt consensus_flip_iff.mp h)]

/-! ### The gap after one round -/

/-- The gap is at most `n` in absolute value. -/
lemma abs_gapR_le (y : Config n Bool) : |gapR y| ≤ n := by
  have h : (ones y : ℝ) ≤ n := by exact_mod_cast ones_le y
  have h0 : (0 : ℝ) ≤ ones y := Nat.cast_nonneg _
  rw [gapR_two, abs_le]
  constructor <;> linarith

/-- After one round the gap is `2 ∑ᵥ coordᵥ - n`. -/
lemma gapR_step (y : Config n Bool) (r : Round n) :
    gapR (step y r) = 2 * ∑ v, coord y v (r v) - n := by
  rw [gapR_two, ones_step_sum]

/-- The mean of the gap after one round, `2 ∑ᵥ 𝔼 coordᵥ - n`. -/
noncomputable def meanGap (y : Config n Bool) : ℝ := 2 * ∑ v, avg (coord y v) - n

/-- The gap after one round is its mean plus twice a sum of independent centered coordinates. -/
lemma gapR_step_eq (y : Config n Bool) (r : Round n) :
    gapR (step y r) = 2 * ∑ v, (coord y v (r v) - avg (coord y v)) + meanGap y := by
  rw [gapR_step, meanGap, sum_sub_distrib]
  ring

variable [NeZero n]

/-- **The mean gap after one round** is `g (3/2 - g²/(2n²))`. -/
lemma meanGap_eq (y : Config n Bool) :
    meanGap y = gapR y * (3 / 2 - gapR y ^ 2 / (2 * n ^ 2)) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [meanGap, sum_avg_coord, ones_mul_falses, gapR_two]
  field_simp
  ring

/-- The factor `3/2 - g²/(2n²)` of the mean gap lies in `[1, 3/2]`. -/
lemma meanGap_factor_mem (y : Config n Bool) :
    1 ≤ 3 / 2 - gapR y ^ 2 / (2 * n ^ 2) ∧ 3 / 2 - gapR y ^ 2 / (2 * n ^ 2) ≤ 3 / 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hg : gapR y ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_gapR_le y) 2
  have h1 : gapR y ^ 2 / (2 * n ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h0 : 0 ≤ gapR y ^ 2 / (2 * n ^ 2) := by positivity
  constructor <;> linarith

/-- From a nonnegative gap, the mean gap after one round is at least the gap. -/
lemma gapR_le_meanGap (y : Config n Bool) (hg : 0 ≤ gapR y) : gapR y ≤ meanGap y := by
  rw [meanGap_eq]
  exact le_mul_of_one_le_right hg (meanGap_factor_mem y).1

/-- The mean gap after one round is at most `3|g|/2` in absolute value. -/
lemma abs_meanGap_le (y : Config n Bool) : |meanGap y| ≤ 3 / 2 * |gapR y| := by
  have hq := meanGap_factor_mem y
  have hpos : 0 < 3 / 2 - gapR y ^ 2 / (2 * n ^ 2) := by linarith [hq.1]
  rw [meanGap_eq, abs_mul, abs_of_pos hpos, mul_comm]
  exact mul_le_mul_of_nonneg_right hq.2 (abs_nonneg _)

/-- For `0 ≤ g ≤ n/2` the mean gap after one round is at least `11g/8`. -/
lemma meanGap_ge (y : Config n Bool) (hg0 : 0 ≤ gapR y) (hg : gapR y ≤ n / 2) :
    11 / 8 * gapR y ≤ meanGap y := by
  have := expones_ge y hg0 hg
  rw [meanGap]
  linarith

/-- **Variance near balance.** If `|g| ≤ n/4`, every coordinate of the next round has variance
at least `1/10`: a `true` node stays `true` with probability `1 - f²` and a `false` node turns
`true` with probability `o²`, where the fractions `f` of `false` and `o` of `true` nodes lie in
`[3/8, 5/8]`. -/
lemma one_tenth_le_variance_coord (y : Config n Bool) (hg : |gapR y| ≤ n / 4) (v : Fin n) :
    1 / 10 ≤ variance (coord y v) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hsum := falses_plus_ones y
  have hgap := gapR_eq y
  have hab := abs_le.mp hg
  rw [variance_of_zero_one (coord_zero_one y v)]
  cases hv : y v with
  | true =>
    rw [avg_coord_of_true y hv]
    have h1 : 3 / 8 ≤ falsesR y / n := by
      rw [le_div_iff₀ hn]
      linarith
    have h2 : falsesR y / n ≤ 5 / 8 := by
      rw [div_le_iff₀ hn]
      linarith
    have := sq_mul_one_sub_sq_ge h1 h2
    linarith
  | false =>
    rw [avg_coord_of_false y hv]
    have h1 : 3 / 8 ≤ (ones y : ℝ) / n := by
      rw [le_div_iff₀ hn]
      linarith
    have h2 : (ones y : ℝ) / n ≤ 5 / 8 := by
      rw [div_le_iff₀ hn]
      linarith
    exact sq_mul_one_sub_sq_ge h1 h2

end Median
