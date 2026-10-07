import Median.AnyStartGap

/-! # Any start: the potential and its one-round drift

The potential of a binary configuration with gap `g` is `gapPot y = exp (-|g| / (256 √n))`, in
`(0, 1]` and small once `|g|` is large. One round contracts it in expectation by `e^{-1/65536}`,
up to the additive error `e^{1/131072 - √n/512}` (`avg_gapPot_step`, for `n ≥ 10`). By the flip
symmetry take `g ≥ 0`; then:

* **far from balance** (`√n/64 ≤ g ≤ n/2`, `avg_gapPot_step_far`): `|g'| ≥ g'`, Hoeffding's lemma
  at every node bounds the exponential moment of the next gap (`avg_exp_neg_gapR_step`), and the
  mean gap grows to at least `11g/8`;
* **beyond `n/2`** (`avg_gapPot_step_huge`): the same bound, with mean gap above `n/2`, gives the
  additive error;
* **near balance** (`g ≤ √n/64`, `avg_gapPot_step_near`): the next gap has variance at least
  `n/10`, so by Paley-Zygmund (`avg_pz_zero_one`) it is at least `√n/4` in absolute value, where
  the potential is at most `e^{-1/1024}`, with probability at least `9/64`. This is where the
  symmetry of a balanced configuration breaks.
-/

namespace Median
open Finset Real Dynamics

variable {n : ℕ}

/-- The potential `exp (-|g| / (256 √n))` of a binary configuration with gap `g`. -/
noncomputable def gapPot (y : Config n Bool) : ℝ := exp (-(|gapR y| / (256 * √(n : ℝ))))

/-- The potential is positive. -/
lemma gapPot_pos (y : Config n Bool) : 0 < gapPot y := exp_pos _

/-- The potential is at most `1`. -/
lemma gapPot_le_one (y : Config n Bool) : gapPot y ≤ 1 := by
  rw [gapPot, exp_le_one_iff, neg_nonpos]
  positivity

/-- Flipping every opinion preserves the potential. -/
lemma gapPot_flip (y : Config n Bool) : gapPot (fun v => !y v) = gapPot y := by
  rw [gapPot, gapPot, gapR_flip, abs_neg]

variable [NeZero n]

/-- `√n > 0` for `n ≠ 0`. -/
lemma sqrt_cast_pos : 0 < √(n : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos n))

/-- The potential is at least `e^{-c}` while `|g| ≤ 256 c √n`. -/
lemma exp_neg_le_gapPot {c : ℝ} {y : Config n Bool} (h : |gapR y| ≤ 256 * c * √(n : ℝ)) :
    exp (-c) ≤ gapPot y := by
  have hs := sqrt_cast_pos (n := n)
  rw [gapPot, exp_le_exp, neg_le_neg_iff, div_le_iff₀ (by positivity)]
  linarith

/-- The potential is at most `e^{-c}` once `|g| ≥ 256 c √n`. -/
lemma gapPot_le_exp_neg {c : ℝ} {y : Config n Bool} (h : 256 * c * √(n : ℝ) ≤ |gapR y|) :
    gapPot y ≤ exp (-c) := by
  have hs := sqrt_cast_pos (n := n)
  rw [gapPot, exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  linarith

/-! ### Far from balance: the exponential moment -/

/-- **Exponential moment of the next gap** (Hoeffding's lemma at every node): for every real `c`,
`𝔼 exp (-c g') ≤ exp (-c 𝔼g' + n c²/2)`. -/
lemma avg_exp_neg_gapR_step (y : Config n Bool) (c : ℝ) :
    avg (fun r : Round n => exp (-(c * gapR (step y r))))
      ≤ exp (-(c * meanGap y) + n * c ^ 2 / 2) := by
  have e (r : Round n) : exp (-(c * gapR (step y r)))
      = exp (c * n) * exp (-(2 * c) * ∑ v, coord y v (r v)) := by
    rw [gapR_step, ← exp_add]
    congr 1
    ring
  simp_rw [e]
  rw [avg_const_mul]
  calc exp (c * n) * avg (fun r : Round n => exp (-(2 * c) * ∑ v, coord y v (r v)))
      ≤ exp (c * n) * exp (-(2 * c) * ∑ v, avg (coord y v) + n * ((-(2 * c)) ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left (avg_exp_sum_le (coord y) (coord_zero_one y) _) (exp_pos _).le
    _ = exp (-(c * meanGap y) + n * c ^ 2 / 2) := by
        rw [← exp_add, meanGap]
        congr 1
        ring

/-- The expected potential after one round, through the exponential moment of the next gap:
at most `exp (-𝔼g'/(256 √n) + 1/131072)`. -/
lemma avg_gapPot_step_le (y : Config n Bool) :
    avg (fun r : Round n => gapPot (step y r))
      ≤ exp (-(meanGap y / (256 * √(n : ℝ))) + 1 / 131072) := by
  have hs := sqrt_cast_pos (n := n)
  have hs0 := hs.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hss : √(n : ℝ) ^ 2 = n := sq_sqrt (Nat.cast_nonneg n)
  have hpt (r : Round n) :
      gapPot (step y r) ≤ exp (-(1 / (256 * √(n : ℝ)) * gapR (step y r))) := by
    rw [gapPot, exp_le_exp, neg_le_neg_iff, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  calc avg (fun r : Round n => gapPot (step y r))
      ≤ avg (fun r : Round n => exp (-(1 / (256 * √(n : ℝ)) * gapR (step y r)))) :=
        avg_le_avg hpt
    _ ≤ exp (-(1 / (256 * √(n : ℝ)) * meanGap y) + n * (1 / (256 * √(n : ℝ))) ^ 2 / 2) :=
        avg_exp_neg_gapR_step y _
    _ = exp (-(meanGap y / (256 * √(n : ℝ))) + 1 / 131072) := by
        congr 1
        rw [div_pow, mul_pow, hss]
        field_simp
        ring

/-- **Far from balance** (`√n/64 ≤ g ≤ n/2`), one round contracts the expected potential by
`e^{-1/65536}`: the mean gap is at least `11g/8`, and the excess `3g/8` beats the Hoeffding
error `1/131072`. -/
lemma avg_gapPot_step_far (y : Config n Bool) (hg1 : √(n : ℝ) / 64 ≤ gapR y)
    (hg2 : gapR y ≤ n / 2) :
    avg (fun r : Round n => gapPot (step y r)) ≤ exp (-(1 / 65536)) * gapPot y := by
  have hs := sqrt_cast_pos (n := n)
  have hg0 : 0 ≤ gapR y := le_trans (by positivity) hg1
  have hd : 0 < 256 * √(n : ℝ) := by positivity
  have h1 : 11 / 8 * (gapR y / (256 * √(n : ℝ))) ≤ meanGap y / (256 * √(n : ℝ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (meanGap_ge y hg0 hg2) hd.le
  have h2 : 1 / 16384 ≤ gapR y / (256 * √(n : ℝ)) := by
    rw [le_div_iff₀ hd]
    linarith
  refine (avg_gapPot_step_le y).trans ?_
  rw [gapPot, ← exp_add, abs_of_nonneg hg0, exp_le_exp]
  linarith

/-- **Beyond `g > n/2`**, the expected potential after one round is at most
`e^{1/131072 - √n/512}`, since the mean gap stays above `n/2`. -/
lemma avg_gapPot_step_huge (y : Config n Bool) (hg : (n : ℝ) / 2 < gapR y) :
    avg (fun r : Round n => gapPot (step y r)) ≤ exp (1 / 131072 - √(n : ℝ) / 512) := by
  have hs := sqrt_cast_pos (n := n)
  have hss : √(n : ℝ) * √(n : ℝ) = n := mul_self_sqrt (Nat.cast_nonneg n)
  have hg0 : 0 ≤ gapR y := le_trans (by positivity) hg.le
  have hE := gapR_le_meanGap y hg0
  have h1 : √(n : ℝ) / 512 ≤ meanGap y / (256 * √(n : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine (avg_gapPot_step_le y).trans (exp_le_exp.mpr ?_)
  linarith

/-! ### Near balance: anti-concentration -/

/-- **Symmetry breaking near balance** (`|g| ≤ √n/64`, `n ≥ 10`): the next gap has variance
`σ² ≥ n/10`; with probability at least `9/64` its centered part `2S` satisfies `σ² ≤ 4S²`
(Paley-Zygmund), and then `|g'| ≥ √n/4`, where the potential is at most `e^{-1/1024}`. -/
lemma avg_gapPot_step_near_le (hn : (10 : ℝ) ≤ n) (y : Config n Bool)
    (hg : |gapR y| ≤ √(n : ℝ) / 64) :
    avg (fun r : Round n => gapPot (step y r)) ≤ 1 - 9 / 64 * (1 - exp (-(1 / 1024))) := by
  have hs := sqrt_cast_pos (n := n)
  have hss : √(n : ℝ) ^ 2 = n := sq_sqrt (Nat.cast_nonneg n)
  have hsn : √(n : ℝ) ≤ n := (sqrt_le_left (by positivity)).mpr (by nlinarith)
  -- the variance `σ²` of the next gap is at least `n/10`
  obtain ⟨σ2, hσ2⟩ : ∃ σ2, σ2 = ∑ v, variance (coord y v) := ⟨_, rfl⟩
  have hσ : (n : ℝ) / 10 ≤ σ2 := by
    have h := sum_le_sum fun v (_ : v ∈ univ) => one_tenth_le_variance_coord y (by linarith) v
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← hσ2] at h
    linarith
  -- Paley-Zygmund: the event `A = {σ² ≤ 4 S²}` has probability at least `9/64`
  obtain ⟨A, hA⟩ : ∃ A : Round n → ℝ, A = fun r =>
      if σ2 ≤ 4 * (∑ v, (coord y v (r v) - avg (coord y v))) ^ 2 then 1 else 0 := ⟨_, rfl⟩
  have hpz : 9 / 64 ≤ avg A := by
    rw [hA, hσ2]
    exact avg_pz_zero_one (coord y) (coord_zero_one y) (by linarith)
  -- on `A`, `|g'| ≥ √n/4` and the potential is at most `e^{-1/1024}`
  have hpt (r : Round n) : gapPot (step y r) ≤ 1 - (1 - exp (-(1 / 1024))) * A r := by
    simp only [hA]
    split_ifs with h
    · rw [mul_one, sub_sub_cancel]
      refine gapPot_le_exp_neg ?_
      have hZ : √(n : ℝ) ^ 2 / 10 ≤ 4 * (∑ v, (coord y v (r v) - avg (coord y v))) ^ 2 := by
        rw [hss]
        linarith
      have hm : |meanGap y| ≤ 3 / 128 * √(n : ℝ) := (abs_meanGap_le y).trans (by linarith)
      have := le_abs_two_mul_add hZ hm
      rw [gapR_step_eq]
      linarith
    · rw [mul_zero, sub_zero]
      exact gapPot_le_one _
  have hc : 0 ≤ 1 - exp (-(1 / 1024 : ℝ)) := by
    rw [sub_nonneg, exp_le_one_iff]
    norm_num
  calc avg (fun r : Round n => gapPot (step y r))
      ≤ avg (fun r => 1 - (1 - exp (-(1 / 1024))) * A r) := avg_le_avg hpt
    _ = 1 - (1 - exp (-(1 / 1024))) * avg A := by rw [avg_sub, avg_const, avg_const_mul]
    _ ≤ 1 - 9 / 64 * (1 - exp (-(1 / 1024))) := by
        have := mul_le_mul_of_nonneg_left hpz hc
        linarith

/-- Near balance (`|g| ≤ √n/64`, `n ≥ 10`) one round contracts the expected potential by
`e^{-1/65536}`: it drops to `1 - (9/64)(1 - e^{-1/1024}) ≤ e^{-5/65536}`, while the potential
itself is at least `e^{-1/16384}`. -/
lemma avg_gapPot_step_near (hn : (10 : ℝ) ≤ n) (y : Config n Bool)
    (hg : |gapR y| ≤ √(n : ℝ) / 64) :
    avg (fun r : Round n => gapPot (step y r)) ≤ exp (-(1 / 65536)) * gapPot y :=
  calc avg (fun r : Round n => gapPot (step y r)) ≤ 1 - 9 / 64 * (1 - exp (-(1 / 1024))) :=
        avg_gapPot_step_near_le hn y hg
    _ ≤ exp (-(5 / 65536)) := near_const_le
    _ = exp (-(1 / 65536)) * exp (-(1 / 16384)) := by rw [← exp_add]; norm_num
    _ ≤ exp (-(1 / 65536)) * gapPot y :=
        mul_le_mul_of_nonneg_left (exp_neg_le_gapPot (by linarith)) (exp_pos _).le

/-! ### The one-round drift -/

/-- **One-round drift of the potential.** For `n ≥ 10`, one round contracts the expected
potential by `e^{-1/65536}`, up to the additive error `e^{1/131072 - √n/512}`. -/
theorem avg_gapPot_step (hn : (10 : ℝ) ≤ n) (y : Config n Bool) :
    avg (fun r : Round n => gapPot (step y r))
      ≤ exp (-(1 / 65536)) * gapPot y + exp (1 / 131072 - √(n : ℝ) / 512) := by
  -- by the flip symmetry, assume `g ≥ 0`
  wlog hg : 0 ≤ gapR y generalizing y
  · simpa only [step_flip, gapPot_flip] using this (fun v => !y v) (by rw [gapR_flip]; linarith)
  have hε : 0 ≤ exp (1 / 131072 - √(n : ℝ) / 512) := (exp_pos _).le
  rcases le_or_gt (gapR y) (√(n : ℝ) / 64) with h1 | h1
  · exact (avg_gapPot_step_near hn y (by rwa [abs_of_nonneg hg])).trans
      (le_add_of_nonneg_right hε)
  rcases le_or_gt (gapR y) (n / 2) with h2 | h2
  · exact (avg_gapPot_step_far y h1.le h2).trans (le_add_of_nonneg_right hε)
  · exact (avg_gapPot_step_huge y h2).trans
      (le_add_of_nonneg_left (mul_nonneg (exp_pos _).le (gapPot_pos y).le))

end Median
