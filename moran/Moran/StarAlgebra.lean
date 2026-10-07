import Mathlib.Analysis.SpecificLimits.Basic
import Moran.StarDefs

/-! # Real-number facts about the star formulas (MOR-3)

Pure algebra and analysis on the ratio `q = starRatio n r` and the centre weight
`κ = starCentreWeight n r`, with no reference to the Moran process:

* signs: `q, κ > 0`; `q ≤ 1`, `κ < 1` for `r > 1` and the reverse for `r < 1`; `κ q ^ n ≠ 1`;
* the amplifier inequality (`star_amplifier_sign`): with `s = 1/r`, the uniform-start closed
  form minus Moran's `(1 - s)/(1 - s^(n+1))` has the sign of `1 - s`, for every `n ≥ 2`. The
  proof reduces it to `s^(n-1) (1 - s)(1 + n s) < 1 - s^(n+1)` (`geom_gap_pos`), whose slack is
  `∑_{k ≤ n-2} (1 - s)(s^k - s^n) > 0` on both sides of `s = 1`, through Bernoulli's inequality
  for `t = (1 + n s)/(n + s)`, where `q = s t` and `κ = s / t`;
* the closed form equals the geometric-sum formula of Broom–Rychtář (`star_closed_eq_sum`), and
  that formula is `1/(n+1)` at `r = 1` (`star_sum_neutral`);
* the closed form tends to `1 - 1/r^2` as `n → ∞` for `r > 1` (`star_closed_tendsto`).
-/

namespace Moran
open Finset Filter Topology

/-! ### The star ratio and centre weight -/

/-- `q > 0`. -/
lemma starRatio_pos (n : ℕ) {r : ℝ} (hr : 0 < r) : 0 < starRatio n r := by
  unfold starRatio
  positivity

/-- `κ > 0`. -/
lemma starCentreWeight_pos (n : ℕ) {r : ℝ} (hr : 0 < r) : 0 < starCentreWeight n r := by
  unfold starCentreWeight
  positivity

/-- For `r ≥ 1`, `q ≤ 1`. -/
lemma starRatio_le_one (n : ℕ) {r : ℝ} (hr : 1 ≤ r) : starRatio n r ≤ 1 := by
  unfold starRatio
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_one (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hn (sub_nonneg.mpr hr)) (by linarith : (0 : ℝ) ≤ r + 1)]

/-- For `r ≤ 1`, `q ≥ 1`. -/
lemma one_le_starRatio (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1) : 1 ≤ starRatio n r := by
  unfold starRatio
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [one_le_div (by positivity)]
  nlinarith [mul_nonneg hn (mul_nonneg hr0.le (sub_nonneg.mpr hr))]

/-- For `r > 1`, `κ < 1`. -/
lemma starCentreWeight_lt_one (n : ℕ) {r : ℝ} (hr : 1 < r) : starCentreWeight n r < 1 := by
  unfold starCentreWeight
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_lt_one (by positivity)]
  nlinarith

/-- For `r < 1`, `κ > 1`. -/
lemma one_lt_starCentreWeight (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    1 < starCentreWeight n r := by
  unfold starCentreWeight
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [one_lt_div (by positivity)]
  nlinarith

/-- For `r ≠ 1`, `κ q ^ n ≠ 1`: the denominator of the fixation probabilities is nonzero. -/
lemma star_denom_ne_zero (n : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    1 - starCentreWeight n r * starRatio n r ^ n ≠ 0 := by
  have hq := starRatio_pos n hr
  have hk := starCentreWeight_pos n hr
  rcases hr1.lt_or_gt with h | h
  · have h1 : 1 ≤ starRatio n r ^ n := one_le_pow₀ (one_le_starRatio n hr h.le)
    have h2 := one_lt_starCentreWeight n hr h
    nlinarith
  · have h1 : starRatio n r ^ n ≤ 1 := pow_le_one₀ hq.le (starRatio_le_one n h.le)
    have h2 := starCentreWeight_lt_one n h
    have h3 : 0 ≤ starRatio n r ^ n := pow_nonneg hq.le n
    nlinarith

/-! ### The amplifier inequality -/

/-- `s^(m+1) (1 - s)(1 + (m+2) s) < 1 - s^(m+3)` for every `s > 0`, `s ≠ 1`: the slack is
`∑_{k ≤ m} (1 - s)(s^k - s^(m+2))`, a sum of positive terms. -/
lemma geom_gap_pos (m : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    s ^ (m + 1) * (1 - s) * (1 + (m + 2) * s) < 1 - s ^ (m + 3) := by
  have hterm : ∀ k ∈ range (m + 1), 0 < (1 - s) * (s ^ k - s ^ (m + 2)) := by
    intro k hk
    have hk : k < m + 2 := by rw [mem_range] at hk; omega
    rcases hs1.lt_or_gt with h | h
    · exact mul_pos (by linarith) (sub_pos.mpr (pow_lt_pow_right_of_lt_one₀ hs h hk))
    · exact mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr (pow_lt_pow_right₀ h hk))
  have hsum := sum_pos hterm ⟨0, mem_range.mpr (Nat.succ_pos m)⟩
  have hgeom : (1 - s) * ∑ k ∈ range (m + 1), s ^ k = 1 - s ^ (m + 1) := by
    rw [mul_comm, geom_sum_mul_neg]
  rw [← mul_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sub, hgeom] at hsum
  have h3 : s ^ (m + 3) = s ^ (m + 1) * s ^ 2 := by rw [← pow_add]
  have h2 : s ^ (m + 2) = s ^ (m + 1) * s := by rw [← pow_succ]
  rw [h2] at hsum
  rw [h3]
  push_cast at hsum
  nlinarith [hsum]

/-- The key inequality: with `t = (1 + (m+2) s)/((m+2) + s)`,
`s^(m+3) (1 - t^(m+1)) < s^2 (m+1)^2 / ((m+2+s)(1+(m+2)s)) · (1 - s^(m+3))`
for every `s > 0`, `s ≠ 1`. -/
lemma star_delta_pos (m : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    s ^ (m + 3) * (1 - ((1 + (m + 2) * s) / (m + 2 + s)) ^ (m + 1)) <
      s ^ 2 * (m + 1) ^ 2 / ((m + 2 + s) * (1 + (m + 2) * s)) * (1 - s ^ (m + 3)) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA : 0 < (m : ℝ) + 2 + s := by positivity
  have hB : 0 < 1 + ((m : ℝ) + 2) * s := by positivity
  set t := (1 + (m + 2) * s) / (m + 2 + s) with ht
  have ht0 : 0 ≤ t := by positivity
  -- Bernoulli: `1 - t^(m+1) ≤ (m+1)(1 - t)`
  have hbern : 1 - t ^ (m + 1) ≤ (m + 1) * (1 - t) := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ t - 1 by linarith) (m + 1)
    rw [add_sub_cancel] at h
    push_cast at h
    linarith
  have h1t : 1 - t = (m + 1) * (1 - s) / (m + 2 + s) := by
    rw [ht]
    field_simp
    ring
  have hK := geom_gap_pos m hs hs1
  have hc : 0 < s ^ 2 * (m + 1) ^ 2 / ((m + 2 + s) * (1 + (m + 2) * s)) := by positivity
  have hlt := mul_lt_mul_of_pos_left hK hc
  have hs3 : 0 ≤ s ^ (m + 3) := by positivity
  calc s ^ (m + 3) * (1 - t ^ (m + 1)) ≤ s ^ (m + 3) * ((m + 1) * (1 - t)) :=
        mul_le_mul_of_nonneg_left hbern hs3
    _ = s ^ 2 * (m + 1) ^ 2 / ((m + 2 + s) * (1 + (m + 2) * s)) *
          (s ^ (m + 1) * (1 - s) * (1 + (m + 2) * s)) := by
        rw [h1t]
        field_simp
        ring
    _ < _ := hlt

/-- **The amplifier inequality**, both directions at once. For `n ≥ 2` and `r > 0`, `r ≠ 1`, the
uniform-start closed form on the star minus Moran's `(1 - 1/r)/(1 - (1/r)^(n+1))` has the sign of
`1 - 1/r`, i.e. of `r - 1`. -/
lemma star_amplifier_sign {n : ℕ} (hn2 : 2 ≤ n) {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < (1 - 1 / r) * ((n * (1 - starRatio n r) + (1 - starCentreWeight n r)) /
        ((n + 1) * (1 - starCentreWeight n r * starRatio n r ^ n)) -
      (1 - 1 / r) / (1 - (1 / r) ^ (n + 1))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn2
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ r = 1 / s := ⟨1 / r, by positivity, by rw [one_div_one_div]⟩
  have hs1 : s ≠ 1 := fun h => hr1 (by rw [h, div_one])
  rw [one_div_one_div]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA : 0 < (m : ℝ) + 2 + s := by positivity
  have hB : 0 < 1 + ((m : ℝ) + 2) * s := by positivity
  set t := (1 + (m + 2) * s) / (m + 2 + s) with ht
  have ht0 : 0 < t := by positivity
  have hq : starRatio (m + 2) (1 / s) = s * t := by
    rw [ht]; unfold starRatio; push_cast; field_simp; ring
  have hk : starCentreWeight (m + 2) (1 / s) = s / t := by
    rw [ht]; unfold starCentreWeight; push_cast; field_simp; ring
  have hkq : starCentreWeight (m + 2) (1 / s) * starRatio (m + 2) (1 / s) ^ (m + 2) =
      s ^ (m + 3) * t ^ (m + 1) := by
    rw [hq, hk, mul_pow]
    field_simp
    ring
  set E := s ^ 2 * (m + 1) ^ 2 / ((m + 2 + s) * (1 + (m + 2) * s)) with hE
  have hnum : ((m + 2 : ℕ) : ℝ) * (1 - starRatio (m + 2) (1 / s)) +
      (1 - starCentreWeight (m + 2) (1 / s)) = (1 - s) * (((m + 2 : ℕ) : ℝ) + 1) * (1 + E) := by
    rw [hq, hk, hE, ht]
    push_cast
    field_simp
    ring
  rw [hnum, hkq]
  set S := s ^ (m + 2 + 1) with hS
  set T := t ^ (m + 1) with hT
  have hS3 : s ^ (m + 3) = S := by rw [hS]
  have hΔ : 0 < E * (1 - S) - S * (1 - T) := by
    have h := star_delta_pos m hs hs1
    rw [← ht, ← hE, hS3] at h
    linarith
  -- signs of `1 - S` and `D = 1 - S T` agree
  have hDS : 0 < (1 - S * T) * (1 - S) := by
    rcases hs1.lt_or_gt with h | h
    · have hS1 : S < 1 := by rw [hS]; exact pow_lt_one₀ hs.le h (by omega)
      have ht1 : t ≤ 1 := by
        rw [ht, div_le_one hA]; nlinarith
      have hT1 : T ≤ 1 := by rw [hT]; exact pow_le_one₀ ht0.le ht1
      have hS0 : 0 ≤ S := by rw [hS]; positivity
      exact mul_pos (by nlinarith) (by linarith)
    · have hS1 : 1 < S := by rw [hS]; exact one_lt_pow₀ h (by omega)
      have ht1 : 1 ≤ t := by
        rw [ht, one_le_div hA]; nlinarith
      have hT1 : 1 ≤ T := by rw [hT]; exact one_le_pow₀ ht1
      exact mul_pos_of_neg_of_neg (by nlinarith) (by linarith)
  have hD : 1 - S * T ≠ 0 := fun h => by rw [h, zero_mul] at hDS; exact lt_irrefl 0 hDS
  have hS1 : 1 - S ≠ 0 := fun h => by rw [h, mul_zero] at hDS; exact lt_irrefl 0 hDS
  have hN : ((m + 2 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have hform : (1 - s) * ((1 - s) * (((m + 2 : ℕ) : ℝ) + 1) * (1 + E) /
      ((((m + 2 : ℕ) : ℝ) + 1) * (1 - S * T)) - (1 - s) / (1 - S)) =
      (1 - s) ^ 2 * (E * (1 - S) - S * (1 - T)) / ((1 - S * T) * (1 - S)) := by
    field_simp
    ring
  rw [hform]
  have hs0 : 0 < (1 - s) ^ 2 := by
    have : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    positivity
  positivity

/-! ### The formula of Broom and Rychtář -/

/-- For `n ≥ 1` and `r ≠ 1`, `q ≠ 1`. -/
lemma starRatio_ne_one {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    starRatio n r ≠ 1 := by
  unfold starRatio
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Ne, div_eq_one_iff_eq (by positivity)]
  intro h
  have h2 : (n : ℝ) * (r ^ 2 - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · have : (r - 1) * (r + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h4 | h4
    · exact hr1 (by linarith)
    · linarith

/-- **The closed form is the formula of Broom and Rychtář** (2008, §5): for `n ≥ 1`, `r > 0`,
`r ≠ 1`, `(n (1 - q) + (1 - κ)) / ((n + 1)(1 - κ q^n))` equals
`(n · n r/(n r + 1) + r/(r + n)) / ((n + 1)(1 + n/(n + r) · ∑_{j=1}^{n-1} q ^ j))`. -/
lemma star_closed_eq_sum {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    (n * (1 - starRatio n r) + (1 - starCentreWeight n r)) /
        ((n + 1) * (1 - starCentreWeight n r * starRatio n r ^ n)) =
      (n * (n * r / (n * r + 1)) + r / (r + n)) /
        ((n + 1) * (1 + n / (n + r) * ∑ j ∈ Ico 1 n, ((n + r) / (r * (n * r + 1))) ^ j)) := by
  have hq1 := starRatio_ne_one hn hr hr1
  have hD := star_denom_ne_zero n hr hr1
  have hr2 : r ^ 2 - 1 ≠ 0 := by
    intro h
    have : (r - 1) * (r + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h4 | h4
    · exact hr1 (by linarith)
    · linarith
  have hgeom := geom_sum_Ico_mul (starRatio n r) hn
  have hsum : ∑ j ∈ Ico 1 n, ((n + r) / (r * (n * r + 1)) : ℝ) ^ j =
      (starRatio n r ^ n - starRatio n r) / (starRatio n r - 1) := by
    show ∑ j ∈ Ico 1 n, starRatio n r ^ j = _
    rw [eq_div_iff (sub_ne_zero.mpr hq1), hgeom, pow_one]
  have hBR : 1 + n / (n + r) * ∑ j ∈ Ico 1 n, ((n + r) / (r * (n * r + 1)) : ℝ) ^ j =
      r ^ 2 * (1 - starCentreWeight n r * starRatio n r ^ n) / (r ^ 2 - 1) := by
    rw [hsum]
    generalize starRatio n r ^ n = X
    have h1 : (n : ℝ) * r + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + r ≠ 0 := by positivity
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hq1e : starRatio n r - 1 = -(n * (r ^ 2 - 1)) / (r * (n * r + 1)) := by
      unfold starRatio
      field_simp
      ring
    rw [hq1e]
    unfold starRatio starCentreWeight
    rw [eq_div_iff hr2]
    field_simp
    ring
  rw [hBR]
  generalize hY : starCentreWeight n r * starRatio n r ^ n = Y at *
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h1 : (n : ℝ) * r + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + r ≠ 0 := by positivity
  have h3 : r + (n : ℝ) ≠ 0 := by positivity
  unfold starRatio starCentreWeight
  field_simp
  ring

/-- **The formula of Broom and Rychtář at `r = 1`** is `1/(n+1)`, for `n ≥ 1`. -/
lemma star_sum_neutral {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) * (n * 1 / (n * 1 + 1)) + 1 / (1 + n)) /
        ((n + 1) * (1 + n / (n + 1) * ∑ j ∈ Ico 1 n, ((n + 1) / (1 * (n * 1 + 1)) : ℝ) ^ j)) =
      1 / (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hn1 : ((m + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have hq : (((m + 1 : ℕ) : ℝ) + 1) / (1 * (((m + 1 : ℕ) : ℝ) * 1 + 1)) = 1 := by
    rw [mul_one, one_mul, div_self hn1]
  rw [hq]
  simp only [one_pow, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ) + 1 + 1 ≠ 0 := by positivity
  have h2 : 1 + ((m : ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((m : ℝ) + 1) ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ### Large stars -/

/-- For `n ≥ 1` and `r ≥ 1`, `q ≤ 1/r`. -/
lemma starRatio_le_inv {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 1 ≤ r) : starRatio n r ≤ 1 / r := by
  unfold starRatio
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : 0 < r := by linarith
  rw [div_le_div_iff₀ (by positivity) hr0]
  nlinarith [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hr)]

/-- **Large stars amplify `r` to `r ^ 2`.** For `r > 1`, the uniform-start closed form tends to
`1 - 1/r^2` as `n → ∞`. -/
lemma star_closed_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => (n * (1 - starRatio n r) + (1 - starCentreWeight n r)) /
        ((n + 1) * (1 - starCentreWeight n r * starRatio n r ^ n))) atTop
      (𝓝 (1 - 1 / r ^ 2)) := by
  have hr0 : 0 < r := by linarith
  -- rewrite as `(a n + b n) / d n`
  have hform : ∀ n : ℕ, (n * (1 - starRatio n r) + (1 - starCentreWeight n r)) /
      ((n + 1) * (1 - starCentreWeight n r * starRatio n r ^ n)) =
      ((n / (n + 1)) * (n / (n + 1 / r)) * (1 - 1 / r ^ 2) + (1 - starCentreWeight n r) / (n + 1)) /
        (1 - starCentreWeight n r * starRatio n r ^ n) := by
    intro n
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hnr : (n : ℝ) + 1 / r ≠ 0 := by positivity
    have hnr' : (n : ℝ) * r + 1 ≠ 0 := by positivity
    have key : (n : ℝ) * (1 - starRatio n r) =
        (n + 1) * ((n / (n + 1)) * (n / (n + 1 / r)) * (1 - 1 / r ^ 2)) := by
      unfold starRatio
      field_simp
      ring
    rw [key, ← div_div, add_div, mul_div_cancel_left₀ _ hn1]
  simp_rw [hform]
  have ha : Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1)) * (n / (n + 1 / r)) * (1 - 1 / r ^ 2))
      atTop (𝓝 (1 - 1 / r ^ 2)) := by
    have h := ((tendsto_natCast_div_add_atTop (1 : ℝ)).mul
      (tendsto_natCast_div_add_atTop (1 / r))).mul_const (1 - 1 / r ^ 2)
    simpa using h
  have hb : Tendsto (fun n : ℕ => (1 - starCentreWeight n r) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    · exact div_nonneg (by linarith [starCentreWeight_lt_one n hr]) (by positivity)
    · exact div_le_div_of_nonneg_right (by linarith [starCentreWeight_pos n hr0]) (by positivity)
  have hd : Tendsto (fun n : ℕ => 1 - starCentreWeight n r * starRatio n r ^ n) atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ => starCentreWeight n r * starRatio n r ^ n) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / r)
          ((div_lt_one hr0).mpr hr))
      · exact mul_nonneg (starCentreWeight_pos n hr0).le (pow_nonneg (starRatio_pos n hr0).le n)
      · filter_upwards [eventually_ge_atTop 1] with n hn
        calc starCentreWeight n r * starRatio n r ^ n ≤ 1 * starRatio n r ^ n :=
              mul_le_mul_of_nonneg_right (starCentreWeight_lt_one n hr).le
                (pow_nonneg (starRatio_pos n hr0).le n)
          _ ≤ (1 / r) ^ n := by
              rw [one_mul]
              exact pow_le_pow_left₀ (starRatio_pos n hr0).le (starRatio_le_inv hn hr.le) n
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  have h := (ha.add hb).div hd one_ne_zero
  rw [add_zero, div_one] at h
  exact h

end Moran
