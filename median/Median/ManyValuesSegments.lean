import Median.BinaryAssembly
import Median.ManyValuesFast
import Median.ManyValuesKernel
import Median.ManyValuesScalar

/-! # Many values: the four segments of fast binary consensus

`binary_consensus_fast` (in `Median/ManyValues.lean`) runs the binary median dynamics through
four segments. Each segment is a chain of one-round moves with failure `n⁻²` per round
(`Dynamics.Kernel.event_chain`); the segments are composed by the Markov property
(`Dynamics.Kernel.event_comp`). With `β = 512 log n`:

1. **Growth** (`growth_segment`): from a gap `Δ ≥ 128 √(n log n)`, the gap grows by `5/4` per
   round (`growth_move`); after `T₁ ≤ 5 log (n/Δ) + 2` rounds (`exists_growth_rounds`) the
   minority is below `n/4`.
2. **Linear saturation** (`linear_sat_segment`): six rounds of `sat_move` (`m ↦ (7/8) m`) bring
   the minority from `n/4` to `n/8`.
3. **Quadratic saturation** (`quad_sat_segment`): the thresholds `q_j = (n/4) (1/2)^(2^j)`
   satisfy `4 q_j²/n = q_(j+1)` (`quad_move`), so `T₃ ≤ 2 log log n + 3` rounds
   (`exists_quad_rounds`) bring the minority from `n/8` to `β`.
4. **Consensus** (`consensus_segment`): two nested phases of four rounds
   (`Dynamics.Kernel.nested_phases`, `mono_move`) reach consensus from `m < β`.
-/

namespace Median

open Finset Real Dynamics

variable {n : ℕ} [NeZero n]

/-! ### Numerics for `log n ≥ 128` -/

omit [NeZero n] in
/-- `β = 512 log n` is at most `n/8` once `log n ≥ 128`. -/
lemma beta_le_n_div_eight (hL : (128 : ℝ) ≤ log n) : 512 * log n ≤ (n : ℝ) / 8 := by
  have hbig := big_log_le hL
  have h1 : (4096 : ℝ) * log n ≤ 2 ^ 20 * log n :=
    mul_le_mul_of_nonneg_right (by norm_num) (by linarith only [hL])
  linarith only [hbig, h1]

omit [NeZero n] in
/-- A gap threshold `Δ ≥ 128 √(n log n)` is at least `1`. -/
lemma one_le_of_sqrt_le (hL : (128 : ℝ) ≤ log n) {Δ : ℝ}
    (hΔ : 128 * √((n : ℝ) * log n) ≤ Δ) : 1 ≤ Δ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast one_le_of_log_pos (by linarith only [hL])
  have h1 : (1 : ℝ) ≤ √((n : ℝ) * log n) := by
    refine Real.one_le_sqrt.mpr ?_
    have p := mul_le_mul hn1 hL (by norm_num) (by linarith only [hn1])
    linarith only [p]
  linarith only [h1, hΔ]

omit [NeZero n] in
/-- **Round count of the growth phase.** Growing by `5/4` per round, the gap threshold passes
`n` from `Δ ≤ n` within `T₁ ≤ 5 log (n/Δ) + 2` rounds. -/
lemma exists_growth_rounds {Δ : ℝ} (hΔ : 0 < Δ) (hΔn : Δ ≤ n) :
    ∃ T : ℕ, (n : ℝ) < (5 / 4 : ℝ) ^ T * Δ ∧ (T : ℝ) ≤ 5 * log (n / Δ) + 2 := by
  obtain ⟨T, hT, hTb⟩ := exists_lt_pow_mul (by norm_num : (1 : ℝ) < 5 / 4) hΔ hΔn
  refine ⟨T, hT, hTb.trans ?_⟩
  have hw0 : 0 ≤ log (n / Δ) := log_nonneg ((one_le_div hΔ).mpr hΔn)
  have hq := log_five_fourth_ge
  have h : log (n / Δ) / log (5 / 4 : ℝ) ≤ 5 * log (n / Δ) := by
    rw [div_le_iff₀ (by linarith only [hq])]
    have p := mul_le_mul_of_nonneg_left hq hw0
    linarith only [p]
  linarith only [h]

omit [NeZero n] in
/-- **Round count of the quadratic saturation phase.** After `T₃ ≤ 2 log log n + 3` squarings,
the threshold `q_T₃ = (n/4) (1/2)^(2^T₃)` is below `β = 512 log n`. -/
lemma exists_quad_rounds (hL : (128 : ℝ) ≤ log n) :
    ∃ T : ℕ, (n : ℝ) / 4 * (1 / 2 : ℝ) ^ 2 ^ T ≤ 512 * log n
      ∧ (T : ℝ) ≤ 2 * log (log n) + 3 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast two_le_of_log hL
  obtain ⟨T, hT, hTb⟩ := exists_le_two_pow_two_pow hn2
  exact ⟨T, (quad_threshold_small (by linarith only [hn2]) hT).trans (by linarith only [hL]),
    hTb⟩

/-! ### The segments -/

/-- **Growth segment.** From a gap of at least `Δ ≥ 128 √(n log n)`, the gap threshold
`(5/4)^i Δ` grows by `5/4` per round (`growth_move`), and once it exceeds `n` the minority is
below `n/4`: after `T` rounds with `n < (5/4)^T Δ`, the minority is below `n/4` except with
probability `T n⁻²`. -/
lemma growth_segment (hL : (128 : ℝ) ≤ log n) {Δ : ℝ} (hΔ : 128 * √((n : ℝ) * log n) ≤ Δ)
    {T : ℕ} (hT : (n : ℝ) < (5 / 4 : ℝ) ^ T * Δ) {x : Config n Bool} (hx : Δ ≤ gapR x) :
    1 - T * (1 / (n : ℝ) ^ 2)
      ≤ (Median.kernel n Bool).event (· ∈ satSet n ((n : ℝ) / 4)) T x := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hL0 : 0 ≤ log n := by linarith only [hL]
  have hΔ0 : 0 ≤ Δ := le_trans (by positivity) hΔ
  have hΔ2 : 16384 * (n : ℝ) * log n ≤ Δ ^ 2 := by
    have h1 : (128 * √((n : ℝ) * log n)) ^ 2 = 16384 * (n : ℝ) * log n := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hn0.le hL0)]
      ring
    rw [← h1]
    exact pow_le_pow_left₀ (by positivity) hΔ 2
  have hmove : ∀ i, ∀ a ∈ growthSet n ((5 / 4 : ℝ) ^ i * Δ),
      1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob
        (· ∈ growthSet n ((5 / 4 : ℝ) ^ (i + 1) * Δ)) := by
    intro i a ha
    have hG0 : 0 ≤ (5 / 4 : ℝ) ^ i * Δ := mul_nonneg (by positivity) hΔ0
    have hG2 : 16384 * (n : ℝ) * log n ≤ ((5 / 4 : ℝ) ^ i * Δ) ^ 2 :=
      hΔ2.trans (pow_le_pow_left₀ hΔ0 (le_mul_of_one_le_left hΔ0 (one_le_pow₀ (by norm_num))) 2)
    have e : (5 / 4 : ℝ) ^ (i + 1) * Δ = 5 / 4 * ((5 / 4 : ℝ) ^ i * Δ) := by ring
    rw [e]
    exact growth_move hL hG0 hG2 ha
  have hx0 : x ∈ growthSet n ((5 / 4 : ℝ) ^ 0 * Δ) := by
    rw [pow_zero, one_mul]
    exact mem_growthSet.mpr (Or.inr hx)
  exact ((Median.kernel n Bool).event_chain (by positivity) T _ hmove x hx0).trans
    ((Median.kernel n Bool).event_mono_set (growthSet_sub_satSet n hT) T x)

/-- **Linear saturation segment.** From a minority below `n/4`, six rounds of `sat_move`
(`m ↦ (7/8) m`, and `(7/8)^6 ≤ 1/2`) bring it below `n/8` except with probability `6 n⁻²`. -/
lemma linear_sat_segment (hL : (128 : ℝ) ≤ log n) {y : Config n Bool}
    (hy : falsesR y < (n : ℝ) / 4) :
    1 - 6 * (1 / (n : ℝ) ^ 2)
      ≤ (Median.kernel n Bool).event (· ∈ satSet n ((n : ℝ) / 8)) 6 y := by
  have hβ0 : (0 : ℝ) ≤ 512 * log n := by linarith only [hL]
  have hβn8 := beta_le_n_div_eight hL
  have hmove : ∀ j, ∀ a ∈ satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ j) (512 * log n)),
      1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob
        (· ∈ satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ (j + 1)) (512 * log n))) := by
    intro j a ha
    have ht0 : 0 ≤ max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ j) (512 * log n) :=
      le_trans hβ0 (le_max_right _ _)
    have htn : max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ j) (512 * log n) ≤ (n : ℝ) / 4 :=
      max_le (mul_le_left_of_le_one (by positivity)
        (pow_le_one₀ (by norm_num) (by norm_num))) (by linarith only [hβn8, hβ0])
    exact le_trans (sat_move hL ht0 htn ha)
      (prob_mono_set' _ (satSet_sub n (sat_threshold_step _ _ hβ0 j)))
  have hy0 : y ∈ satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ 0) (512 * log n)) := by
    rw [pow_zero, mul_one]
    exact lt_of_lt_of_le hy (le_max_left _ _)
  have hsub : satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ 6) (512 * log n))
      ⊆ satSet n ((n : ℝ) / 8) := by
    apply satSet_sub
    refine max_le ?_ hβn8
    have h1 : (7 / 8 : ℝ) ^ 6 ≤ 1 / 2 := by norm_num
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (n : ℝ) / 4 by positivity)
    linarith only [h2]
  have h := ((Median.kernel n Bool).event_chain (by positivity) 6 _ hmove y hy0).trans
    ((Median.kernel n Bool).event_mono_set hsub 6 y)
  push_cast at h
  exact h

/-- **Quadratic saturation segment.** From a minority below `n/8`, the minority follows the
thresholds `q_j = (n/4) (1/2)^(2^j)` floored at `β = 512 log n`, one round per threshold
(`quad_move`, `4 q_j²/n = q_(j+1)`): after `T` rounds with `q_T ≤ β` it is below `β` except
with probability `T n⁻²`. -/
lemma quad_sat_segment (hL : (128 : ℝ) ≤ log n) {T : ℕ}
    (hT : (n : ℝ) / 4 * (1 / 2 : ℝ) ^ 2 ^ T ≤ 512 * log n) {y : Config n Bool}
    (hy : falsesR y < (n : ℝ) / 8) :
    1 - T * (1 / (n : ℝ) ^ 2)
      ≤ (Median.kernel n Bool).event (· ∈ satSet n (512 * log n)) T y := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hβ0 : (0 : ℝ) ≤ 512 * log n := by linarith only [hL]
  have hβn4 : 4 * (512 * log n) ≤ (n : ℝ) := by linarith only [beta_le_n_div_eight hL, hβ0]
  have hmove : ∀ j, ∀ a ∈ satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ 2 ^ j) (512 * log n)),
      1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob
        (· ∈ satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ 2 ^ (j + 1)) (512 * log n))) := by
    intro j a ha
    have hstep := max_sq_div_le (q := (n : ℝ) / 4 * (1 / 2 : ℝ) ^ 2 ^ j) hβ0 hn0 hβn4
    rw [quad_threshold_succ hn0.ne' j] at hstep
    exact (quad_move hL ha).trans (prob_mono_set' _ (satSet_sub n hstep))
  have hy0 : y ∈ satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ 2 ^ 0) (512 * log n)) := by
    rw [quad_threshold_zero]
    exact lt_of_lt_of_le hy (le_max_left _ _)
  have hsub : satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ 2 ^ T) (512 * log n))
      ⊆ satSet n (512 * log n) := by
    rw [max_eq_right hT]
  exact ((Median.kernel n Bool).event_chain (by positivity) T _ hmove y hy0).trans
    ((Median.kernel n Bool).event_mono_set hsub T y)

/-- **Consensus segment.** From a minority below `β = 512 log n`, two nested phases of four
rounds (`Dynamics.Kernel.nested_phases`: stay below `β` by `sat_move`, then jump to consensus by
`mono_move`; consensus absorbs) reach consensus after `8` rounds except with probability
`10 n⁻²`. -/
lemma consensus_segment (hL : (128 : ℝ) ≤ log n) {y : Config n Bool}
    (hy : falsesR y < 512 * log n) :
    1 - 10 * (1 / (n : ℝ) ^ 2) ≤ (Median.kernel n Bool).event (· ∈ consSet) 8 y := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hβ0 : (0 : ℝ) ≤ 512 * log n := by linarith only [hL]
  have hβn4 : 512 * log n ≤ (n : ℝ) / 4 := by
    linarith only [beta_le_n_div_eight hL, hβ0]
  let A : ℕ → Set (Config n Bool) :=
    fun i => if i ≤ 1 then satSet n (512 * log n) else consSet
  have hA1 : A 1 = satSet n (512 * log n) := if_pos le_rfl
  have hA2 : A 2 = consSet := if_neg (by norm_num)
  have hnest : ∀ i, 1 ≤ i → i < 2 → A (i + 1) ⊆ A i := by
    intro i h1 h2
    obtain rfl : i = 1 := by omega
    rw [hA1, hA2]
    intro z hz
    have hfr : falsesR z = 0 := (eq_true_iff_falsesR_zero).mp (mem_consSet.mp hz)
    refine mem_satSet.mpr ?_
    rw [hfr]
    linarith only [hL]
  have hstay : ∀ i, 1 ≤ i → i ≤ 2 → ∀ a ∈ A i,
      1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob (· ∈ A i) := by
    intro i h1 h2 a ha
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · rw [hA1] at ha ⊢
      have hstep : max ((7 / 8 : ℝ) * (512 * log n)) (512 * log n) ≤ 512 * log n :=
        max_le (by linarith only [hβ0]) le_rfl
      exact le_trans (sat_move hL hβ0 hβn4 ha) (prob_mono_set' _ (satSet_sub n hstep))
    · rw [hA2] at ha ⊢
      rw [cons_absorb ha]
      have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
      linarith
  have hmove : ∀ i, 1 ≤ i → i < 2 → ∀ a ∈ A i,
      1 - exp (-(log n / 2)) ≤ (Median.kernel n Bool a).prob (· ∈ A (i + 1)) := by
    intro i h1 h2 a ha
    obtain rfl : i = 1 := by omega
    rw [hA1] at ha
    rw [hA2]
    exact mono_move hL ha
  have hy1 : y ∈ A 1 := by
    rw [hA1]
    exact hy
  have hK := Dynamics.Kernel.nested_phases (Median.kernel n Bool) A (T := 2) (by norm_num) 4
    (ε := 1 / (n : ℝ) ^ 2) (ν := exp (-(log n / 2))) (by positivity) (by positivity)
    hnest hstay hmove y hy1
  rw [hA2, exp_half_pow_four hn] at hK
  have e : (4 : ℕ) * 2 = 8 := rfl
  rw [e] at hK
  push_cast at hK
  linarith

end Median
