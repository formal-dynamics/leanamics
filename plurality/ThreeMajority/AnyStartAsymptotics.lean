import Mathlib

/-!
# The real inequalities of Theorem 4 of BCEKMN17

Phase 1 of Theorem 4 stops at `k = ⌊n^{1/4} log^{1/8} n⌋` colours (`phase1Colours n`). For `n`
large, `1 ≤ k ≤ n^{1/3 − 1/24}`, and the two phases fit in `O(n^{3/4} log^{7/8} n)` rounds.
-/

namespace ThreeMajority

open Filter

/-- The number of colours at the end of Phase 1 of Theorem 4: `⌊n^{1/4} log^{1/8} n⌋`. -/
noncomputable def phase1Colours (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 8)⌋₊

/-- For `s > 0`, eventually `log y ^ r ≤ y ^ s`. -/
lemma eventually_log_rpow_le_rpow (r : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ y : ℝ in atTop, Real.log y ^ r ≤ y ^ s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop r hs).bound one_pos, eventually_ge_atTop 1]
    with y hy h1
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg h1) r),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) s), one_mul] at hy

/-- The eventual conditions on `y` used for Theorem 4: `3 ≤ y`, `log y ≤ y^{1/4}` and
`log^{1/8} y ≤ y^{1/24}`. -/
lemma eventually_phase1_conditions :
    ∀ᶠ y : ℝ in atTop, 3 ≤ y ∧ Real.log y ≤ y ^ ((1 : ℝ) / 4) ∧
      Real.log y ^ ((1 : ℝ) / 8) ≤ y ^ ((1 : ℝ) / 24) := by
  filter_upwards [eventually_ge_atTop 3,
    eventually_log_rpow_le_rpow 1 (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_log_rpow_le_rpow (1 / 8) (by norm_num : (0 : ℝ) < 1 / 24)] with y h1 h2 h3
  rw [Real.rpow_one] at h2
  exact ⟨h1, h2, h3⟩

/-- The algebra of the round count: if `k ≤ x ≤ 2k`, `1 ≤ L ≤ x`, `1 ≤ M`, `M x = y L` and
`x³ √L = M`, the two phases take at most `(49 + 4A) M` rounds. -/
lemma rounds_le_of_bounds {A k x L M y : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hkx : k ≤ x)
    (hxk : x ≤ 2 * k) (hLx : L ≤ x) (hM : 1 ≤ M) (hMx : M * x = y * L) (hx3 : x ^ 3 * √L = M) :
    24 * (y / k) * L + 1 + A * ((k ^ 2 * √L + k * L) * (k + L)) ≤ (49 + 4 * A) * M := by
  have hx1 : 1 ≤ x := hL.trans hLx
  have hk0 : 0 < k := by linarith
  have hsL : √L ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hss : √L * √L = L := Real.mul_self_sqrt (by linarith)
  have h1 : 24 * (y / k) * L ≤ 48 * M := by
    rw [show 24 * (y / k) * L = 24 * (y * L) / k by ring, div_le_iff₀ hk0, ← hMx]
    nlinarith [mul_le_mul_of_nonneg_left hxk (by linarith : (0 : ℝ) ≤ M)]
  have h2 : (k ^ 2 * √L + k * L) * (k + L) ≤ (x ^ 2 * √L + x * L) * (x + L) := by
    gcongr
  have h3 : x * L ≤ x ^ 2 * √L := by
    calc x * L = x * (√L * √L) := by rw [hss]
      _ ≤ x * (x * √L) := by gcongr; linarith
      _ = x ^ 2 * √L := by ring
  have h4 : (x ^ 2 * √L + x * L) * (x + L) ≤ 4 * M := by
    calc (x ^ 2 * √L + x * L) * (x + L) ≤ (2 * (x ^ 2 * √L)) * (2 * x) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = 4 * M := by rw [← hx3]; ring
  have h5 := mul_le_mul_of_nonneg_left (h2.trans h4) hA
  linarith

/-- For real `y ≥ 3` with `log y ≤ y^{1/4}`, `x = y^{1/4} log^{1/8} y` and
`M = y^{3/4} log^{7/8} y` satisfy `1 ≤ log y ≤ x`, `1 ≤ M`, `M x = y log y` and
`x³ √(log y) = M`. -/
lemma phase1_identities {y : ℝ} (hy : 3 ≤ y) (h1 : Real.log y ≤ y ^ ((1 : ℝ) / 4)) :
    1 ≤ Real.log y ∧ Real.log y ≤ y ^ ((1 : ℝ) / 4) * Real.log y ^ ((1 : ℝ) / 8) ∧
    1 ≤ y ^ ((3 : ℝ) / 4) * Real.log y ^ ((7 : ℝ) / 8) ∧
    y ^ ((3 : ℝ) / 4) * Real.log y ^ ((7 : ℝ) / 8) *
      (y ^ ((1 : ℝ) / 4) * Real.log y ^ ((1 : ℝ) / 8)) = y * Real.log y ∧
    (y ^ ((1 : ℝ) / 4) * Real.log y ^ ((1 : ℝ) / 8)) ^ 3 * √(Real.log y) =
      y ^ ((3 : ℝ) / 4) * Real.log y ^ ((7 : ℝ) / 8) := by
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    linarith [Real.exp_one_lt_d9]
  generalize Real.log y = L at h1 hL1 ⊢
  have hL0 : 0 < L := by linarith
  refine ⟨hL1, h1.trans (le_mul_of_one_le_right (by positivity)
    (Real.one_le_rpow hL1 (by norm_num))), one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (by linarith) (by norm_num)) (Real.one_le_rpow hL1 (by norm_num)), ?_, ?_⟩
  · rw [mul_mul_mul_comm, ← Real.rpow_add hy0, ← Real.rpow_add hL0]
    norm_num
  · rw [mul_pow, ← Real.rpow_mul_natCast hy0.le, ← Real.rpow_mul_natCast hL0.le,
      Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hL0]
    norm_num

/-- The asymptotic bookkeeping of Theorem 4: for `n` large, `k = phase1Colours n` satisfies
`1 ≤ k ≤ n^{1/3 − 1/24}`, and Phase 1 (`24 (n/k) log n + 1` rounds) together with Phase 2
(`A (k² √log n + k log n)(k + log n)` rounds) fits in `C n^{3/4} log^{7/8} n` rounds. -/
theorem anyStart_asymptotics (A : ℝ) (hA : 0 ≤ A) :
    ∃ C N : ℝ, ∀ n : ℕ, N ≤ n →
      2 ≤ n ∧ 1 ≤ phase1Colours n ∧
      (phase1Colours n : ℝ) ≤ (n : ℝ) ^ (1 / 3 - 1 / 24 : ℝ) ∧
      24 * ((n : ℝ) / phase1Colours n) * Real.log n + 1 +
          A * (((phase1Colours n : ℝ) ^ 2 * √(Real.log n) + phase1Colours n * Real.log n) *
            (phase1Colours n + Real.log n)) ≤
        C * (n : ℝ) ^ ((3 : ℝ) / 4) * Real.log n ^ ((7 : ℝ) / 8) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_phase1_conditions
  refine ⟨49 + 4 * A, N, fun n hn => ?_⟩
  obtain ⟨hy3, h1, h2⟩ := hN n hn
  refine ⟨by exact_mod_cast (by linarith : (2 : ℝ) ≤ n), ?_⟩
  obtain ⟨hL1, hLx, hM1, hMx, hx3⟩ := phase1_identities hy3 h1
  unfold phase1Colours
  generalize (n : ℝ) = y at *
  have hx7 : y ^ ((1 : ℝ) / 4) * Real.log y ^ ((1 : ℝ) / 8) ≤ y ^ (1 / 3 - 1 / 24 : ℝ) := by
    rw [show (1 / 3 - 1 / 24 : ℝ) = 1 / 4 + 1 / 24 by norm_num, Real.rpow_add (by linarith)]
    gcongr
  generalize y ^ ((1 : ℝ) / 4) * Real.log y ^ ((1 : ℝ) / 8) = x at *
  have hx0 : 0 ≤ x := by linarith
  have hk1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hL1.trans hLx)
  have hkx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hxk : x ≤ 2 * ⌊x⌋₊ := by
    have := Nat.lt_floor_add_one x
    have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hk1
    linarith
  refine ⟨hk1, hkx.trans hx7, ?_⟩
  exact (rounds_le_of_bounds hA hL1 hkx hxk hLx hM1 hMx hx3).trans_eq (mul_assoc _ _ _).symm

end ThreeMajority
