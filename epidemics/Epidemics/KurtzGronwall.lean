import Mathlib

/-! # Kurtz's law of large numbers for SIR: discrete stability (CRN-2, helpers)

The deterministic half of the law of large numbers. A sequence `X k` in `ℝ × ℝ × ℝ` that follows
the Euler scheme `X (k+1) ≈ X k + h F (X k)` up to a martingale part bounded by `δ`
(`‖X k - X 0 - h ∑_{j<k} F (X j)‖ ≤ δ`) stays close to a sequence `y k` with one-step Euler error
at most `η`, provided `F` is `Lip`-Lipschitz along the two sequences:

  `‖X k - y k‖ ≤ (‖X 0 - y 0‖ + δ + n η) · exp(h Lip k)`  for `k ≤ n`.

The Grönwall step uses Mathlib's `discrete_gronwall` (applied to the partial sums, frozen after
step `n`), in the sum form `le_mul_exp_of_le_add_sum`.
-/

namespace Epidemics.Kurtz

open Finset Real

/-- **Discrete Grönwall inequality, sum form, on a finite range** (from Mathlib's
`discrete_gronwall`): if `0 ≤ u k ≤ A + b ∑_{j<k} u j` for `k ≤ n`, then `u k ≤ A exp(b k)`. -/
lemma le_mul_exp_of_le_add_sum {u : ℕ → ℝ} {A b : ℝ} {n : ℕ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hu0 : ∀ k, 0 ≤ u k) (hu : ∀ k ≤ n, u k ≤ A + b * ∑ j ∈ range k, u j) :
    ∀ k ≤ n, u k ≤ A * exp (b * k) := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, B = fun k ↦ A + b * ∑ j ∈ range (min k n), u j := ⟨_, rfl⟩
  have hB0 (k : ℕ) : 0 ≤ B k := by
    rw [hB]
    exact add_nonneg hA (mul_nonneg hb (sum_nonneg fun j _ ↦ hu0 j))
  have hrec : ∀ k ≥ 0, B (k + 1) ≤ (1 + b) * B k + 0 := by
    intro k _
    rcases lt_or_ge k n with hk | hk
    · have hk' := hu k hk.le
      rw [hB]
      simp only [min_eq_left (show k + 1 ≤ n by omega), min_eq_left hk.le, sum_range_succ]
      nlinarith
    · have h0 := hB0 k
      have h1 : B (k + 1) = B k := by
        rw [hB]
        simp only [min_eq_right hk, min_eq_right (show n ≤ k + 1 by omega)]
      rw [h1]
      nlinarith
  have hg := discrete_gronwall (u := B) (b := fun _ ↦ 0) (c := fun _ ↦ b) (n₀ := 0) (hB0 0) hrec
    (fun _ _ ↦ hb) (fun _ _ ↦ le_rfl)
  intro k hk
  have hk' := hg (Nat.zero_le k)
  simp only [sum_const_zero, add_zero, sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
    at hk'
  have hB00 : B 0 = A := by simp [hB]
  have hBk : u k ≤ B k := by
    rw [hB]
    simp only [min_eq_left hk]
    exact hu k hk
  calc u k ≤ B k := hBk
    _ ≤ B 0 * exp (k * b) := hk'
    _ = A * exp (b * k) := by rw [hB00, mul_comm (k : ℝ) b]

/-- The Euler errors accumulate linearly:
`‖y k - y 0 - h ∑_{j<k} F (y j)‖ ≤ k η` when every step errs by at most `η`. -/
lemma norm_sub_sum_le {F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} {y : ℕ → ℝ × ℝ × ℝ} {h η : ℝ} {n : ℕ}
    (hy : ∀ j < n, ‖y (j + 1) - y j - h • F (y j)‖ ≤ η) :
    ∀ k ≤ n, ‖y k - y 0 - h • ∑ j ∈ range k, F (y j)‖ ≤ k * η := by
  intro k hk
  have e : ∑ j ∈ range k, (y (j + 1) - y j - h • F (y j))
      = y k - y 0 - h • ∑ j ∈ range k, F (y j) := by
    rw [sum_sub_distrib, sum_range_sub, smul_sum]
  rw [← e]
  calc ‖∑ j ∈ range k, (y (j + 1) - y j - h • F (y j))‖
      ≤ ∑ j ∈ range k, ‖y (j + 1) - y j - h • F (y j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range k, η :=
        sum_le_sum fun j hj ↦ hy j (lt_of_lt_of_le (mem_range.mp hj) hk)
    _ = k * η := by rw [sum_const, card_range, nsmul_eq_mul]

/-- **Discrete stability of the Euler scheme.** If `X` follows the Euler scheme of `F` up to a
martingale part bounded by `δ`, `y` follows it up to one-step errors `η`, and `F` is
`Lip`-Lipschitz between `X j` and `y j`, then `‖X k - y k‖ ≤ (‖X 0 - y 0‖ + δ + n η) exp(h Lip k)`
for `k ≤ n`. -/
lemma norm_sub_le_of_euler {F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} {X y : ℕ → ℝ × ℝ × ℝ}
    {Lip h δ η : ℝ} {n : ℕ} (hLip0 : 0 ≤ Lip) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hLip : ∀ j < n, ‖F (X j) - F (y j)‖ ≤ Lip * ‖X j - y j‖)
    (hX : ∀ k ≤ n, ‖X k - X 0 - h • ∑ j ∈ range k, F (X j)‖ ≤ δ)
    (hy : ∀ j < n, ‖y (j + 1) - y j - h • F (y j)‖ ≤ η) :
    ∀ k ≤ n, ‖X k - y k‖ ≤ (‖X 0 - y 0‖ + δ + n * η) * exp (h * Lip * k) := by
  have hρ := norm_sub_sum_le hy
  refine le_mul_exp_of_le_add_sum (by positivity) (by positivity) (fun _ ↦ norm_nonneg _) ?_
  intro k hk
  have e : X k - y k = (X 0 - y 0) + (X k - X 0 - h • ∑ j ∈ range k, F (X j))
      - (y k - y 0 - h • ∑ j ∈ range k, F (y j))
      + h • ∑ j ∈ range k, (F (X j) - F (y j)) := by
    rw [sum_sub_distrib, smul_sub]
    abel
  have hsum : ‖∑ j ∈ range k, (F (X j) - F (y j))‖ ≤ Lip * ∑ j ∈ range k, ‖X j - y j‖ := by
    rw [mul_sum]
    exact (norm_sum_le _ _).trans
      (sum_le_sum fun j hj ↦ hLip j (lt_of_lt_of_le (mem_range.mp hj) hk))
  have hkn : (k : ℝ) * η ≤ n * η := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hη
  rw [e]
  calc ‖(X 0 - y 0) + (X k - X 0 - h • ∑ j ∈ range k, F (X j))
        - (y k - y 0 - h • ∑ j ∈ range k, F (y j)) + h • ∑ j ∈ range k, (F (X j) - F (y j))‖
      ≤ ‖X 0 - y 0‖ + ‖X k - X 0 - h • ∑ j ∈ range k, F (X j)‖
        + ‖y k - y 0 - h • ∑ j ∈ range k, F (y j)‖
        + ‖h • ∑ j ∈ range k, (F (X j) - F (y j))‖ := by
        have h1 := norm_add_le ((X 0 - y 0) + (X k - X 0 - h • ∑ j ∈ range k, F (X j))
          - (y k - y 0 - h • ∑ j ∈ range k, F (y j))) (h • ∑ j ∈ range k, (F (X j) - F (y j)))
        have h2 := norm_sub_le ((X 0 - y 0) + (X k - X 0 - h • ∑ j ∈ range k, F (X j)))
          (y k - y 0 - h • ∑ j ∈ range k, F (y j))
        have h3 := norm_add_le (X 0 - y 0) (X k - X 0 - h • ∑ j ∈ range k, F (X j))
        linarith
    _ ≤ ‖X 0 - y 0‖ + δ + k * η + h * (Lip * ∑ j ∈ range k, ‖X j - y j‖) := by
        rw [norm_smul, Real.norm_of_nonneg hh]
        gcongr
        · exact hX k hk
        · exact hρ k hk
    _ ≤ ‖X 0 - y 0‖ + δ + n * η + h * Lip * ∑ j ∈ range k, ‖X j - y j‖ := by
        rw [← mul_assoc]
        linarith

end Epidemics.Kurtz
