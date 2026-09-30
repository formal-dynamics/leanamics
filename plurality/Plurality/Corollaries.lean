import Plurality.Upper

/-!
# Corollaries 3.10, 3.11 and 3.12

Three choices of `λ` in Theorem 3.8 (`theorem_3_8_bigO`).

* **Corollary 3.10** (`corollary_3_10`): `λ = min {2k, (n / log n)^{1/3}}`.
  No hypothesis on the plurality size is needed: if `λ = 2k` then
  `c_m ≥ n/k` by pigeonhole, and otherwise the bias hypothesis alone forces
  `c_m ≥ s(c) ≥ n/λ`. This is the paper's headline bound
  `O(min {k, (n / log n)^{1/3}} log n)`.
* **Corollary 3.11** (`corollary_3_11`): `λ = log^ℓ n` for `ℓ ≥ 1`, giving
  `O(log^{ℓ+1} n)` rounds.
* **Corollary 3.12** (`corollary_3_12`): a constant `λ = β ≥ 3`, giving
  `O(log n)` rounds.
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3)

variable {n k : ℕ}

/-- **Pigeonhole**: the plurality color has at least `n/k` nodes. -/
lemma le_mul_maxc (x : Config n k) : n ≤ k * maxc (count x) := by
  calc n = ∑ j, count x j := (sum_count x).symm
    _ ≤ ∑ _j : Fin k, maxc (count x) := sum_le_sum fun j _ => le_maxc _ j
    _ = k * maxc (count x) := by simp

/-- The parameter `λ = min {2k, (n / log n)^{1/3}}` of Corollary 3.10. -/
noncomputable def lamK (n k : ℕ) : ℝ := min (2 * k) (((n : ℝ) / Real.log n) ^ (1 / 3 : ℝ))

/-- **Corollary 3.10.** Let `log n ≥ 40` and `k ≥ 2`, and write
`λ = min {2k, (n / log n)^{1/3}}`. If `m` is the unique plurality color and
`s(c) ≥ 22 √(λ n log n)`, then after at most `130 λ log n` rounds all nodes
support `m` with probability at least `1 - 143 λ log n / n`. -/
theorem corollary_3_10 (hL : 40 ≤ Real.log n) (hk : 2 ≤ k) (x : Config n k) {m : Fin k}
    (hM : argmaxSet (count x) = {m})
    (hs : 22 * √(lamK n k * n * Real.log n) ≤ bias (count x)) :
    ((10 * phases n (lamK n k) : ℕ) : ℝ) ≤ 130 * lamK n k * Real.log n ∧
      1 - 143 * lamK n k * Real.log n / n
        ≤ expList (Tgt3 n) (10 * phases n (lamK n k))
            (fun l => if Mono (run x l) m then (1 : ℝ) else 0) := by
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log n with hLdef
  have hL0 : 0 < L := by linarith
  set r : ℝ := ((n : ℝ) / L) ^ (1 / 3 : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr3 : r ^ 3 = (n : ℝ) / L := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  -- `(n / log n)^{1/3} ≥ 3`, since `n = e^L ≥ 27 L`
  have hr_ge : 3 ≤ r := by
    have h1 := mul_le_exp (show (20 : ℝ) ≤ L by linarith)
    have h2 : exp L = n := by rw [hLdef, exp_log hn0]
    have h27 : (27 : ℝ) ≤ n / L := by rw [le_div_iff₀ hL0]; linarith
    rw [← pow_le_pow_iff_left₀ (by norm_num) hr0 (by norm_num : (3 : ℕ) ≠ 0), hr3]
    linarith
  have hlam : 3 ≤ lamK n k := by
    refine le_min ?_ hr_ge
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hlam0 : 0 < lamK n k := by linarith
  -- the plurality has at least `n/λ` nodes
  have hcmax : (count x m : ℝ) = maxc (count x) := by exact_mod_cast argmaxSet_eq_singleton hM
  have hcm : (n : ℝ) / lamK n k ≤ count x m := by
    rcases min_cases (2 * (k : ℝ)) r with ⟨h, _⟩ | ⟨h, _⟩
    · -- `λ = 2k`: pigeonhole
      rw [lamK, h, hcmax]
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hpig : (n : ℝ) ≤ k * maxc (count x) := by exact_mod_cast le_mul_maxc x
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) (maxc (count x))]
    · -- `λ = (n / log n)^{1/3}`: the bias alone is at least `n/λ`
      have hl : lamK n k = r := by rw [lamK, h]
      rw [hl] at hs ⊢
      have hrpos : 0 < r := by linarith
      have hLr : L * r ^ 3 = n := by rw [hr3]; field_simp
      have hsq : (n : ℝ) / r ≤ √(r * n * L) := by
        rw [← Real.sqrt_sq (show 0 ≤ (n : ℝ) / r by positivity)]
        refine Real.sqrt_le_sqrt ?_
        rw [div_pow, div_le_iff₀ (by positivity)]
        have e : r * n * L * r ^ 2 = n * (L * r ^ 3) := by ring
        rw [e, hLr]
        nlinarith
      have hsm : (bias (count x) : ℝ) ≤ count x m := by
        rw [hcmax]; exact_mod_cast bias_le_maxc _
      have : 0 ≤ √(r * n * L) := Real.sqrt_nonneg _
      linarith
  exact theorem_3_8_bigO hL hk hlam x hM hcm hs

/-- **Corollary 3.11.** Let `log n ≥ 40`, `k ≥ 2` and `ℓ ≥ 1`. If `m` is the
unique plurality color, `c_m ≥ n / log^ℓ n` and `s(c) ≥ 22 √(n log^{ℓ+1} n)`,
then after at most `130 log^{ℓ+1} n` rounds all nodes support `m` with
probability at least `1 - 143 log^{ℓ+1} n / n`. -/
theorem corollary_3_11 (hL : 40 ≤ Real.log n) (hk : 2 ≤ k) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (x : Config n k) {m : Fin k} (hM : argmaxSet (count x) = {m})
    (hcm : (n : ℝ) / Real.log n ^ ℓ ≤ count x m)
    (hs : 22 * √(n * Real.log n ^ (ℓ + 1)) ≤ bias (count x)) :
    ((10 * phases n (Real.log n ^ ℓ) : ℕ) : ℝ) ≤ 130 * Real.log n ^ (ℓ + 1) ∧
      1 - 143 * Real.log n ^ (ℓ + 1) / n
        ≤ expList (Tgt3 n) (10 * phases n (Real.log n ^ ℓ))
            (fun l => if Mono (run x l) m then (1 : ℝ) else 0) := by
  set L := Real.log n
  have hlam : 3 ≤ L ^ ℓ := by
    have : L ^ 1 ≤ L ^ ℓ := pow_le_pow_right₀ (by linarith) hℓ
    rw [pow_one] at this
    linarith
  have e : L ^ ℓ * n * L = n * L ^ (ℓ + 1) := by ring
  have hs' : 22 * √(L ^ ℓ * n * L) ≤ bias (count x) := by rwa [e]
  have h := theorem_3_8_bigO hL hk hlam x hM hcm hs'
  have e2 : 130 * L ^ ℓ * L = 130 * L ^ (ℓ + 1) := by ring
  have e3 : 143 * L ^ ℓ * L = 143 * L ^ (ℓ + 1) := by ring
  rw [e2, e3] at h
  exact h

/-- **Corollary 3.12.** Let `log n ≥ 40`, `k ≥ 2` and `β ≥ 3`. If `m` is the
unique plurality color, `c_m ≥ n/β` and `s(c) ≥ 22 √(β n log n)`, then after at
most `130 β log n` rounds all nodes support `m` with probability at least
`1 - 143 β log n / n`. For a constant `β` this is `O(log n)` rounds. -/
theorem corollary_3_12 (hL : 40 ≤ Real.log n) (hk : 2 ≤ k) {β : ℝ} (hβ : 3 ≤ β)
    (x : Config n k) {m : Fin k} (hM : argmaxSet (count x) = {m})
    (hcm : (n : ℝ) / β ≤ count x m)
    (hs : 22 * √(β * n * Real.log n) ≤ bias (count x)) :
    ((10 * phases n β : ℕ) : ℝ) ≤ 130 * β * Real.log n ∧
      1 - 143 * β * Real.log n / n
        ≤ expList (Tgt3 n) (10 * phases n β)
            (fun l => if Mono (run x l) m then (1 : ℝ) else 0) :=
  theorem_3_8_bigO hL hk hβ x hM hcm hs

end Plurality
