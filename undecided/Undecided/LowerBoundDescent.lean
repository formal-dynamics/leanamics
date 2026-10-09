import Undecided.LowerBoundDescentCore

/-! # The `Ω(md(c))` lower bound (UND-3): the descent of the undecided (SODA 2015, Lemma 6)

[BCNPS15, Lemma 6]: let `k ≤ ε (n / log n)^{1/6}`. If after the first round
`n / (2R(c̄)²) ≤ c_m⁽¹⁾ ≤ 2n / R(c̄)²` and `n (1 - 2/Λ(c̄)) ≤ q⁽¹⁾ ≤ n (1 - 1/(2Λ(c̄)))`, then
within the next `O(log n)` rounds there is a round `t̄` with `C_m ≤ γ n / md(c̄)` and
`|Q - n/2| ≤ 2γ² n / md(c̄)` w.h.p., for a sufficiently large constant `γ`.

Its proof has two one-round steps, stated separately (with failure probability `C / n²`, so
that they can be iterated over `O(log n)` rounds):
* (16) `undecided_square`: from `q = (1 + δ) n/2` with `1 - δ ≥ 1/(2k)`, w.h.p.
  `Q' ≤ (1 + δ²) n/2` (the number of undecided nodes approaches `n/2` doubly exponentially);
* (17) `undecided_not_below`: if all colours are at most `γ n / D`, then w.h.p.
  `Q' ≥ n/2 - 2γ² n / D` (`Q` cannot jump over the window around `n/2`).

Corrections (see `PROGRESS-UND3.md`):
* the conclusion `|Q - n/2| ≤ 2γ² / md(c̄)` of the paper is a typo for `2γ² n / md(c̄)`;
* the proof of (17) uses `∑ⱼ cⱼ² = c₁² md(c̄)`, which mixes the current configuration and the
  initial one; the bound `∑ⱼ cⱼ² ≤ maxⱼ cⱼ · (n - q) ≤ maxⱼ cⱼ · n` gives (17) for every `γ ≥ 1`;
* the bound is kept for **every** colour (`maxCount`), not only the initial plurality;
* the round `t̄` is deterministic here (it depends only on `n`, `Λ(c̄)` and `md(c̄)`), and the
  colours stay below `γ n / md(c̄)` at **every** round up to `t̄`, not only at `t̄`: this is what
  the proof gives, and it is needed for the per-round form `lower_bound_whp` of Theorem 8 at
  times before `t̄` (when `md(c̄) ≪ log Λ(c̄)`);
* (16) is stated for every `δ` with `1 - δ ≥ 1/(2k)`, a larger range than the paper's
  `1/md(c̄) ≤ δ ≤ 1 - 1/(2Λ(c̄))` (as `Λ(c̄) ≤ k`).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- **Equation (16) of [BCNPS15]** (proof of Lemma 6): the undecided nodes approach `n/2`
doubly exponentially. There is `C > 0` such that, for every `n` with `log n ≥ C`, every `k` with
`C k ≤ (n / log n)^{1/6}`, every configuration `y` with `q = (1 + δ) n/2` and
`1 - δ ≥ 1/(2k)`, after one round, with probability at least `1 - C / n²`,
`Q' ≤ (1 + δ²) n/2`. -/
theorem undecided_square : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) →
    ∀ (y : Config n k) (δ : ℝ), und y = (1 + δ) * n / 2 → 1 / (2 * k) ≤ 1 - δ →
      miss {z | und z ≤ (1 + δ ^ 2) * n / 2} 1 y ≤ C / n ^ 2 := by
  refine ⟨8, by norm_num, ?_⟩
  intro n hL k hk y δ hδ hmargin
  have hlogpos : 0 < log n := by linarith
  have hn1 : 1 < n := one_lt_n_of_log (by norm_num : (0 : ℝ) < 8) hL
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hundn : und y = n := by
      have hsum : ∑ i : Fin k, cnt y i = 0 :=
        Finset.sum_eq_zero fun i _ => False.elim (by have := i.isLt; omega)
      linarith [und_add_sum y, hsum]
    have hδ1 : δ = 1 := by
      have heq : (1 + δ) * (n : ℝ) / 2 = n := by
        rw [← hδ, hundn]
      have hmul : (1 + δ) * n = 2 * n := by
        field_simp at heq
        linarith
      have : (n : ℝ) * (1 + δ) = n * 2 := by linarith
      have : 1 + δ = 2 := mul_left_cancel₀ hnR.ne' this
      linarith
    have hEq : {z : Config n k | und z ≤ (1 + δ ^ 2) * n / 2} = Set.univ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hle : und z ≤ n := by
        have hsum : 0 ≤ ∑ i, cnt z i := sum_nonneg fun _ _ => cnt_nonneg _ _
        linarith [und_add_sum z, hsum]
      have hrhs : (1 + δ ^ 2) * n / 2 = n := by
        rw [hδ1]
        ring
      linarith
    rw [hEq]
    have h0 : miss (Set.univ : Set (Config n k)) 1 y = 0 := by
      classical
      unfold miss
      simp only [Set.mem_univ, if_true]
      exact expList_zero_fun 1
    have hpos : (0 : ℝ) ≤ 8 / (n : ℝ) ^ 2 := by positivity
    linarith
  · haveI : NeZero n := ⟨hn.ne'⟩
    have hlog1 : (1 : ℝ) ≤ log n := by linarith
    have hk_le : k ≤ n :=
      k_le_n_of_range (by norm_num : (1 : ℝ) ≤ 8) (by norm_num : (1 : ℝ) / 6 ≤ 1) hlog1 hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hpoly : (8 * (k : ℝ)) ^ 6 * log n ≤ n :=
      pow_of_rpow (by norm_num : 0 < 6) (by positivity) hlogpos (Nat.cast_nonneg n) hk
    have hpoly' : (262144 : ℝ) * (k : ℝ) ^ 6 * log n ≤ n := by
      have heq : (8 * (k : ℝ)) ^ 6 = (262144 : ℝ) * (k : ℝ) ^ 6 := by ring
      rwa [heq] at hpoly
    have hk6 : (1 : ℝ) ≤ (k : ℝ) ^ 6 := one_le_pow₀ hk1
    have h18 : (18 : ℝ) * log n ≤ n := by
      have hlog0 : 0 ≤ log n := hlogpos.le
      have hcoe : (18 : ℝ) ≤ 262144 * (k : ℝ) ^ 6 :=
        le_trans (by norm_num : (18 : ℝ) ≤ 262144) (le_mul_of_one_le_right (by norm_num) hk6)
      exact le_trans (mul_le_mul_of_nonneg_right hcoe hlog0) hpoly'
    have h6 : 6 * (3 * log n) ≤ n := by
      have : 6 * (3 * log n) = 18 * log n := by ring
      linarith
    have h3072 : (3072 : ℝ) * (k : ℝ) ^ 6 * log n ≤ n := by
      have hlog0 : 0 ≤ log n := hlogpos.le
      have h1 : (3072 : ℝ) * (k : ℝ) ^ 6 ≤ 262144 * (k : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      exact le_trans (mul_le_mul_of_nonneg_right h1 hlog0) hpoly'
    have hs : (32 * (k : ℝ) ^ 3) ^ 2 * (3 * log n) ≤ n := by
      have heq : (32 * (k : ℝ) ^ 3) ^ 2 * (3 * log n) = 3072 * (k : ℝ) ^ 6 * log n := by ring
      linarith
    have hsqrt : √((3 * log n) * n) ≤ n / (32 * (k : ℝ) ^ 3) :=
      sqrt_ln_le (by linarith) (by positivity) hs
    have hdevb : 2 * √((3 * log n) * n) ≤ n / (16 * (k : ℝ) ^ 3) := by
      have heq : 2 * (n / (32 * (k : ℝ) ^ 3)) = n / (16 * (k : ℝ) ^ 3) := by
        field_simp
        norm_num
      linarith
    let m : Fin k := ⟨0, hkpos⟩
    have hS : ∀ z, Good (3 * log n) m y z → z ∈ {z | und z ≤ (1 + δ ^ 2) * n / 2} := by
      intro z hG
      exact square_of_good hnR hkpos (by linarith) h6 hδ hmargin hdevb hG
    have hmiss := miss_round_le (by linarith : 0 < 3 * log n) m y _ hS
    calc
        miss {z | und z ≤ (1 + δ ^ 2) * n / 2} 1 y
          ≤ ((k : ℝ) + 4) * exp (-(3 * log n)) := hmiss
      _ = ((k : ℝ) + 4) / (n : ℝ) ^ 3 := by
          rw [exp_neg_three_log hnR]
          ring
      _ ≤ 5 / (n : ℝ) ^ 2 := bad_prob_le (by omega) hk_le
      _ ≤ 8 / (n : ℝ) ^ 2 := by
          rw [div_le_div_iff₀ (pow_pos hnR 2) (pow_pos hnR 2)]
          exact mul_le_mul_of_nonneg_right (by norm_num : (5 : ℝ) ≤ 8) (sq_nonneg (n : ℝ))

/-- **Equation (17) of [BCNPS15]** (proof of Lemma 6, corrected): `Q` cannot jump below the
window around `n/2`. There is `C > 0` such that, for every `γ ≥ 1`, every `n` with
`log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/6}`, every `D ∈ (0, k]` and every
configuration `y` whose colours are all at most `γ n / D`, after one round, with probability at
least `1 - C / n²`, `Q' ≥ n/2 - 2γ² n / D`. -/
theorem undecided_not_below : ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 1 ≤ γ → ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) → ∀ D : ℝ, 0 < D → D ≤ k →
    ∀ y : Config n k, (maxCount y : ℝ) ≤ γ * n / D →
      miss {z | (n : ℝ) / 2 - 2 * γ ^ 2 * n / D ≤ und z} 1 y ≤ C / n ^ 2 := by
  refine ⟨8, by norm_num, ?_⟩
  intro γ hγ n hL k hk D hD hDk y hmax
  have hlog1 : (1 : ℝ) ≤ log n := by linarith
  have hlogpos : 0 < log n := by linarith
  have hn1 : 1 < n := one_lt_n_of_log (by norm_num : (0 : ℝ) < 8) hL
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hk_le : k ≤ n :=
    k_le_n_of_range (by norm_num : (1 : ℝ) ≤ 8) (by norm_num : (1 : ℝ) / 6 ≤ 1) hlog1 hk
  have hkpos : 0 < k := k_pos_of_D hD hDk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hpoly : (8 * (k : ℝ)) ^ 6 * log n ≤ n :=
    pow_of_rpow (by norm_num : 0 < 6) (by positivity) hlogpos (Nat.cast_nonneg n) hk
  have hpoly' : (262144 : ℝ) * (k : ℝ) ^ 6 * log n ≤ n := by
    have heq : (8 * (k : ℝ)) ^ 6 = (262144 : ℝ) * (k : ℝ) ^ 6 := by ring
    rwa [heq] at hpoly
  have hk6 : (1 : ℝ) ≤ (k : ℝ) ^ 6 := one_le_pow₀ hk1
  have h18 : (18 : ℝ) * log n ≤ n := by
    have hlog0 : 0 ≤ log n := hlogpos.le
    have hcoe : (18 : ℝ) ≤ 262144 * (k : ℝ) ^ 6 :=
      le_trans (by norm_num : (18 : ℝ) ≤ 262144) (le_mul_of_one_le_right (by norm_num) hk6)
    exact le_trans (mul_le_mul_of_nonneg_right hcoe hlog0) hpoly'
  have h6 : 6 * (3 * log n) ≤ n := by
    have : 6 * (3 * log n) = 18 * log n := by ring
    linarith
  have hD2 : D ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hD.le hDk 2
  have hk26 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 := by
    have hk4 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
    calc (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * 1 := by ring
      _ ≤ (k : ℝ) ^ 2 * (k : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left hk4 (by positivity)
      _ = (k : ℝ) ^ 6 := by ring
  have hD6 : D ^ 2 ≤ (k : ℝ) ^ 6 := le_trans hD2 hk26
  have h12 : (12 : ℝ) * D ^ 2 * log n ≤ n := by
    have hlog0 : 0 ≤ log n := hlogpos.le
    have h1 : (12 : ℝ) * D ^ 2 ≤ 12 * (k : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_left hD6 (by norm_num)
    have h1' : (12 : ℝ) * D ^ 2 * log n ≤ 12 * (k : ℝ) ^ 6 * log n :=
      mul_le_mul_of_nonneg_right h1 hlog0
    have h2 : (12 : ℝ) * (k : ℝ) ^ 6 ≤ 262144 * (k : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact le_trans (le_trans h1' (mul_le_mul_of_nonneg_right h2 hlog0)) hpoly'
  have hs : (2 * D) ^ 2 * (3 * log n) ≤ n := by
    have heq : (2 * D) ^ 2 * (3 * log n) = 12 * D ^ 2 * log n := by ring
    linarith
  have hsqrt : √((3 * log n) * n) ≤ n / (2 * D) :=
    sqrt_ln_le (by linarith) (by linarith : 0 < 2 * D) hs
  have hdevb : 2 * √((3 * log n) * n) ≤ n / D := by
    have heq : 2 * (n / (2 * D)) = n / D := by
      field_simp
    linarith
  let m : Fin k := ⟨0, hkpos⟩
  have hS : ∀ z, Good (3 * log n) m y z →
      z ∈ {z | (n : ℝ) / 2 - 2 * γ ^ 2 * n / D ≤ und z} := by
    intro z hG
    exact not_below_of_good hnR (by linarith) h6 hγ hD hmax hdevb hG
  have hmiss := miss_round_le (by linarith : 0 < 3 * log n) m y _ hS
  calc
      miss {z | (n : ℝ) / 2 - 2 * γ ^ 2 * n / D ≤ und z} 1 y
        ≤ ((k : ℝ) + 4) * exp (-(3 * log n)) := hmiss
    _ = ((k : ℝ) + 4) / (n : ℝ) ^ 3 := by
        rw [exp_neg_three_log hnR]
        ring
    _ ≤ 5 / (n : ℝ) ^ 2 := bad_prob_le (by omega) hk_le
    _ ≤ 8 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hnR 2) (pow_pos hnR 2)]
        exact mul_le_mul_of_nonneg_right (by norm_num : (5 : ℝ) ≤ 8) (sq_nonneg (n : ℝ))

set_option maxHeartbeats 2000000 in
/-- **Lemma 6 of [BCNPS15]** (descent of the undecided, corrected). There are `γ ≥ 1` and
`C > 0` such that, for every `n` with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/6}`,
every initial configuration `x` without undecided nodes and with `md(x) ≥ C`, and every
configuration `y` as after the first round (Lemma 3: all colours at most `2n / R(x)²`, and
`n (1 - 2/Λ(x)) ≤ q ≤ n (1 - 1/(2Λ(x)))`), there is a round `t ≤ C log n` such that, with
probability at least `1 - C / n` each: at every round `s ≤ t` all colours are at most
`γ n / md(x)`; and at round `t` moreover `|q - n/2| ≤ 2γ² n / md(x)`. -/
theorem descent : ∃ γ C : ℝ, 1 ≤ γ ∧ 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) →
    ∀ x : Config n k, count x none = 0 → C ≤ md x →
    ∀ y : Config n k, (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 →
      n * (1 - 2 / ratioLam x) ≤ und y → und y ≤ n * (1 - 1 / (2 * ratioLam x)) →
      ∃ t : ℕ, (t : ℝ) ≤ C * Real.log n ∧
        (∀ s ≤ t, miss {z | (maxCount z : ℝ) ≤ γ * n / md x} s y ≤ C / n) ∧
        miss {z | (maxCount z : ℝ) ≤ γ * n / md x ∧
          |und z - n / 2| ≤ 2 * γ ^ 2 * n / md x} t y ≤ C / n := by
  refine ⟨24, 1000000, by norm_num, by norm_num, ?_⟩
  intro n hL k hk x _ hmd y hmax0 hUlo hUhi
  classical
  let γ : ℝ := 24
  let C : ℝ := 1000000
  have hγ : (1 : ℝ) ≤ γ := by norm_num
  have hγ24 : (24 : ℝ) ≤ γ := by norm_num
  have hCpos : (0 : ℝ) < C := by norm_num
  have hC8 : (8 : ℝ) ≤ C := by norm_num
  have hC1 : (1 : ℝ) ≤ C := by norm_num
  have hC6 : (8 : ℝ) ^ 6 ≤ C ^ 6 := pow_le_pow_left₀ (by norm_num) hC8 6
  have hlogpos : 0 < log n := log_pos_of_log hCpos hL
  have hlog1 : (1 : ℝ) ≤ log n := by linarith
  have hlognn : 0 ≤ log n := hlogpos.le
  have hn1 : 1 < n := one_lt_n_of_log hCpos hL
  have hn : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : NeZero n := ⟨hn.ne'⟩
  let D : ℝ := md x
  have hCD : C ≤ D := hmd
  have hD : 0 < D := lt_of_lt_of_le hCpos hCD
  have hDk : D ≤ (k : ℝ) := md_le_card x
  have hkpos : 0 < k := k_pos_of_D hD hDk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hk_le : k ≤ n :=
    k_le_n_of_range hC1 (by norm_num : (1 : ℝ) / 6 ≤ 1) hlog1 hk
  have hkpow : (1 : ℝ) ≤ (k : ℝ) ^ 6 := one_le_pow₀ hk1
  let Λ : ℝ := ratioLam x
  have hΛD : D ≤ Λ := md_le_ratioLam x
  have hΛk : Λ ≤ (k : ℝ) := ratioLam_le_card x
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hΛpos : 0 < Λ := by linarith
  have hRsq : Λ * D = ratioR x ^ 2 := by
    have hdef : Λ = ratioR x ^ 2 / D := by simpa [Λ, D] using ratioLam_def x
    rw [hdef]
    exact div_mul_cancel₀ _ hD.ne'
  let M0 : ℝ := 2 * n / ratioR x ^ 2
  have hM0eq : M0 = 2 * (n : ℝ) / (Λ * D) := by
    simp only [M0]
    rw [← hRsq]
  have hΛDle : Λ * D ≤ (k : ℝ) ^ 2 := by
    calc Λ * D ≤ (k : ℝ) * D := mul_le_mul_of_nonneg_right hΛk hD.le
      _ ≤ (k : ℝ) * (k : ℝ) := mul_le_mul_of_nonneg_left hDk hkR.le
      _ = (k : ℝ) ^ 2 := by ring
  have hM0pos : 0 < M0 := by
    rw [hM0eq]
    exact div_pos (by positivity) (mul_pos hΛpos hD)
  have hM0nn : 0 ≤ M0 := hM0pos.le
  have hM0ge : 2 * (n : ℝ) / (k : ℝ) ^ 2 ≤ M0 := by
    rw [hM0eq, div_le_div_iff₀ (pow_pos hkR 2) (mul_pos hΛpos hD)]
    exact mul_le_mul_of_nonneg_left hΛDle (by positivity)
  have hmaxM0 : (maxCount y : ℝ) ≤ M0 := by simpa [M0] using hmax0
  let ℓ : ℝ := 3 * log n
  have hℓ0 : 0 ≤ ℓ := by rw [show ℓ = 3 * log n from rfl]; linarith
  have hℓpos : 0 < ℓ := by rw [show ℓ = 3 * log n from rfl]; linarith
  let ε : ℝ := 2 * √(2 * ℓ / M0)
  have hε0 : 0 ≤ ε := by rw [show ε = 2 * √(2 * ℓ / M0) from rfl]; positivity
  have hpoly : (C * (k : ℝ)) ^ 6 * log n ≤ (n : ℝ) :=
    pow_of_rpow (b := 6) (by norm_num) (mul_nonneg hCpos.le (Nat.cast_nonneg k))
      hlogpos hnR.le hk
  have hk6 : (k : ℝ) ^ 6 * log n ≤ (n : ℝ) / C ^ 6 := by
    have hCpow : 0 < C ^ 6 := pow_pos hCpos 6
    rw [le_div_iff₀ hCpow]
    calc (k : ℝ) ^ 6 * log n * C ^ 6 = C ^ 6 * (k : ℝ) ^ 6 * log n := by ring
      _ = (C * (k : ℝ)) ^ 6 * log n := by rw [mul_pow]
      _ ≤ (n : ℝ) := hpoly
  have hε_small : (k : ℝ) * ε ≤ 1 / 100 :=
    colour_eps_small hC8 hk1 hnR hlogpos hM0ge (by rfl) hk6 (by rfl)
  have h6n : 6 * ℓ ≤ (n : ℝ) := by
    have hcoef : (18 : ℝ) ≤ C ^ 6 * (k : ℝ) ^ 6 := by
      calc (18 : ℝ) ≤ (8 : ℝ) ^ 6 := by norm_num
        _ ≤ C ^ 6 := hC6
        _ = C ^ 6 * 1 := by ring
        _ ≤ C ^ 6 * (k : ℝ) ^ 6 := mul_le_mul_of_nonneg_left hkpow (pow_nonneg hCpos.le 6)
    calc 6 * ℓ = 18 * log n := by rw [show ℓ = 3 * log n from rfl]; ring
      _ ≤ (C ^ 6 * (k : ℝ) ^ 6) * log n := mul_le_mul_of_nonneg_right hcoef hlognn
      _ = (C * (k : ℝ)) ^ 6 * log n := by rw [mul_pow]
      _ ≤ (n : ℝ) := hpoly
  have hk2log : (k : ℝ) ^ 2 * log n ≤ (n : ℝ) / C ^ 6 := by
    have hk4 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
    have hdiv : (k : ℝ) ^ 6 * log n / (k : ℝ) ^ 4 ≤ ((n : ℝ) / C ^ 6) / (k : ℝ) ^ 4 :=
      div_le_div_of_nonneg_right hk6 (by positivity)
    have heq : (k : ℝ) ^ 2 * log n = (k : ℝ) ^ 6 * log n / (k : ℝ) ^ 4 := by
      field_simp
    have hself : ((n : ℝ) / C ^ 6) / (k : ℝ) ^ 4 ≤ (n : ℝ) / C ^ 6 :=
      div_le_self (div_nonneg hnR.le (pow_nonneg hCpos.le 6)) hk4
    linarith only [hdiv, heq, hself]
  have hdevU : 2 * √(ℓ * (n : ℝ)) ≤ (n : ℝ) / (16 * (k : ℝ) ^ 3) := by
    have hs : (0 : ℝ) < 32 * (k : ℝ) ^ 3 := mul_pos (by norm_num) (pow_pos hkR 3)
    have hcoef : (3072 : ℝ) ≤ C ^ 6 := by
      calc (3072 : ℝ) ≤ (8 : ℝ) ^ 6 := by norm_num
        _ ≤ C ^ 6 := hC6
    have hs2 : (32 * (k : ℝ) ^ 3) ^ 2 * ℓ ≤ (n : ℝ) := by
      calc (32 * (k : ℝ) ^ 3) ^ 2 * ℓ = 3072 * ((k : ℝ) ^ 6 * log n) := by
            rw [show ℓ = 3 * log n from rfl]; ring
        _ ≤ C ^ 6 * ((k : ℝ) ^ 6 * log n) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by positivity) hlognn)
        _ = (C * (k : ℝ)) ^ 6 * log n := by rw [mul_pow]; ring
        _ ≤ (n : ℝ) := hpoly
    have hsqrt := sqrt_ln_le hℓ0 hs hs2
    have htwo : 2 * ((n : ℝ) / (32 * (k : ℝ) ^ 3)) = (n : ℝ) / (16 * (k : ℝ) ^ 3) := by
      field_simp; ring
    calc 2 * √(ℓ * (n : ℝ)) ≤ 2 * ((n : ℝ) / (32 * (k : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = (n : ℝ) / (16 * (k : ℝ) ^ 3) := htwo
  have hdevD : 2 * √(ℓ * (n : ℝ)) ≤ (n : ℝ) / D := by
    have hs : 0 < 2 * D := by linarith
    have hD2 : D ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith only [hDk, hD.le]
    have h12c : (12 : ℝ) ≤ C ^ 6 := by
      calc (12 : ℝ) ≤ (8 : ℝ) ^ 6 := by norm_num
        _ ≤ C ^ 6 := hC6
    have h12 : 12 * (D ^ 2 * log n) ≤ (n : ℝ) := by
      have hDlog : D ^ 2 * log n ≤ (k : ℝ) ^ 2 * log n :=
        mul_le_mul_of_nonneg_right hD2 hlognn
      calc 12 * (D ^ 2 * log n) ≤ 12 * ((k : ℝ) ^ 2 * log n) :=
            mul_le_mul_of_nonneg_left hDlog (by norm_num)
        _ ≤ 12 * ((n : ℝ) / C ^ 6) := mul_le_mul_of_nonneg_left hk2log (by norm_num)
        _ ≤ C ^ 6 * ((n : ℝ) / C ^ 6) :=
            mul_le_mul_of_nonneg_right h12c (div_nonneg hnR.le (pow_nonneg hCpos.le 6))
        _ = (n : ℝ) := by field_simp
    have hs2 : (2 * D) ^ 2 * ℓ ≤ (n : ℝ) := by
      calc (2 * D) ^ 2 * ℓ = 12 * (D ^ 2 * log n) := by rw [show ℓ = 3 * log n from rfl]; ring
        _ ≤ (n : ℝ) := h12
    have hsqrt := sqrt_ln_le hℓ0 hs hs2
    have htwo : 2 * ((n : ℝ) / (2 * D)) = (n : ℝ) / D := by field_simp
    calc 2 * √(ℓ * (n : ℝ)) ≤ 2 * ((n : ℝ) / (2 * D)) :=
          mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = (n : ℝ) / D := htwo
  have h6M0 : 6 * ℓ ≤ 2 * M0 := by
    have hfour : 4 * (n : ℝ) / (k : ℝ) ^ 2 ≤ 2 * M0 := by
      calc 4 * (n : ℝ) / (k : ℝ) ^ 2 = 2 * (2 * (n : ℝ) / (k : ℝ) ^ 2) := by ring
        _ ≤ 2 * M0 := mul_le_mul_of_nonneg_left hM0ge (by norm_num)
    have hcoef : (18 : ℝ) ≤ 4 * C ^ 6 := by
      calc (18 : ℝ) ≤ 4 * ((8 : ℝ) ^ 6) := by norm_num
        _ ≤ 4 * C ^ 6 := mul_le_mul_of_nonneg_left hC6 (by norm_num)
    have hleft : 6 * ℓ ≤ 4 * (n : ℝ) / (k : ℝ) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hkR 2)]
      calc 6 * ℓ * (k : ℝ) ^ 2 = 18 * ((k : ℝ) ^ 2 * log n) := by
            rw [show ℓ = 3 * log n from rfl]; ring
        _ ≤ 18 * ((n : ℝ) / C ^ 6) := mul_le_mul_of_nonneg_left hk2log (by norm_num)
        _ ≤ (4 * C ^ 6) * ((n : ℝ) / C ^ 6) :=
            mul_le_mul_of_nonneg_right hcoef (div_nonneg hnR.le (pow_nonneg hCpos.le 6))
        _ = 4 * (n : ℝ) := by field_simp
    exact hleft.trans hfour
  let u : ℝ := 1 - 1 / Λ
  let w : ℝ := 4 * γ ^ 2 / D
  have hw0 : 0 ≤ w := by rw [show w = 4 * γ ^ 2 / D from rfl]; exact div_nonneg (by norm_num) hD.le
  have hwpos : 0 < w := by
    rw [show w = 4 * γ ^ 2 / D from rfl]
    exact div_pos (by norm_num) hD
  have hu0 : 0 ≤ u := by
    rw [show u = 1 - 1 / Λ from rfl]
    have : 1 / Λ ≤ 1 := (div_le_one hΛpos).mpr hΛ1
    linarith
  have hu1 : u ≤ 1 := by
    rw [show u = 1 - 1 / Λ from rfl]
    have : 0 ≤ 1 / Λ := div_nonneg zero_le_one hΛpos.le
    linarith
  have hw_half : w ≤ (1 : ℝ) / 2 := by
    rw [show w = 4 * γ ^ 2 / D from rfl, div_le_div_iff₀ hD (by norm_num : (0 : ℝ) < 2)]
    have : (8 : ℝ) * γ ^ 2 ≤ C := by norm_num
    linarith
  have hw1 : w ≤ 1 := by linarith
  have hwsq : w ^ 2 ≤ w := sq_le hw0 hw1
  have hwu : w ≤ u := by
    have hnum : 4 * γ ^ 2 + 1 ≤ D := by
      have : 4 * γ ^ 2 + 1 ≤ C := by norm_num
      linarith
    have hinv : 1 / Λ ≤ 1 / D := by
      rw [div_le_div_iff₀ hΛpos hD]
      nlinarith only [hΛD]
    have hsum : 4 * γ ^ 2 / D + 1 / Λ ≤ 1 := by
      calc 4 * γ ^ 2 / D + 1 / Λ ≤ 4 * γ ^ 2 / D + 1 / D := by linarith only [hinv]
        _ = (4 * γ ^ 2 + 1) / D := by field_simp
        _ ≤ 1 := (div_le_one hD).mpr hnum
    rw [show w = 4 * γ ^ 2 / D from rfl, show u = 1 - 1 / Λ from rfl]
    linarith only [hsum]
  let e : ℕ → ℝ := fun s => max (u ^ (2 ^ s)) w
  have he_nn : ∀ s, 0 ≤ e s := by
    intro s
    have : w ≤ e s := by simp [e]
    linarith
  have he_le_u : ∀ s, e s ≤ u := by
    intro s
    refine max_le ?_ hwu
    exact pow_le_of_le_one hu0 hu1 (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  have hu_k : u ≤ 1 - 1 / (k : ℝ) := by
    have hinv : 1 / (k : ℝ) ≤ 1 / Λ := by
      rw [div_le_div_iff₀ hkR hΛpos]
      nlinarith only [hΛk]
    rw [show u = 1 - 1 / Λ from rfl]
    linarith only [hinv]
  have hemargin : ∀ s, e s ≤ 1 - 1 / (k : ℝ) := fun s => (he_le_u s).trans hu_k
  have he_next : ∀ s, max ((e s) ^ 2) (w ^ 2) ≤ e (s + 1) := by
    intro s
    have hup : 0 ≤ u ^ (2 ^ s) := pow_nonneg hu0 _
    have hsq : (e s) ^ 2 = max ((u ^ (2 ^ s)) ^ 2) (w ^ 2) := by
      simpa [e] using max_sq hup hw0
    have hpow : (u ^ (2 ^ s)) ^ 2 = u ^ (2 ^ (s + 1)) := by
      rw [← pow_mul]
      have : (2 ^ s) * 2 = 2 ^ (s + 1) := by rw [pow_succ, mul_comm]
      rw [this]
    have hw_le : w ≤ e s := by simp [e]
    have hwsq_le : w ^ 2 ≤ (e s) ^ 2 := (sq_le_sq₀ hw0 (he_nn s)).mpr hw_le
    have hmax_le : max (u ^ (2 ^ (s + 1))) (w ^ 2) ≤ e (s + 1) := by
      rw [show e (s + 1) = max (u ^ (2 ^ (s + 1))) w from rfl]
      exact max_le (le_max_left _ _) (le_trans hwsq (le_max_right _ _))
    calc max ((e s) ^ 2) (w ^ 2) = (e s) ^ 2 := max_eq_left hwsq_le
      _ = max (u ^ (2 ^ (s + 1))) (w ^ 2) := by rw [hsq, hpow]
      _ ≤ e (s + 1) := hmax_le
  let mΛ : ℕ := Nat.ceil Λ
  let a : ℕ := Nat.clog 2 mΛ
  have hmΛ_ge : Λ ≤ (mΛ : ℝ) := Nat.le_ceil _
  have hmΛ_le : mΛ ≤ k := by rw [Nat.ceil_le]; exact hΛk
  have hmΛ_pos : 0 < mΛ := by
    have h1 : (1 : ℝ) ≤ (mΛ : ℝ) := hΛ1.trans hmΛ_ge
    have hnat : 1 ≤ mΛ := by exact_mod_cast h1
    omega
  have h2a : Λ ≤ (2 : ℝ) ^ a := by
    calc Λ ≤ (mΛ : ℝ) := hmΛ_ge
      _ ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) mΛ
      _ = (2 : ℝ) ^ a := by norm_cast
  have ha_pos : 0 < a := by
    have hbig : 1 < mΛ := by
      by_contra h
      have hm : mΛ ≤ 1 := by omega
      have : (mΛ : ℝ) ≤ 1 := by exact_mod_cast hm
      linarith [hmΛ_ge, show (2 : ℝ) ≤ Λ by linarith [show (2 : ℝ) ≤ C by norm_num, hCD]]
    exact Nat.clog_pos (by norm_num : 1 < 2) hbig
  have h2a_le : (2 : ℝ) ^ a ≤ 2 * Λ := by
    have hbig : 1 < mΛ := by
      by_contra h
      have hm : mΛ ≤ 1 := by omega
      have : (mΛ : ℝ) ≤ 1 := by exact_mod_cast hm
      linarith [hmΛ_ge, show (2 : ℝ) ≤ Λ by linarith [show (2 : ℝ) ≤ C by norm_num, hCD]]
    have hpred : 2 ^ (a - 1) < mΛ := Nat.pow_pred_clog_lt_self (by norm_num) hbig
    have hpred_le : 2 ^ (a - 1) ≤ mΛ - 1 := by omega
    have hdouble : 2 ^ a ≤ 2 * (mΛ - 1) := by
      have ha1 : a = (a - 1) + 1 := by omega
      rw [ha1, Nat.pow_succ]
      exact (Nat.mul_le_mul_right 2 hpred_le).trans_eq (Nat.mul_comm _ _)
    have hleR : (2 : ℝ) ^ a ≤ 2 * ((mΛ : ℝ) - 1) := by
      have hone : (1 : ℕ) ≤ mΛ := by omega
      have hnat : ((2 ^ a : ℕ) : ℝ) ≤ ((2 * (mΛ - 1) : ℕ) : ℝ) := by exact_mod_cast hdouble
      have hsub : ((mΛ - 1 : ℕ) : ℝ) = (mΛ : ℝ) - 1 := by
        rw [Nat.cast_sub hone, Nat.cast_one]
      rw [Nat.cast_mul, hsub, Nat.cast_ofNat] at hnat
      simpa [Nat.cast_pow] using hnat
    have hmlt : (mΛ : ℝ) - 1 < Λ := by
      have hmLt : (mΛ : ℝ) < Λ + 1 := Nat.ceil_lt_add_one hΛpos.le
      linarith
    exact le_of_lt (lt_of_le_of_lt hleR (mul_lt_mul_of_pos_left hmlt (by norm_num)))
  let Lw : ℝ := log (1 / w)
  have hinvw : 0 < 1 / w := by positivity
  have hinv_eq : 1 / w = D / (4 * γ ^ 2) := by
    rw [show w = 4 * γ ^ 2 / D from rfl]
    field_simp
  have hLw_pos : 0 < Lw := by
    rw [show Lw = log (1 / w) from rfl, Real.log_pos_iff hinvw.le, one_lt_div hwpos]
    linarith
  have hLw_le_k : Lw ≤ (k : ℝ) := by
    calc Lw ≤ 1 / w - 1 := by rw [show Lw = log (1 / w) from rfl]; exact log_le_sub_one_of_pos hinvw
      _ ≤ 1 / w := by linarith
      _ = D / (4 * γ ^ 2) := hinv_eq
      _ ≤ D := by
          rw [div_le_iff₀ (by positivity : 0 < 4 * γ ^ 2)]
          have h1 : (1 : ℝ) ≤ 4 * γ ^ 2 := by norm_num
          calc D = D * 1 := (mul_one D).symm
            _ ≤ D * (4 * γ ^ 2) := mul_le_mul_of_nonneg_left h1 hD.le
      _ ≤ (k : ℝ) := hDk
  let mL : ℕ := Nat.ceil Lw
  let b : ℕ := Nat.clog 2 mL
  have hmL_pos : 0 < mL := by
    by_contra h0
    have hm0 : mL = 0 := by omega
    have hceil : Lw ≤ (mL : ℝ) := by simpa [mL] using Nat.le_ceil Lw
    have : Lw ≤ 0 := by rw [hm0] at hceil; exact_mod_cast hceil
    linarith only [hLw_pos, this]
  have hmL_le_k : mL ≤ k := by rw [Nat.ceil_le]; exact hLw_le_k
  have h2b : Lw ≤ (2 : ℝ) ^ b := by
    calc Lw ≤ (mL : ℝ) := Nat.le_ceil _
      _ ≤ ((2 ^ b : ℕ) : ℝ) := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) mL
      _ = (2 : ℝ) ^ b := by norm_cast
  have hexpw : exp (-Lw) = w := by
    rw [show Lw = log (1 / w) from rfl, exp_neg, exp_log hinvw]
    field_simp
  have hclose : u ^ (2 ^ (a + b)) ≤ w := by
    have hratio : Lw ≤ (2 : ℝ) ^ (a + b) / Λ := by
      rw [le_div_iff₀ hΛpos]
      calc Lw * Λ ≤ ((2 : ℝ) ^ b) * Λ := mul_le_mul_of_nonneg_right h2b hΛpos.le
        _ ≤ ((2 : ℝ) ^ b) * ((2 : ℝ) ^ a) :=
            mul_le_mul_of_nonneg_left h2a (pow_nonneg (by norm_num) _)
        _ = (2 : ℝ) ^ (a + b) := by rw [mul_comm, ← pow_add, add_comm]
    have hneg : -((2 : ℝ) ^ (a + b)) / Λ ≤ -Lw := by
      have := neg_le_neg hratio
      simpa [neg_div] using this
    calc u ^ (2 ^ (a + b)) ≤ exp (-((2 : ℝ) ^ (a + b)) / Λ) := by
          simpa [u] using u_pow_le hΛ1 (a + b)
      _ ≤ exp (-Lw) := exp_le_exp.mpr hneg
      _ = w := hexpw
  haveI : DecidablePred (fun s : ℕ => u ^ (2 ^ s) ≤ w) := fun _ => Classical.propDecidable _
  have hex : ∃ s, u ^ (2 ^ s) ≤ w := ⟨a + b, hclose⟩
  let t : ℕ := Nat.find hex
  have ht_spec : u ^ (2 ^ t) ≤ w := Nat.find_spec hex
  have ht_le : t ≤ a + b := Nat.find_min' hex hclose
  have he_pow : ∀ r < t, e r = u ^ (2 ^ r) := by
    intro r hr
    have hnot : ¬ u ^ (2 ^ r) ≤ w := Nat.find_min hex hr
    have hgt : w < u ^ (2 ^ r) := lt_of_not_ge hnot
    simpa [e] using (max_eq_left hgt.le : max (u ^ (2 ^ r)) w = u ^ (2 ^ r))
  have het : e t = w := by
    simpa [e] using (max_eq_right ht_spec : max (u ^ (2 ^ t)) w = w)
  have ha_log : (a : ℝ) ≤ 2 * log n + 2 := by
    have hmn : mΛ ≤ 2 * n := by
      have : mΛ ≤ n := hmΛ_le.trans hk_le
      omega
    exact clog_two_le_two_log hn1 hmn hmΛ_pos
  have hb_log : (b : ℝ) ≤ 2 * log n + 2 := by
    have hmn : mL ≤ 2 * n := by
      have : mL ≤ n := hmL_le_k.trans hk_le
      omega
    exact clog_two_le_two_log hn1 hmn hmL_pos
  have ht_log : (t : ℝ) ≤ C * log n := by
    have hsum : (t : ℝ) ≤ (a : ℝ) + (b : ℝ) := by
      have ht' : (t : ℝ) ≤ (a + b : ℕ) := by exact_mod_cast ht_le
      have hadd : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by norm_cast
      linarith
    calc (t : ℝ) ≤ (a : ℝ) + (b : ℝ) := hsum
      _ ≤ (2 * log n + 2) + (2 * log n + 2) := by linarith
      _ = 4 * log n + 4 := by ring
      _ ≤ 8 * log n := by linarith [hlog1]
      _ ≤ C * log n := mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ C) hlognn
  have ha_le_k : a ≤ k := (clog_two_le mΛ).trans hmΛ_le
  have haε : ε * (a : ℝ) ≤ 1 := by
    calc ε * (a : ℝ) = (a : ℝ) * ε := by ring
      _ ≤ (k : ℝ) * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast ha_le_k) hε0
      _ ≤ 1 / 100 := hε_small
      _ ≤ 1 := by norm_num
  have hb_le_k : b ≤ k := (clog_two_le mL).trans hmL_le_k
  have hbγ : (b : ℝ) * (γ / D) ≤ 1 / 96 := by
    have hb_le : (b : ℝ) ≤ (mL : ℝ) := by exact_mod_cast clog_two_le mL
    have hceil : (mL : ℝ) < Lw + 1 := Nat.ceil_lt_add_one hLw_pos.le
    have hL1 : Lw + 1 ≤ 1 / w := by
      have hlogw : Lw ≤ 1 / w - 1 := log_le_sub_one_of_pos hinvw
      linarith only [hlogw]
    have hb_lt : (b : ℝ) < 1 / w := by linarith
    have hmul : (b : ℝ) * (γ / D) < (1 / w) * (γ / D) :=
      mul_lt_mul_of_pos_right hb_lt (div_pos (by norm_num) hD)
    have heq : (1 / w) * (γ / D) = 1 / (4 * γ) := by rw [hinv_eq]; field_simp
    have h96 : 1 / (4 * γ) = 1 / 96 := by norm_num
    linarith
  have hbε : (b : ℝ) * ε ≤ 1 / 100 := by
    calc (b : ℝ) * ε ≤ (k : ℝ) * ε :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hb_le_k) hε0
      _ ≤ 1 / 100 := hε_small
  have hδnn : 0 ≤ γ / D + ε := by
    have : 0 ≤ γ / D := div_nonneg (by norm_num) hD.le
    linarith
  have hdrift_b : (b : ℝ) * (γ / D + ε) ≤ 1 / 6 := by
    have : (b : ℝ) * (γ / D + ε) = (b : ℝ) * (γ / D) + (b : ℝ) * ε := by ring
    linarith [hbγ, hbε, show (1 : ℝ) / 96 + 1 / 100 ≤ 1 / 6 by norm_num]
  have hdrift : ∀ d ≤ t - a, (d : ℝ) * (γ / D + ε) ≤ 1 / 6 := by
    intro d hd
    have hdb : d ≤ b := by omega
    calc (d : ℝ) * (γ / D + ε) ≤ (b : ℝ) * (γ / D + ε) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hdb) hδnn
      _ ≤ 1 / 6 := hdrift_b
  have hdecay : ∀ d < t - a, e (a + d) ≤ exp (-((2 : ℝ) ^ d)) := by
    intro d hd
    have hr : a + d < t := by omega
    have hge : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (a + d) / Λ := by
      rw [le_div_iff₀ hΛpos]
      calc (2 : ℝ) ^ d * Λ ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ a :=
            mul_le_mul_of_nonneg_left h2a (pow_nonneg (by norm_num) _)
        _ = (2 : ℝ) ^ (a + d) := by rw [← pow_add, add_comm]
    have hneg : -((2 : ℝ) ^ (a + d)) / Λ ≤ -((2 : ℝ) ^ d) := by
      simpa [neg_div] using neg_le_neg hge
    calc e (a + d) = u ^ (2 ^ (a + d)) := he_pow (a + d) hr
      _ ≤ exp (-((2 : ℝ) ^ (a + d)) / Λ) := by simpa [u] using u_pow_le hΛ1 (a + d)
      _ ≤ exp (-((2 : ℝ) ^ d)) := exp_le_exp.mpr hneg
  have hAtop : M0 * (2 : ℝ) ^ a * exp (ε * (a : ℝ) / 2) ≤ 8 * (n : ℝ) / D := by
    have hexp_le : exp (ε * (a : ℝ) / 2) ≤ 2 := by
      have hhalf : ε * (a : ℝ) / 2 ≤ 1 / 2 := by linarith
      exact (exp_le_exp.mpr hhalf).trans exp_half_le_two
    have hEight : M0 * (2 * Λ) * 2 = 8 * (n : ℝ) / D := by
      rw [hM0eq]
      field_simp; ring
    calc M0 * (2 : ℝ) ^ a * exp (ε * (a : ℝ) / 2)
        ≤ M0 * (2 * Λ) * exp (ε * (a : ℝ) / 2) := by
          have h1 : M0 * (2 : ℝ) ^ a ≤ M0 * (2 * Λ) :=
            mul_le_mul_of_nonneg_left h2a_le hM0nn
          exact mul_le_mul_of_nonneg_right h1 (exp_nonneg _)
      _ ≤ M0 * (2 * Λ) * 2 :=
          mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hM0nn (by positivity))
      _ = 8 * (n : ℝ) / D := hEight
  have hphase : ∀ s ≤ a, descentGrowth (n : ℝ) ε e M0 s ≤ 8 * (n : ℝ) / D := by
    intro s hs
    have hA := descentGrowth_phaseA hnR hε0 hM0nn he_nn s
    have hpow : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) hs
    have hexp : exp (ε * (s : ℝ) / 2) ≤ exp (ε * (a : ℝ) / 2) := by
      apply exp_le_exp.mpr
      have hsR : (s : ℝ) ≤ a := by exact_mod_cast hs
      have : ε * (s : ℝ) ≤ ε * (a : ℝ) := mul_le_mul_of_nonneg_left hsR hε0
      exact div_le_div_of_nonneg_right this (by norm_num)
    have hmono : M0 * (2 : ℝ) ^ s * exp (ε * (s : ℝ) / 2) ≤
        M0 * (2 : ℝ) ^ a * exp (ε * (a : ℝ) / 2) := by
      have h1 : M0 * (2 : ℝ) ^ s ≤ M0 * (2 : ℝ) ^ a :=
        mul_le_mul_of_nonneg_left hpow hM0nn
      calc M0 * (2 : ℝ) ^ s * exp (ε * (s : ℝ) / 2)
          ≤ M0 * (2 : ℝ) ^ a * exp (ε * (s : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h1 (exp_nonneg _)
        _ ≤ M0 * (2 : ℝ) ^ a * exp (ε * (a : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg hM0nn (pow_nonneg (by norm_num) _))
    exact (hA.trans hmono).trans hAtop
  have hbase : descentGrowth (n : ℝ) ε e M0 a ≤ 8 * (n : ℝ) / D := hphase a le_rfl
  have h8γ : 8 * (n : ℝ) / D ≤ γ * (n : ℝ) / D :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ γ) hnR.le) hD.le
  have hgrowth : ∀ s ≤ t, descentGrowth (n : ℝ) ε e M0 s ≤ γ * (n : ℝ) / D := by
    intro s hs
    by_cases hsa : s ≤ a
    · exact (hphase s hsa).trans h8γ
    · have hlt : a < s := by omega
      let d : ℕ := s - a
      have hd : d ≤ t - a := by omega
      have hs_eq : a + d = s := Nat.add_sub_of_le hlt.le
      have hB := descentGrowth_phaseB (n := (n : ℝ)) (ε := ε) (γ := γ) (D := D) (M0 := M0)
        (e := e) (a := a) (N := t - a) hnR hD hε0 hγ24 hM0nn he_nn hbase hdrift hdecay d hd
      have henv := envelope_le (n := (n : ℝ)) (D := D) (γ := γ) (δ := γ / D + ε) (d := d)
        hnR hD (hdrift d hd) hγ24
      have hBd : descentGrowth (n : ℝ) ε e M0 (a + d) ≤ γ * (n : ℝ) / D := hB.trans henv
      rw [hs_eq] at hBd
      exact hBd
  have hlo_eq : (1 - w) * n / 2 = n / 2 - 2 * γ ^ 2 * n / D := by
    rw [show w = 4 * γ ^ 2 / D from rfl]
    field_simp; ring
  have hhi_eq : (1 + w) * n / 2 = n / 2 + 2 * γ ^ 2 * n / D := by
    rw [show w = 4 * γ ^ 2 / D from rfl]
    field_simp; ring
  have hhalf : n / 2 ≤ und y := by
    have h4 : (4 : ℝ) ≤ Λ := by linarith [show (4 : ℝ) ≤ C by norm_num, hCD]
    have h2 : 2 / Λ ≤ (1 : ℝ) / 2 := by
      rw [div_le_div_iff₀ hΛpos (by norm_num)]
      linarith only [h4]
    have hcoef : (1 : ℝ) / 2 ≤ 1 - 2 / Λ := by linarith only [h2]
    calc n / 2 = n * ((1 : ℝ) / 2) := by ring
      _ ≤ n * (1 - 2 / Λ) := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg n)
      _ ≤ und y := by
          rw [show n * (1 - 2 / Λ) = n * (1 - 2 / ratioLam x) by simp [Λ]]
          exact hUlo
  have he0u : e 0 = u := by
    have : u ^ (2 ^ (0 : ℕ)) = u := by simp
    simpa [e, this] using (max_eq_left hwu : max u w = u)
  have hupper0 : und y ≤ (1 + e 0) * n / 2 := by
    rw [he0u]
    have hid : n * (1 - 1 / (2 * Λ)) = (1 + u) * n / 2 := by
      rw [show u = 1 - 1 / Λ from rfl]
      field_simp; ring
    have : n * (1 - 1 / (2 * ratioLam x)) = n * (1 - 1 / (2 * Λ)) := by simp [Λ]
    calc und y ≤ n * (1 - 1 / (2 * ratioLam x)) := hUhi
      _ = n * (1 - 1 / (2 * Λ)) := this
      _ = (1 + u) * n / 2 := hid
  have hdrop : 0 ≤ 2 * γ ^ 2 * n / D :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg γ))
      (Nat.cast_nonneg n)) hD.le
  let G : ℕ → Set (Config n k) := fun s =>
    {z | (maxCount z : ℝ) ≤ descentGrowth (n : ℝ) ε e M0 s ∧
      n / 2 - 2 * γ ^ 2 * n / D ≤ und z ∧
      und z ≤ (1 + e s) * n / 2}
  have hyG0 : y ∈ G 0 := by
    refine ⟨?_, ?_, hupper0⟩
    · simpa [descentGrowth_zero] using hmaxM0
    · exact (sub_le_self _ hdrop).trans hhalf
  have hexpℓ : exp (-ℓ) = 1 / (n : ℝ) ^ 3 := by
    rw [show ℓ = 3 * log (n : ℝ) from rfl]
    exact exp_neg_three_log hnR
  let mcol : Fin k := ⟨0, hkpos⟩
  have hround : ∀ r ≤ t, ∀ z : Config n k, z ∈ G r →
      miss (G (r + 1)) 1 z ≤ 5 / (n : ℝ) ^ 2 := by
    intro r hr z hz
    let M : ℝ := descentGrowth (n : ℝ) ε e M0 r
    have hMnn : 0 ≤ M := descentGrowth_nonneg hnR hε0 hM0nn he_nn r
    have hMge : M0 ≤ M := descentGrowth_ge hnR hε0 hM0nn he_nn r
    have hMγ : M ≤ γ * n / D := hgrowth r hr
    have h6M : 6 * ℓ ≤ 2 * M := by
      have : 2 * M0 ≤ 2 * M := mul_le_mul_of_nonneg_left hMge (by norm_num)
      linarith only [h6M0, this]
    have hdevC : 2 * √(2 * ℓ * M) ≤ ε * M := rel_dev_le hℓ0 hM0pos hMge rfl
    have hmem : ∀ z' : Config n k, Good ℓ mcol z z' → z' ∈ G (r + 1) := by
      intro z' hG
      have hlo : (1 - w) * n / 2 ≤ und z := by simpa [hlo_eq] using hz.2.1
      have hstep := descent_step_of_good (ℓ := ℓ) (γ := γ) (D := D) (M := M) (e := e r)
        (w := w) (e' := e (r + 1)) (ε := ε) (m := mcol) (y := z) (z := z')
        hnR hkpos hℓ0 h6n hγ hD hMnn (he_nn r) hw0 hε0 hz.1 hMγ hlo hz.2.2
        (hemargin r) hdevU hdevD h6M hdevC (he_next r) hG
      refine ⟨?_, hstep.2.1, hstep.2.2⟩
      rw [descentGrowth_succ]
      simpa [M] using hstep.1
    calc miss (G (r + 1)) 1 z ≤ ((k : ℝ) + 4) * exp (-ℓ) :=
          miss_round_le hℓpos mcol z (G (r + 1)) hmem
      _ = ((k : ℝ) + 4) / (n : ℝ) ^ 3 := by rw [hexpℓ]; ring
      _ ≤ 5 / (n : ℝ) ^ 2 := bad_prob_le hn2 hk_le
  have hfive : 0 ≤ 5 / (n : ℝ) ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  have hescape : ∀ s ≤ t, miss (G s) s y ≤ (s : ℝ) * (5 / (n : ℝ) ^ 2) := by
    intro s hs
    refine expList_escape step hfive s G y hyG0 ?_
    intro r hr z hz
    have hrle : r ≤ t := by omega
    rw [← descent_miss_one_eq]
    exact hround r hrle z hz
  have h5log : (5 : ℝ) * log n ≤ (n : ℝ) := by
    have h5 : (5 : ℝ) ≤ C ^ 6 * (k : ℝ) ^ 6 := by
      calc (5 : ℝ) ≤ (8 : ℝ) ^ 6 := by norm_num
        _ ≤ C ^ 6 := hC6
        _ = C ^ 6 * 1 := by ring
        _ ≤ C ^ 6 * (k : ℝ) ^ 6 := mul_le_mul_of_nonneg_left hkpow (pow_nonneg hCpos.le 6)
    calc (5 : ℝ) * log n ≤ (C ^ 6 * (k : ℝ) ^ 6) * log n :=
          mul_le_mul_of_nonneg_right h5 hlognn
      _ = (C * (k : ℝ)) ^ 6 * log n := by rw [mul_pow]
      _ ≤ (n : ℝ) := hpoly
  have hprob : (t : ℝ) * (5 / (n : ℝ) ^ 2) ≤ C / (n : ℝ) := by
    have ht5 : (t : ℝ) * 5 ≤ C * (n : ℝ) := by
      calc (t : ℝ) * 5 ≤ (C * log n) * 5 := mul_le_mul_of_nonneg_right ht_log (by norm_num)
        _ = C * (5 * log n) := by ring
        _ ≤ C * (n : ℝ) := mul_le_mul_of_nonneg_left h5log hCpos.le
    calc (t : ℝ) * (5 / (n : ℝ) ^ 2) = ((t : ℝ) * 5) / (n : ℝ) ^ 2 := by ring
      _ ≤ (C * (n : ℝ)) / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right ht5 (sq_nonneg _)
      _ = C / (n : ℝ) := by field_simp
  have hsub : ∀ s ≤ t, G s ⊆ {z | (maxCount z : ℝ) ≤ γ * n / D} := by
    intro s hs z hz
    exact hz.1.trans (hgrowth s hs)
  have hsubT : G t ⊆ {z | (maxCount z : ℝ) ≤ γ * n / D ∧
      |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} := by
    intro z hz
    refine ⟨hz.1.trans (hgrowth t le_rfl), ?_⟩
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : -(2 * γ ^ 2 * n / D) = (n / 2 - 2 * γ ^ 2 * n / D) - n / 2 := by ring
      rw [this]
      exact sub_le_sub_right hz.2.1 _
    · have hhi : und z ≤ (1 + w) * n / 2 := by
        have hhi0 : und z ≤ (1 + e t) * n / 2 := hz.2.2
        rwa [het] at hhi0
      have hdiff : (1 + w) * n / 2 - n / 2 = 2 * γ ^ 2 * n / D := by
        rw [hhi_eq]; ring
      calc und z - n / 2 ≤ (1 + w) * n / 2 - n / 2 := sub_le_sub_right hhi _
        _ = 2 * γ ^ 2 * n / D := hdiff
  refine ⟨t, ht_log, ?_, ?_⟩
  · intro s hs
    calc miss {z | (maxCount z : ℝ) ≤ γ * n / md x} s y
        ≤ miss (G s) s y := by simpa [D] using miss_mono (hsub s hs) s y
      _ ≤ (s : ℝ) * (5 / (n : ℝ) ^ 2) := hescape s hs
      _ ≤ (t : ℝ) * (5 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hfive
      _ ≤ C / n := hprob
  · calc miss {z | (maxCount z : ℝ) ≤ γ * n / md x ∧
          |und z - n / 2| ≤ 2 * γ ^ 2 * n / md x} t y
        ≤ miss (G t) t y := by simpa [D] using miss_mono hsubT t y
      _ ≤ (t : ℝ) * (5 / (n : ℝ) ^ 2) := hescape t le_rfl
      _ ≤ C / n := hprob

end Undecided.Plurality
