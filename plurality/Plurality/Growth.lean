import Plurality.Expectation
import Plurality.Quantities
import Plurality.Tail

/-!
# Growth of the bias in one round (Lemmas 3.3, 3.4, 3.5)

Fix a coloring `x` with a unique plurality color `m`, and write `c = count x`,
`s = s(c)`, `α = α(c)`, `γ = γ(c)`.

* **Lemma 3.3** (`lemma_3_3`): for every other color `j`, the gap
  `C_{m,t+1} - C_{j,t+1}` exceeds `s (1 + γ + c_m α / (2s))` except with
  probability `exp(-c_m α²/25)`. Its expectation is at least
  `s(1 + γ) + c_m α` (from Lemmas 3.1 and 3.2), and Bernstein's inequality
  (`Dynamics.avg_bernstein`, with `b = 2` and variance at most `3 c_m`) bounds
  the lower deviation by `c_m α / 2`.
* **Lemma 3.4** (`lemma_3_4`): `C_{m,t+1} > c_m (1 + γ + α/2)` except with
  probability `exp(-c_m α²/11)`, by the multiplicative Chernoff bound.
* **Lemma 3.5** (`lemma_3_5`): if `λ n ≤ c_m ≤ (2/3) n` and
  `s ≥ 22 √((1/λ) n log n)`, the bias grows by a factor `1 + λ/6` against each
  color, and the plurality grows, except with probability `1/n²` each.
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

variable {n k : ℕ}

/-- `n` times the probability of adopting `j` is `μⱼ(c)`. -/
lemma n_mul_avg_adopt (hn : 1 ≤ n) (x : Config n k) (j : Fin k) :
    (n : ℝ) * avg (adopt maj3 x j) = mu n (count x) j := by
  rw [← expected_count_stepWith hn]
  exact expected_count hn x j

lemma avg_adopt_nonneg (x : Config n k) (j : Fin k) : 0 ≤ avg (adopt maj3 x j) :=
  avg_nonneg fun s => by rcases adopt_zero_one maj3 x j s with h | h <;> simp [h]

lemma avg_adopt_le_one (hn : 1 ≤ n) (x : Config n k) (j : Fin k) :
    avg (adopt maj3 x j) ≤ 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  calc avg (adopt maj3 x j) ≤ avg (fun _ : Fin n × Fin n × Fin n => (1 : ℝ)) :=
        avg_le_avg fun s => by rcases adopt_zero_one maj3 x j s with h | h <;> simp [h]
    _ = 1 := avg_const 1

lemma maxc_pos (hn : 1 ≤ n) (x : Config n k) : 1 ≤ maxc (count x) := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have := sum_count x; simp at this; omega
    · exact hk
  by_contra h
  have hle : ∀ j, count x j = 0 := fun j => by have := le_maxc (count x) j; omega
  have := sum_count x
  simp [hle] at this
  omega

/-- A unique plurality color has a positive bias. -/
lemma bias_pos (hn : 1 ≤ n) (x : Config n k) {m : Fin k} (hM : argmaxSet (count x) = {m}) :
    1 ≤ bias (count x) := by
  rw [bias_of_singleton hM]
  have hmax := maxc_pos hn x
  have : secondc (count x) < maxc (count x) := by
    unfold secondc
    rcases (univ.filter fun h => count x h ≠ maxc (count x)).eq_empty_or_nonempty with he | hne
    · rw [he]; simp only [sup_empty, bot_eq_zero']; omega
    · obtain ⟨h, hh, hsup⟩ := exists_mem_eq_sup _ hne (count x)
      rw [hsup]
      exact lt_of_le_of_ne (le_maxc _ h) (mem_filter.mp hh).2
  omega

/-- The shorthand facts about `c_m`, `s`, `α`, `γ` used throughout. -/
structure Setting (n : ℕ) (x : Config n k) (m : Fin k) : Prop where
  hn : 1 ≤ n
  hM : argmaxSet (count x) = {m}

section
variable {x : Config n k} {m : Fin k}

lemma Setting.cm_eq (hS : Setting n x m) : count x m = maxc (count x) :=
  argmaxSet_eq_singleton hS.hM

lemma Setting.alpha_nonneg (_hS : Setting n x m) : 0 ≤ alpha n (count x) :=
  (lemma_3_1_b (sum_count x)).1

lemma Setting.alpha_le_quarter (_hS : Setting n x m) : alpha n (count x) ≤ 1 / 4 :=
  (lemma_3_1_b (sum_count x)).2.trans (min_le_right _ _)

lemma Setting.alpha_le_bias (_hS : Setting n x m) :
    alpha n (count x) ≤ (bias (count x) : ℝ) / n :=
  (lemma_3_1_b (sum_count x)).2.trans (min_le_left _ _)

lemma Setting.gamma_nonneg (hS : Setting n x m) : 0 ≤ gamma n (count x) :=
  (lemma_3_1_c (sum_count x) hS.hn).1

lemma Setting.gamma_le (hS : Setting n x m) : gamma n (count x) ≤ 1 / 8 :=
  (lemma_3_1_c (sum_count x) hS.hn).2

end

/-- **Lemma 3.3 (increasing rate of the bias).** If `M(c) = {m}` then for
every other color `j`,
`P(C_{m,t+1} - C_{j,t+1} ≤ s(c)(1 + γ(c) + c_m α(c)/(2 s(c)))) ≤ exp(-c_m α(c)²/25)`. -/
theorem lemma_3_3 (hn : 1 ≤ n) (x : Config n k) {m j : Fin k}
    (hM : argmaxSet (count x) = {m}) (hj : j ≠ m) :
    avg (fun r : Tgt3 n =>
        if (count (step x r) m : ℝ) - count (step x r) j
            ≤ bias (count x) * (1 + gamma n (count x)
                + count x m * alpha n (count x) / (2 * bias (count x)))
        then (1 : ℝ) else 0)
      ≤ exp (-(count x m * alpha n (count x) ^ 2 / 25)) := by
  have hS : Setting n x m := ⟨hn, hM⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set s : ℝ := ((bias (count x) : ℕ) : ℝ) with hs
  set α := alpha n (count x) with hα
  set γ' := gamma n (count x) with hγ
  set cm : ℝ := ((count x m : ℕ) : ℝ) with hcm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ s := by rw [hs]; exact_mod_cast bias_pos hn x hM
  have hcm1 : (1 : ℝ) ≤ cm := by
    have h1 := hS.cm_eq
    have h2 := maxc_pos hn x
    rw [hcm]
    exact_mod_cast (show 1 ≤ count x m by omega)
  have hα0 := hS.alpha_nonneg
  have hα4 := hS.alpha_le_quarter
  have hαs := hS.alpha_le_bias
  have hγ0 := hS.gamma_nonneg
  have hγ8 := hS.gamma_le
  have hmM : m ∈ argmaxSet (count x) := by rw [hM]; exact mem_singleton_self m
  have hcmax : (count x m : ℝ) = maxc (count x) := by exact_mod_cast hS.cm_eq
  -- the gap between `m` and `j` in the current coloring
  have hgap : (count x j : ℝ) + s ≤ cm := by
    have := add_bias_le hS.cm_eq hj
    have : ((count x j + bias (count x) : ℕ) : ℝ) ≤ maxc (count x) := by exact_mod_cast this
    push_cast at this
    rw [hcm, hcmax]
    exact this
  -- expectations from Lemma 3.2
  have hμm : mu n (count x) m = cm * (1 + γ' + α) := lemma_3_2_a hmM
  have hμj : mu n (count x) j = count x j * (1 + γ' + α - (cm - count x j) / n) := by
    rw [lemma_3_2_b hn j, hcm, hcmax]
  -- per-node variables `Y = 𝟙[adopt j] - 𝟙[adopt m]`, whose sum is `C_j' - C_m'`
  let Y : Fin n → Fin n × Fin n × Fin n → ℝ := fun _ t => adopt maj3 x j t - adopt maj3 x m t
  have hsumY (r : Tgt3 n) : ∑ v, Y v (r v) = (count (step x r) j : ℝ) - count (step x r) m := by
    change _ = (count (stepWith maj3 x r) j : ℝ) - count (stepWith maj3 x r) m
    rw [count_stepWith_eq_sum, count_stepWith_eq_sum, ← sum_sub_distrib]
  have hEY : ∑ v, avg (Y v) = mu n (count x) j - mu n (count x) m := by
    simp only [Y, avg_sub, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [n_mul_avg_adopt hn, n_mul_avg_adopt hn]
  -- `𝔼[C_m' - C_j'] ≥ s(1 + γ) + c_m α`
  have hdrift : mu n (count x) m - mu n (count x) j ≥ s * (1 + γ') + cm * α := by
    rw [hμm, hμj]
    have hcj0 : (0 : ℝ) ≤ count x j := Nat.cast_nonneg _
    have h1 : 0 ≤ (cm - count x j - s) * (1 + γ') := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (count x j : ℝ) * ((cm - count x j - s) / n) := mul_nonneg hcj0 (by
      apply div_nonneg _ hn0.le; linarith)
    have h3 : 0 ≤ (count x j : ℝ) * (s / n - α) := mul_nonneg hcj0 (by linarith)
    have e : (cm - count x j - s) / n = (cm - count x j) / n - s / n := by ring
    rw [e] at h2
    nlinarith
  -- Bernstein's inequality with `b = 2` and variance at most `3 c_m`
  have hYb (v : Fin n) (t : Fin n × Fin n × Fin n) : Y v t - avg (Y v) ≤ 2 := by
    simp only [Y, avg_sub]
    have := avg_adopt_nonneg x j
    have := avg_adopt_le_one hn x m
    rcases adopt_zero_one maj3 x j t with h | h <;>
      rcases adopt_zero_one maj3 x m t with h' | h' <;>
      rw [h, h'] <;> linarith
  have hYsq (v : Fin n) (t : Fin n × Fin n × Fin n) :
      Y v t ^ 2 = adopt maj3 x j t + adopt maj3 x m t := by
    simp only [Y, adopt]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hj
    all_goals norm_num
  have hvar : ∑ v, variance (Y v) ≤ 3 * cm := by
    calc ∑ v, variance (Y v) ≤ ∑ v : Fin n, avg (fun t => Y v t ^ 2) :=
          sum_le_sum fun v _ => variance_le_avg_sq (Y v)
      _ = ∑ _v : Fin n, (avg (adopt maj3 x j) + avg (adopt maj3 x m)) := by
          refine sum_congr rfl fun v _ => ?_
          rw [← avg_add]
          exact congrArg avg (funext (hYsq v))
      _ = mu n (count x) j + mu n (count x) m := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
            n_mul_avg_adopt hn, n_mul_avg_adopt hn]
      _ ≤ 3 * cm := by
          have hjm : mu n (count x) j ≤ mu n (count x) m := by
            rw [hμm, hμj]
            have hcj0 : (0 : ℝ) ≤ count x j := Nat.cast_nonneg _
            have : (0 : ℝ) ≤ (cm - count x j) / n := div_nonneg (by linarith) hn0.le
            nlinarith
          rw [hμm] at hjm ⊢
          nlinarith
  have hσ0 : (0 : ℝ) < 3 * cm := by linarith
  have hlam : 0 ≤ cm * α / 2 := by positivity
  have hB := avg_bernstein Y (by norm_num : (0 : ℝ) < 2) hYb hvar hσ0 hlam
  -- event inclusion
  have hevent : ∀ r : Tgt3 n,
      (if (count (step x r) m : ℝ) - count (step x r) j ≤ s * (1 + γ' + cm * α / (2 * s))
        then (1 : ℝ) else 0)
        ≤ if (∑ v, avg (Y v)) + cm * α / 2 ≤ ∑ v, Y v (r v) then 1 else 0 := by
    intro r
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      rw [hsumY, hEY]
      have e : s * (1 + γ' + cm * α / (2 * s)) = s * (1 + γ') + cm * α / 2 := by
        field_simp
      rw [e] at h1
      linarith
    · norm_num
    · exact le_rfl
  calc _ ≤ avg (fun r : Tgt3 n =>
          if (∑ v, avg (Y v)) + cm * α / 2 ≤ ∑ v, Y v (r v) then (1 : ℝ) else 0) :=
        avg_le_avg hevent
    _ ≤ exp (-((cm * α / 2) ^ 2 / (2 * (3 * cm) * (1 + 2 * (cm * α / 2) / (3 * (3 * cm)))))) :=
        hB
    _ ≤ exp (-(cm * α ^ 2 / 25)) := by
        apply exp_le_exp.mpr
        have hcm0 : 0 < cm := by linarith
        have hα0' : 0 ≤ α := hα0
        have h9 : (9 : ℝ) + α ≠ 0 := by linarith
        have h72 : (72 : ℝ) + 8 * α ≠ 0 := by linarith
        have e : (cm * α / 2) ^ 2 / (2 * (3 * cm) * (1 + 2 * (cm * α / 2) / (3 * (3 * cm))))
            = cm * α ^ 2 / (24 + 8 / 3 * α) := by
          field_simp
          ring
        rw [e, neg_le_neg_iff]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith

/-- **Lemma 3.4.** If `M(c) = {m}` then
`P(C_{m,t+1} ≤ c_m (1 + γ(c) + α(c)/2)) ≤ exp(-c_m α(c)²/11)`. -/
theorem lemma_3_4 (hn : 1 ≤ n) (x : Config n k) {m : Fin k}
    (hM : argmaxSet (count x) = {m}) :
    avg (fun r : Tgt3 n =>
        if (count (step x r) m : ℝ) ≤ count x m * (1 + gamma n (count x) + alpha n (count x) / 2)
        then (1 : ℝ) else 0)
      ≤ exp (-(count x m * alpha n (count x) ^ 2 / 11)) := by
  have hS : Setting n x m := ⟨hn, hM⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set α := alpha n (count x)
  set γ' := gamma n (count x)
  set cm : ℝ := ((count x m : ℕ) : ℝ) with hcm
  have hα0 := hS.alpha_nonneg
  have hα4 := hS.alpha_le_quarter
  have hγ0 := hS.gamma_nonneg
  have hγ8 := hS.gamma_le
  have hmM : m ∈ argmaxSet (count x) := by rw [hM]; exact mem_singleton_self m
  have hμ : ∑ v : Fin n, avg (fun t => adopt maj3 x m t) = cm * (1 + γ' + α) := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, n_mul_avg_adopt hn]
    exact lemma_3_2_a hmM
  have hD : 0 < 1 + γ' + α := by linarith
  set δ : ℝ := α / (2 * (1 + γ' + α)) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ < 1 := by rw [hδ, div_lt_one (by positivity)]; linarith
  have hC := chernoff_lower (fun (_ : Fin n) t => adopt maj3 x m t)
    (fun _ t => adopt_zero_one maj3 x m t) hδ0 hδ1
  rw [hμ] at hC
  have hk : (1 - δ) * (cm * (1 + γ' + α)) = cm * (1 + γ' + α / 2) := by
    rw [hδ]; field_simp; ring
  rw [hk] at hC
  have hevent : ∀ r : Tgt3 n,
      (if (count (step x r) m : ℝ) ≤ cm * (1 + γ' + α / 2) then (1 : ℝ) else 0)
        = if ∑ v, adopt maj3 x m (r v) ≤ cm * (1 + γ' + α / 2) then 1 else 0 := by
    intro r
    change (if (count (stepWith maj3 x r) m : ℝ) ≤ _ then (1 : ℝ) else 0) = _
    rw [count_stepWith_eq_sum]
  simp_rw [hevent]
  refine hC.trans (exp_le_exp.mpr ?_)
  rw [neg_le_neg_iff, hδ]
  have hcm0 : 0 ≤ cm := Nat.cast_nonneg _
  have e : (α / (2 * (1 + γ' + α))) ^ 2 * (cm * (1 + γ' + α)) / 2
      = cm * α ^ 2 / (8 * (1 + γ' + α)) := by
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

lemma exp_neg_two_log (hn : 1 ≤ n) : exp (-(2 * Real.log n)) = 1 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [exp_neg, show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num, exp_log (by positivity), one_div]

/-- **Lemma 3.5 (large plurality and large bias).** If `M(c) = {m}`,
`0 < λ ≤ 2/3`, `λ n ≤ c_m ≤ (2/3) n` and `s(c) ≥ 22 √((1/λ) n log n)`, then for
every other color `j`, `P(C_{m,t+1} - C_{j,t+1} ≤ s(c)(1 + λ/6)) ≤ 1/n²`, and
`P(C_{m,t+1} ≤ c_m) ≤ 1/n²`. -/
theorem lemma_3_5 (hn : 1 ≤ n) (x : Config n k) {m : Fin k}
    (hM : argmaxSet (count x) = {m}) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 2 / 3)
    (hcm0 : lam * n ≤ count x m) (hcm1 : (count x m : ℝ) ≤ 2 / 3 * n)
    (hs : 22 * √((1 / lam) * n * Real.log n) ≤ bias (count x)) :
    (∀ j, j ≠ m →
      avg (fun r : Tgt3 n =>
          if (count (step x r) m : ℝ) - count (step x r) j ≤ bias (count x) * (1 + lam / 6)
          then (1 : ℝ) else 0) ≤ 1 / (n : ℝ) ^ 2) ∧
    avg (fun r : Tgt3 n => if (count (step x r) m : ℝ) ≤ count x m then (1 : ℝ) else 0)
      ≤ 1 / (n : ℝ) ^ 2 := by
  have hS : Setting n x m := ⟨hn, hM⟩
  set s : ℝ := ((bias (count x) : ℕ) : ℝ) with hs_def
  set α := alpha n (count x) with hα_def
  set γ' := gamma n (count x)
  set cm : ℝ := ((count x m : ℕ) : ℝ) with hcm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ s := by rw [hs_def]; exact_mod_cast bias_pos hn x hM
  have hγ0 := hS.gamma_nonneg
  have hcmax : cm = maxc (count x) := by rw [hcm]; exact_mod_cast hS.cm_eq
  have hαeq : α = ((n : ℝ) - cm) * s / (n : ℝ) ^ 2 := by rw [hα_def, alpha, hcmax]
  -- (5): `c_m α / (2 s) ≥ λ/6`
  have h5 : lam / 6 ≤ cm * α / (2 * s) := by
    rw [hαeq]
    have e : cm * (((n : ℝ) - cm) * s / (n : ℝ) ^ 2) / (2 * s)
        = cm * ((n : ℝ) - cm) / (2 * n ^ 2) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have : (n : ℝ) / 3 ≤ n - cm := by linarith
    nlinarith [mul_le_mul hcm0 this (by positivity) (by nlinarith)]
  -- (6): `c_m α² / 25 ≥ 2 log n`
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hs2 : 484 * ((1 / lam) * n * Real.log n) ≤ s ^ 2 := by
    have hsq := Real.sq_sqrt (show 0 ≤ (1 / lam) * n * Real.log n by positivity)
    have hle : (22 * √((1 / lam) * n * Real.log n)) ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs 2
    nlinarith
  have h6 : 2 * Real.log n ≤ cm * α ^ 2 / 25 := by
    rw [hαeq]
    have hnc : (n : ℝ) / 3 ≤ n - cm := by linarith
    have e : cm * (((n : ℝ) - cm) * s / (n : ℝ) ^ 2) ^ 2 / 25
        = cm * ((n : ℝ) - cm) ^ 2 * s ^ 2 / (25 * (n : ℝ) ^ 4) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hsq : ((n : ℝ) / 3) ^ 2 ≤ ((n : ℝ) - cm) ^ 2 := pow_le_pow_left₀ (by positivity) hnc 2
    have hlam_s : lam * s ^ 2 ≥ 484 * n * Real.log n := by
      have := mul_le_mul_of_nonneg_left hs2 hlam0.le
      field_simp at this
      nlinarith
    -- `c_m (n-c_m)² s² ≥ λ n (n/3)² s² ≥ (484/9) n⁴ log n`
    have hcm0' : 0 ≤ cm := by linarith [mul_nonneg hlam0.le hn0.le]
    have step1 : cm * ((n : ℝ) / 3) ^ 2 * s ^ 2 ≤ cm * ((n : ℝ) - cm) ^ 2 * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq hcm0'
      exact mul_le_mul_of_nonneg_right this (sq_nonneg s)
    have step2 : lam * n * ((n : ℝ) / 3) ^ 2 * s ^ 2 ≤ cm * ((n : ℝ) / 3) ^ 2 * s ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
      exact mul_le_mul_of_nonneg_right hcm0 (sq_nonneg _)
    have step3 : 484 * n * Real.log n * ((n : ℝ) / 3) ^ 2 * n
        ≤ lam * n * ((n : ℝ) / 3) ^ 2 * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hlam_s (show 0 ≤ (n : ℝ) * ((n : ℝ) / 3) ^ 2 by positivity)
      nlinarith
    have h4 : 0 ≤ (n : ℝ) ^ 4 * Real.log n := by positivity
    linarith
  have hprob : exp (-(cm * α ^ 2 / 25)) ≤ 1 / (n : ℝ) ^ 2 := by
    rw [← exp_neg_two_log hn]
    exact exp_le_exp.mpr (by linarith)
  constructor
  · intro j hj
    refine le_trans ?_ ((lemma_3_3 hn x hM hj).trans hprob)
    refine avg_le_avg fun r => ?_
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      have : s * (1 + lam / 6) ≤ s * (1 + γ' + cm * α / (2 * s)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
      linarith
    · norm_num
    · exact le_rfl
  · have h11 : exp (-(cm * α ^ 2 / 11)) ≤ exp (-(cm * α ^ 2 / 25)) := by
      apply exp_le_exp.mpr
      rw [neg_le_neg_iff]
      have : 0 ≤ cm * α ^ 2 := by
        have : 0 ≤ cm := by linarith [mul_nonneg hlam0.le hn0.le]
        positivity
      apply div_le_div_of_nonneg_left this (by norm_num) (by norm_num)
    refine le_trans ?_ (((lemma_3_4 hn x hM).trans h11).trans hprob)
    refine avg_le_avg fun r => ?_
    have hα0 := hS.alpha_nonneg
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      have : cm ≤ cm * (1 + γ' + α / 2) := by
        have : 0 ≤ cm := by linarith [mul_nonneg hlam0.le hn0.le]
        nlinarith
      linarith
    · norm_num
    · exact le_rfl

end Plurality
