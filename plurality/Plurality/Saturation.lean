import Plurality.Growth
import Plurality.Numerics

/-!
# The saturation phase (Lemmas 3.6 and 3.7)

Once the bias is at least `n/3`, the number `C̄ₘ = n - Cₘ` of nodes that do
not support the plurality color `m` decreases geometrically.

* **Lemma 3.6** (`lemma_3_6`): `(n - cₘ)(1 - cₘ²/n²) ≤ 𝔼[C̄_{m,t+1}] ≤ (n - cₘ)(1 - s cₘ/n²)`.
* **Lemma 3.7** (`lemma_3_7_i`, `lemma_3_7_ii`): if `s(c) ≥ n/3` then
  `C̄_{m,t+1} < (17/18)(n - cₘ)` except with probability `1/n²` as long as
  `n - cₘ ≥ n^{1/4} log n`; below that threshold, all nodes support `m`
  after one more round except with probability `n^{-1/5}`, and the threshold is
  not exceeded again except with probability `1/n²`.

The paper omits the proof of Lemma 3.7; the one here uses Lemma 3.6 with the
bounds `s cₘ ≥ n²/9` (first regime) and `s ≥ n - 2(n - cₘ)` (second regime),
the closed-form Chernoff upper tail `ThreeMajority.avg_tail_ge_log_le`, and
Markov's inequality. "Sufficiently large `n`" is made explicit as `log n ≥ 40`.
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

variable {n k : ℕ}

lemma one_le_of_log_pos (hL : 0 < Real.log n) : 1 ≤ n := by
  rcases n with _ | n
  · simp at hL
  · omega

/-- The per-node indicator of not adopting `m`. -/
def notAdopt (x : Config n k) (m : Fin k) (_ : Fin n) (t : Fin n × Fin n × Fin n) : ℝ :=
  1 - adopt maj3 x m t

lemma notAdopt_zero_one (x : Config n k) (m : Fin k) (v : Fin n) (t : Fin n × Fin n × Fin n) :
    notAdopt x m v t = 0 ∨ notAdopt x m v t = 1 := by
  unfold notAdopt
  rcases adopt_zero_one maj3 x m t with h | h <;> simp [h]

lemma sum_notAdopt (x : Config n k) (m : Fin k) (r : Tgt3 n) :
    ∑ v, notAdopt x m v (r v) = (n : ℝ) - count (step x r) m := by
  change _ = (n : ℝ) - count (stepWith maj3 x r) m
  rw [count_stepWith_eq_sum]
  simp [notAdopt, sum_sub_distrib]

lemma sum_avg_notAdopt (hn : 1 ≤ n) (x : Config n k) (m : Fin k) :
    ∑ v, avg (notAdopt x m v) = (n : ℝ) - mu n (count x) m := by
  haveI : Nonempty (Fin n × Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)⟩
  have h (v : Fin n) : avg (notAdopt x m v) = 1 - avg (adopt maj3 x m) := by
    unfold notAdopt
    rw [avg_sub, avg_const]
  simp_rw [h]
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, n_mul_avg_adopt hn]

/-- The expected number of nodes not supporting `m` after one round. -/
lemma avg_count_compl (hn : 1 ≤ n) (x : Config n k) (m : Fin k) :
    avg (fun r : Tgt3 n => (n : ℝ) - count (step x r) m) = (n : ℝ) - mu n (count x) m := by
  haveI := tgt3_nonempty hn
  rw [avg_sub, avg_const, ← n_mul_avg_adopt hn, ← expected_count_stepWith hn]
  rfl

/-- **Lemma 3.6.** For every plurality color `m`,
`(n - cₘ)(1 - cₘ²/n²) ≤ μ̄ₘ(c) ≤ (n - cₘ)(1 - s(c) cₘ/n²)`, where
`μ̄ₘ(c) = 𝔼[C̄_{m,t+1} | Cₜ = c]`. -/
theorem lemma_3_6 (hn : 1 ≤ n) (x : Config n k) {m : Fin k} (hm : m ∈ argmaxSet (count x)) :
    ((n : ℝ) - count x m) * (1 - (count x m : ℝ) ^ 2 / (n : ℝ) ^ 2)
        ≤ avg (fun r : Tgt3 n => (n : ℝ) - count (step x r) m) ∧
      avg (fun r : Tgt3 n => (n : ℝ) - count (step x r) m)
        ≤ ((n : ℝ) - count x m) * (1 - (bias (count x) : ℝ) * count x m / (n : ℝ) ^ 2) := by
  rw [avg_count_compl hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcm : count x m = maxc (count x) := mem_argmaxSet.mp hm
  have hγ := (lemma_3_1_c (sum_count x) hn).1
  unfold gamma alpha at hγ
  rw [← hcm] at hγ
  have hsq : (count x m : ℝ) ^ 2 ≤ ∑ h, (count x h : ℝ) ^ 2 :=
    single_le_sum (f := fun h => (count x h : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ m)
  have hcm0 : (0 : ℝ) ≤ count x m := Nat.cast_nonneg _
  -- `n cₘ - ∑ cₕ² ≥ (n - cₘ) s`, i.e. `γ(c) ≥ 0`
  have hkey : ((n : ℝ) - count x m) * bias (count x)
      ≤ n * count x m - ∑ h, (count x h : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right (sub_nonneg.mpr hγ) (sq_nonneg (n : ℝ))
    rw [zero_mul] at this
    have e : (((n : ℝ) * count x m - ∑ h, (count x h : ℝ) ^ 2) / (n : ℝ) ^ 2
        - ((n : ℝ) - count x m) * bias (count x) / (n : ℝ) ^ 2) * (n : ℝ) ^ 2
        = ((n : ℝ) * count x m - ∑ h, (count x h : ℝ) ^ 2)
          - ((n : ℝ) - count x m) * bias (count x) := by
      field_simp
    have := sub_nonneg.mp (le_of_le_of_eq (le_of_eq_of_le rfl (sub_nonneg.mpr hγ)) rfl)
    nlinarith [sub_nonneg.mpr hγ, e]
  unfold mu
  constructor
  · rw [show ((n : ℝ) - count x m) * (1 - (count x m : ℝ) ^ 2 / (n : ℝ) ^ 2)
        = (n : ℝ) - count x m * (1 + (n * count x m - (count x m : ℝ) ^ 2) / (n : ℝ) ^ 2) by
      field_simp; ring]
    have : (n * count x m - ∑ h, (count x h : ℝ) ^ 2) / (n : ℝ) ^ 2
        ≤ (n * count x m - (count x m : ℝ) ^ 2) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  · rw [show ((n : ℝ) - count x m) * (1 - (bias (count x) : ℝ) * count x m / (n : ℝ) ^ 2)
        = (n : ℝ) - count x m * (1 + ((n : ℝ) - count x m) * bias (count x) / (n : ℝ) ^ 2) by
      field_simp; ring]
    have : ((n : ℝ) - count x m) * bias (count x) / (n : ℝ) ^ 2
        ≤ (n * count x m - ∑ h, (count x h : ℝ) ^ 2) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hkey (by positivity)
    nlinarith

/-- Every color other than `m` has at most `n - cₘ` nodes, so the bias is at
least `cₘ - (n - cₘ)`. -/
lemma bias_ge_of_singleton (x : Config n k) {m : Fin k} (hM : argmaxSet (count x) = {m}) :
    (count x m : ℝ) - ((n : ℝ) - count x m) ≤ bias (count x) := by
  have hcm := argmaxSet_eq_singleton hM
  have hsec : secondc (count x) + count x m ≤ n := by
    have hs := sum_count x
    rw [← add_sum_erase univ _ (mem_univ m)] at hs
    have : secondc (count x) ≤ ∑ h ∈ univ.erase m, count x h := by
      unfold secondc
      refine Finset.sup_le fun h hh => ?_
      have hne : h ≠ m := fun e => (mem_filter.mp hh).2 (e ▸ hcm)
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hne, mem_univ h⟩)
    omega
  rw [bias_of_singleton hM]
  have := secondc_le_maxc (count x)
  have : ((maxc (count x) - secondc (count x) : ℕ) : ℝ)
      = (maxc (count x) : ℝ) - secondc (count x) := by push_cast [Nat.cast_sub this]; ring
  rw [this, ← hcm]
  have : ((secondc (count x) + count x m : ℕ) : ℝ) ≤ n := by exact_mod_cast hsec
  push_cast at this
  linarith

/-- **Lemma 3.7, first regime.** If `M(c) = {m}`, `s(c) ≥ n/3` and
`n - cₘ ≥ n^{1/4} log n`, then `P(C̄_{m,t+1} ≥ (17/18)(n - cₘ)) ≤ 1/n²`. -/
theorem lemma_3_7_i (hL : 40 ≤ Real.log n) (x : Config n k) {m : Fin k}
    (hM : argmaxSet (count x) = {m}) (hs : (n : ℝ) / 3 ≤ bias (count x))
    (hu : (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n ≤ (n : ℝ) - count x m) :
    avg (fun r : Tgt3 n =>
        if 17 / 18 * ((n : ℝ) - count x m) ≤ (n : ℝ) - count (step x r) m then (1 : ℝ) else 0)
      ≤ 1 / (n : ℝ) ^ 2 := by
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  haveI : Nonempty (Fin n × Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log n with hLdef
  set u : ℝ := (n : ℝ) - count x m with hudef
  have hq : 1500 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [rpow_eq_exp hn]; exact fifteen_hundred_le_exp (by linarith)
  have hu1 : 1500 * L ≤ u := le_trans (mul_le_mul_of_nonneg_right hq (by linarith)) hu
  have hupos : 0 < u := by linarith
  -- `𝔼[C̄'] ≤ (8/9) u`
  have hmM : m ∈ argmaxSet (count x) := by rw [hM]; exact mem_singleton_self m
  have h36 := (lemma_3_6 hn x hmM).2
  rw [avg_count_compl hn] at h36
  have hsc : (1 : ℝ) / 9 ≤ (bias (count x) : ℝ) * count x m / (n : ℝ) ^ 2 := by
    have hsm : (bias (count x) : ℝ) ≤ count x m := by
      rw [argmaxSet_eq_singleton hM]; exact_mod_cast bias_le_maxc _
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hμ : ∑ v, avg (notAdopt x m v) ≤ 8 / 9 * u := by
    rw [sum_avg_notAdopt hn]
    calc (n : ℝ) - mu n (count x) m ≤ u * (1 - (bias (count x) : ℝ) * count x m / (n : ℝ) ^ 2) :=
          h36
      _ ≤ 8 / 9 * u := by nlinarith
  have hC := ThreeMajority.avg_tail_ge_log_le (notAdopt x m) (notAdopt_zero_one x m) hμ
    (by positivity) (by linarith : 8 / 9 * u ≤ 17 / 18 * u)
  simp only [threeMajority_avg_eq] at hC
  have hevent : (fun r : Tgt3 n =>
        if 17 / 18 * u ≤ (n : ℝ) - count (step x r) m then (1 : ℝ) else 0)
      = fun r : Tgt3 n => if 17 / 18 * u ≤ ∑ v, notAdopt x m v (r v) then (1 : ℝ) else 0 := by
    funext r; rw [sum_notAdopt]
  rw [hevent]
  refine hC.trans ?_
  rw [← exp_neg_two_log hn]
  apply exp_le_exp.mpr
  have hdiv : 17 / 18 * u / (8 / 9 * u) = 17 / 16 := by field_simp; norm_num
  rw [hdiv]
  have hlog := log_seventeen_sixteen
  nlinarith

/-- **Lemma 3.7, second regime.** If `M(c) = {m}`, `s(c) ≥ n/3` and
`n - cₘ < n^{1/4} log n`, then `P(C̄_{m,t+1} > 0) ≤ n^{-1/5}` and
`P(C̄_{m,t+1} ≥ n^{1/4} log n) ≤ 1/n²`. -/
theorem lemma_3_7_ii (hL : 40 ≤ Real.log n) (x : Config n k) {m : Fin k}
    (hM : argmaxSet (count x) = {m})
    (hu : (n : ℝ) - count x m < (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n) :
    avg (fun r : Tgt3 n => if 0 < (n : ℝ) - count (step x r) m then (1 : ℝ) else 0)
        ≤ (n : ℝ) ^ (-(1 / 5 : ℝ)) ∧
      avg (fun r : Tgt3 n =>
          if (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n ≤ (n : ℝ) - count (step x r) m
          then (1 : ℝ) else 0) ≤ 1 / (n : ℝ) ^ 2 := by
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  haveI : Nonempty (Fin n × Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log n with hLdef
  set u : ℝ := (n : ℝ) - count x m with hudef
  have hu0 : 0 ≤ u := by
    rw [hudef]; have := count_le x m; have : (count x m : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have hnexp : (n : ℝ) = exp L := natCast_eq_exp hn
  have hq : (n : ℝ) ^ (1 / 4 : ℝ) = exp (L / 4) := by rw [rpow_eq_exp hn, ← hLdef]; ring_nf
  rw [hq] at hu ⊢
  -- `𝔼[C̄'] ≤ 3u²/n ≤ 3 L² e^{-L/2}`
  have hmM : m ∈ argmaxSet (count x) := by rw [hM]; exact mem_singleton_self m
  have h36 := (lemma_3_6 hn x hmM).2
  rw [avg_count_compl hn] at h36
  have hsb := bias_ge_of_singleton x hM
  have hcm0 : (0 : ℝ) ≤ count x m := Nat.cast_nonneg _
  have hμ1 : ∑ v, avg (notAdopt x m v) ≤ 3 * u ^ 2 / n := by
    rw [sum_avg_notAdopt hn]
    refine h36.trans ?_
    rw [le_div_iff₀ hn0]
    have hsc : ((n : ℝ) - 2 * u) * count x m ≤ (bias (count x) : ℝ) * count x m :=
      mul_le_mul_of_nonneg_right (by rw [hudef]; linarith) hcm0
    have hcmu : (count x m : ℝ) = n - u := by rw [hudef]; ring
    rw [hcmu] at hsc ⊢
    have e : u * (1 - (bias (count x) : ℝ) * (n - u) / (n : ℝ) ^ 2) * n
        = u * n - u * ((bias (count x) : ℝ) * (n - u)) / n := by
      field_simp
    rw [sub_sub_cancel, e]
    have : u * (((n : ℝ) - 2 * u) * (n - u)) / n ≤ u * ((bias (count x) : ℝ) * (n - u)) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsc hu0) hn0.le
    have e2 : u * (((n : ℝ) - 2 * u) * (n - u)) / n = u * n - 3 * u ^ 2 + 2 * u ^ 3 / n := by
      field_simp; ring
    have : 0 ≤ 2 * u ^ 3 / n := by positivity
    linarith
  have hL0 : 0 < L := by linarith
  have hμ2 : 3 * u ^ 2 / n ≤ 3 * L ^ 2 * exp (-(L / 2)) := by
    have hu2 : u ^ 2 ≤ (exp (L / 4) * L) ^ 2 := pow_le_pow_left₀ hu0 hu.le 2
    rw [hnexp, div_le_iff₀ (exp_pos L)]
    have e : 3 * L ^ 2 * exp (-(L / 2)) * exp L = 3 * (exp (L / 4) * L) ^ 2 := by
      rw [mul_pow, ← exp_nat_mul, mul_assoc, ← exp_add]
      ring_nf
    rw [e]
    linarith
  constructor
  · -- Markov: `P(C̄' ≥ 1) ≤ 𝔼[C̄'] ≤ 3 L² e^{-L/2} ≤ e^{-L/5}`
    have hM1 := markov_one (notAdopt x m) (notAdopt_zero_one x m)
    have hevent : ∀ r : Tgt3 n,
        (if 0 < (n : ℝ) - count (step x r) m then (1 : ℝ) else 0)
          = if 1 ≤ ∑ v, notAdopt x m v (r v) then (1 : ℝ) else 0 := by
      intro r
      rw [sum_notAdopt]
      have hc := count_le (step x r) m
      by_cases h : count (step x r) m < n
      · have h1 : (count (step x r) m : ℝ) + 1 ≤ n := by exact_mod_cast h
        rw [if_pos (by linarith), if_pos (by linarith)]
      · have h1 : count (step x r) m = n := by omega
        rw [h1]; simp
    simp_rw [hevent]
    refine hM1.trans (hμ1.trans (hμ2.trans ?_))
    rw [rpow_eq_exp hn, ← hLdef]
    have hy : 12 ≤ 3 * L / 10 := by linarith
    have h34 := sq_mul_le_exp hy
    have e : 3 * L ^ 2 * exp (-(L / 2))
        = 3 * L ^ 2 * exp (-(1 / 5 : ℝ) * L) * exp (-(3 * L / 10)) := by
      rw [mul_assoc (3 * L ^ 2), ← exp_add]; ring_nf
    rw [e]
    have hpos : 0 < exp (-(1 / 5 : ℝ) * L) := exp_pos _
    have : 3 * L ^ 2 * exp (-(3 * L / 10)) ≤ 1 := by
      rw [exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)]
      nlinarith
    calc 3 * L ^ 2 * exp (-(1 / 5 : ℝ) * L) * exp (-(3 * L / 10))
        = exp (-(1 / 5 : ℝ) * L) * (3 * L ^ 2 * exp (-(3 * L / 10))) := by ring
      _ ≤ exp (-(1 / 5 : ℝ) * L) * 1 := mul_le_mul_of_nonneg_left this hpos.le
      _ = exp (-(1 / 5 : ℝ) * L) := mul_one _
  · -- Chernoff with `μ ≤ 3 L² e^{-L/2}` and threshold `k = e^{L/4} L`
    set μub : ℝ := 3 * L ^ 2 * exp (-(L / 2)) with hμub
    set kk : ℝ := exp (L / 4) * L with hkk
    have hμub0 : 0 < μub := by positivity
    have hexp34 : 3 * L ≤ exp (3 * L / 4) := by
      have := mul_le_exp (show (20 : ℝ) ≤ 3 * L / 4 by linarith)
      nlinarith
    have hratio : kk / μub = exp (3 * L / 4) / (3 * L) := by
      rw [hkk, hμub]
      have e : exp (L / 4) = exp (3 * L / 4) * exp (-(L / 2)) := by rw [← exp_add]; ring_nf
      rw [e]
      have : exp (-(L / 2)) ≠ 0 := (exp_pos _).ne'
      field_simp
    have hμk : μub ≤ kk := by
      have h1 : 1 ≤ kk / μub := by
        rw [hratio, le_div_iff₀ (by positivity), one_mul]
        exact hexp34
      exact (one_le_div hμub0).mp h1
    have hC := ThreeMajority.avg_tail_ge_log_le (notAdopt x m) (notAdopt_zero_one x m)
      (hμ1.trans hμ2) hμub0 hμk
    simp only [threeMajority_avg_eq] at hC
    have hevent : (fun r : Tgt3 n =>
          if kk ≤ (n : ℝ) - count (step x r) m then (1 : ℝ) else 0)
        = fun r : Tgt3 n => if kk ≤ ∑ v, notAdopt x m v (r v) then (1 : ℝ) else 0 := by
      funext r; rw [sum_notAdopt]
    rw [hevent]
    refine hC.trans ?_
    rw [← exp_neg_two_log hn]
    apply exp_le_exp.mpr
    -- `log (k/μ) = 3L/4 - log (3L) ≥ 2`
    have hlog : 2 ≤ Real.log (kk / μub) := by
      rw [hratio, Real.log_div (exp_pos _).ne' (by positivity), Real.log_exp]
      have := log_three_mul_le hL0
      linarith
    have hk2 : 2 * L ≤ kk := by
      have := fifteen_hundred_le_exp (show (10 : ℝ) ≤ L / 4 by linarith)
      rw [hkk]; nlinarith
    have hkk0 : 0 ≤ kk := by positivity
    nlinarith

end Plurality
