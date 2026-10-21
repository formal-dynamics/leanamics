import ThreeMajority.ManyOpinionsExpect
import Dynamics.Moments
import Dynamics.Chernoff

/-!
# One-round tails of 3-Majority with many colours (roadmap MAJ-12 (a))

Tools for the one-round estimates of BCNPT16 (Becchetti, Clementi, Natale, Pasquale, Trevisan,
*Stabilizing consensus with many opinions*, SODA 2016, arXiv:1508.06782), Section 3 and
Appendix B, for the model `stepCol` of `ThreeMajority.AnyStartModel`.

* Deterministic facts on supports: dead colours stay dead (`colourCount_runCol_eq_zero`); if
  every colour of a configuration with `j` colours has more than `n/j − m` agents, every colour
  has at most `n/j + (j − 1) m` (`colourCount_le_of_forall_lt`), hence
  `∑_b (c_b/n)² ≤ (n/j + (j − 1) m)/n` and a lower bound on the expected support
  (`le_avg_colourCount_stepCol`); the upper bound of Lemma 2.1 at a level `b ≥ c_a`
  (`avg_colourCount_stepCol_le_of_le`); the smallest of `j` supports adding up to `n` is at most
  `n/j − (1/(2j)) ∑_a |c_a − n/j|` (`inf'_colourCount_le`).
* Chernoff bounds for the new support of a colour at a threshold `k`
  (`avg_colourCount_stepCol_ge`, `avg_colourCount_stepCol_le_tail`): with the mean bounded by
  `μ`, the tail beyond `k` is at most `exp(−(k − μ)²/(k + μ))` (upper) or
  `exp(−(μ − k)²/(2μ))` (lower).
* Anti-concentration (`avg_abs_colourCount_stepCol_sub_ge`): the new support of a colour is at
  mean absolute distance at least `(9/256) σ` from any fixed value, `σ²` being the sum of the
  agents' variances (Paley–Zygmund, `avg_pz_zero_one`). This replaces the Central Limit Theorem
  of BCNPT16, Equation (4).
-/

namespace ThreeMajority

open Finset Dynamics

section Scalar

/-- From `D² j³ log n ≤ n`: `D √(j n log n) ≤ n/j`. -/
lemma mul_sqrt_le_div {n j : ℕ} {D : ℝ} (hD : 0 ≤ D) (hj : (0 : ℝ) < j)
    (h : D ^ 2 * (j : ℝ) ^ 3 * Real.log n ≤ n) :
    D * √(j * n * Real.log n) ≤ n / j := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [show D * √(j * n * Real.log n) = √(D ^ 2 * (j * n * Real.log n)) by
    rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]]
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left h hn0
  calc D ^ 2 * (j * n * Real.log n) * (j : ℝ) ^ 2 =
        (n : ℝ) * (D ^ 2 * (j : ℝ) ^ 3 * Real.log n) := by ring
    _ ≤ (n : ℝ) * n := this
    _ = (n : ℝ) ^ 2 := by ring

/-- `exp (−k log n) = 1/n^k`. -/
lemma exp_neg_nat_mul_log {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Real.exp (-(k * Real.log n)) = 1 / (n : ℝ) ^ k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_pow, Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- `log n ≥ log 2` for `n ≥ 2`. -/
lemma log_ge_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0.6931471803 ≤ Real.log n :=
  Real.log_two_gt_d9.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))

/-- The union bound, pointwise. -/
lemma ite_exists_le_sum {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P]
    [Decidable (∃ a ∈ s, P a)] :
    (if ∃ a ∈ s, P a then (1 : ℝ) else 0) ≤ ∑ a ∈ s, if P a then (1 : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨a, ha, hP⟩ := h
    calc (1 : ℝ) = if P a then (1 : ℝ) else 0 := (if_pos hP).symm
      _ ≤ ∑ a ∈ s, if P a then (1 : ℝ) else 0 :=
        single_le_sum (f := fun a => if P a then (1 : ℝ) else 0)
          (fun b _ => by split_ifs <;> norm_num) ha
  · exact sum_nonneg fun b _ => by split_ifs <;> norm_num

end Scalar

section Deterministic

variable {n : ℕ} {σ : Type*} [DecidableEq σ]

lemma colourCount_eq_zero_of_notMem {c : Fin n → σ} {a : σ} (ha : a ∉ univ.image c) :
    colourCount c a = 0 := by
  rw [colourCount, card_eq_zero, filter_eq_empty_iff]
  intro v _ hv
  exact ha (mem_image.mpr ⟨v, mem_univ v, hv⟩)

lemma notMem_image_of_colourCount_eq_zero {c : Fin n → σ} {a : σ} (h : colourCount c a = 0) :
    a ∉ univ.image c := by
  intro ha
  obtain ⟨v, -, hv⟩ := mem_image.mp ha
  have hmem : v ∈ univ.filter fun u => c u = a := mem_filter.mpr ⟨mem_univ v, hv⟩
  rw [colourCount, card_eq_zero] at h
  rw [h] at hmem
  exact notMem_empty v hmem

/-- A dead colour stays dead. -/
lemma colourCount_runCol_eq_zero {c : Fin n → σ} {a : σ} (h : colourCount c a = 0)
    (l : List (Tgt3 n)) : colourCount (runCol c l) a = 0 :=
  colourCount_eq_zero_of_notMem fun ha =>
    notMem_image_of_colourCount_eq_zero h (image_runCol_subset c l ha)

/-- The supports of the colours of any superset of the remaining colours add up to `n`. -/
lemma sum_colourCount_of_image_subset {c : Fin n → σ} {J : Finset σ} (h : univ.image c ⊆ J) :
    ∑ b ∈ J, (colourCount c b : ℝ) = n := by
  rw [← sum_subset h (fun b _ hb => by rw [colourCount_eq_zero_of_notMem hb, Nat.cast_zero])]
  exact sum_image_colourCount c

lemma sum_colourCount_univ [Fintype σ] (c : Fin n → σ) : ∑ b, (colourCount c b : ℝ) = n :=
  sum_colourCount_of_image_subset (subset_univ _)

/-- If every colour of `c` (`j` colours) has more than `n/j − m` agents, every colour has at most
`n/j + (j − 1) m` agents. -/
lemma colourCount_le_of_forall_lt {c : Fin n → σ} {m : ℝ} (hm : 0 ≤ m)
    (hj1 : 1 ≤ numColours c)
    (h : ∀ b ∈ univ.image c, (n : ℝ) / numColours c - m < colourCount c b) (b : σ) :
    (colourCount c b : ℝ) ≤ n / numColours c + (numColours c - 1) * m := by
  have hj : (1 : ℝ) ≤ numColours c := by exact_mod_cast hj1
  by_cases hb : b ∈ univ.image c
  · have hsum := sum_image_colourCount c
    rw [← add_sum_erase _ _ hb] at hsum
    have hle := card_nsmul_le_sum ((univ.image c).erase b) (fun b => (colourCount c b : ℝ))
      ((n : ℝ) / numColours c - m) (fun b' hb' => (h b' (mem_of_mem_erase hb')).le)
    have hcard : ((((univ.image c).erase b).card : ℕ) : ℝ) = numColours c - 1 := by
      rw [card_erase_of_mem hb, Nat.cast_sub (card_pos.mpr ⟨b, hb⟩), Nat.cast_one]
      rfl
    rw [nsmul_eq_mul, hcard] at hle
    have e : ((numColours c : ℝ) - 1) * ((n : ℝ) / numColours c - m) =
        n - n / numColours c - (numColours c - 1) * m := by
      field_simp
    linarith
  · rw [colourCount_eq_zero_of_notMem hb, Nat.cast_zero]
    have : (0 : ℝ) ≤ (numColours c - 1) * m := mul_nonneg (by linarith) hm
    positivity

/-- `∑_b (c_b/n)² ≤ M/n` when every support is at most `M`. -/
lemma sum_sq_div_le [Fintype σ] {c : Fin n → σ} {M : ℝ} (hn : (0 : ℝ) < n)
    (hM : ∀ b, (colourCount c b : ℝ) ≤ M) :
    ∑ b, ((colourCount c b : ℝ) / n) ^ 2 ≤ M / n := by
  have h1 : ∑ b, (colourCount c b : ℝ) ^ 2 ≤ ∑ b, M * colourCount c b :=
    sum_le_sum fun b _ => by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hM b) (Nat.cast_nonneg _)
  rw [← mul_sum, sum_colourCount_univ] at h1
  simp only [div_pow, ← sum_div]
  rw [div_le_div_iff₀ (by positivity) hn]
  calc (∑ b, (colourCount c b : ℝ) ^ 2) * n ≤ M * n * n := mul_le_mul_of_nonneg_right h1 hn.le
    _ = M * (n : ℝ) ^ 2 := by ring

/-- The smallest of the supports of the colours of `J ⊇ image c` is at most
`n/|J| − (1/(2|J|)) ∑_{a ∈ J} |c_a − n/|J||`. -/
lemma inf'_colourCount_le {c : Fin n → σ} {J : Finset σ} (hJ : J.Nonempty)
    (h : univ.image c ⊆ J) :
    J.inf' hJ (fun a => (colourCount c a : ℝ)) ≤ n / (J.card : ℝ) -
      1 / (2 * (J.card : ℝ)) * ∑ a ∈ J, |(colourCount c a : ℝ) - n / (J.card : ℝ)| := by
  have hk : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  have hsum := sum_colourCount_of_image_subset h
  have hι : (J.card : ℝ) * J.inf' hJ (fun a => (colourCount c a : ℝ)) ≤ n := by
    have := card_nsmul_le_sum J (fun a => (colourCount c a : ℝ))
      (J.inf' hJ (fun a => (colourCount c a : ℝ))) (fun a ha => inf'_le _ ha)
    rw [nsmul_eq_mul, hsum] at this
    exact this
  have hιle : J.inf' hJ (fun a => (colourCount c a : ℝ)) ≤ n / (J.card : ℝ) := by
    rw [le_div_iff₀ hk]
    linarith
  have hpt : ∀ a ∈ J, |(colourCount c a : ℝ) - n / (J.card : ℝ)| ≤
      ((colourCount c a : ℝ) - n / (J.card : ℝ)) +
        2 * (n / (J.card : ℝ) - J.inf' hJ (fun a => (colourCount c a : ℝ))) := by
    intro a ha
    have := inf'_le (fun a => (colourCount c a : ℝ)) ha
    rcases le_total (n / (J.card : ℝ)) (colourCount c a : ℝ) with h1 | h1
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith)]
      linarith
  have hS := sum_le_sum hpt
  rw [sum_add_distrib, sum_sub_distrib, hsum, sum_const, nsmul_eq_mul, sum_const,
    nsmul_eq_mul] at hS
  have e : (J.card : ℝ) * (n / (J.card : ℝ)) = n := by field_simp
  have hgoal : 1 / (2 * (J.card : ℝ)) * ∑ a ∈ J, |(colourCount c a : ℝ) - n / (J.card : ℝ)| ≤
      n / (J.card : ℝ) - J.inf' hJ (fun a => (colourCount c a : ℝ)) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  linarith

end Deterministic

section Mean

variable {n : ℕ} {σ : Type*} [DecidableEq σ] [NeZero n]

/-- The expected new support of `a` is the sum of the agents' adoption probabilities. -/
lemma sum_avg_adoptInd (c : Fin n → σ) (a : σ) :
    ∑ v, avg (adoptInd c a v) = avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) := by
  rw [show (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) =
      fun r : Tgt3 n => ∑ v, adoptInd c a v (r v) from
      funext (colourCount_stepCol_eq_sum c a), avg_sum]
  exact sum_congr rfl fun v _ => (avg_eval n v (adoptInd c a v)).symm

/-- Lower bound on the expected new support (Lemma 2.1 with `c_b ≤ M` for all `b`):
`𝔼[C_a'] ≥ c_a (1 + c_a/n − M/n)`. -/
lemma le_avg_colourCount_stepCol [Finite σ] (c : Fin n → σ) (a : σ) {M : ℝ}
    (hM : ∀ b, (colourCount c b : ℝ) ≤ M) :
    colourCount c a * (1 + colourCount c a / n - M / n) ≤
      avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) := by
  have := Fintype.ofFinite σ
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [avg_colourCount_stepCol]
  have := sum_sq_div_le hn hM
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

/-- Upper bound of Lemma 2.1 at a level `b ≥ c_a`, with at most `j` colours:
`𝔼[C_a'] ≤ b (1 + b/n − 1/j)`. -/
lemma avg_colourCount_stepCol_le_of_le [Finite σ] (c : Fin n → σ) (a : σ) {j : ℕ} {b : ℝ}
    (hj : numColours c ≤ j) (hb : (colourCount c a : ℝ) ≤ b) :
    avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) ≤ b * (1 + b / n - 1 / j) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h := avg_colourCount_stepCol_le c a
  have hW : (0 : ℝ) < numColours c := by
    have : 0 < numColours c := by
      rw [numColours, card_pos]
      exact univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩ |>.image c
    exact_mod_cast this
  have hjW : (numColours c : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : 1 / (j : ℝ) ≤ 1 / numColours c := one_div_le_one_div_of_le hW hjW
  have hj1 : 1 / (j : ℝ) ≤ 1 := by
    rw [div_le_one (hW.trans_le hjW)]
    linarith [show (1 : ℝ) ≤ numColours c by
      exact_mod_cast (show 1 ≤ numColours c by exact_mod_cast hW)]
  have hc0 : (0 : ℝ) ≤ colourCount c a := Nat.cast_nonneg _
  have h2 : (colourCount c a : ℝ) * (1 + colourCount c a / n - 1 / numColours c) ≤
      colourCount c a * (1 + colourCount c a / n - 1 / j) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have e : b * (1 + b / n - 1 / j) - colourCount c a * (1 + colourCount c a / n - 1 / j) =
      (b - colourCount c a) * ((1 - 1 / j) + (b + colourCount c a) / n) := by ring
  have h3 : 0 ≤ (b - colourCount c a) * ((1 - 1 / (j : ℝ)) + (b + colourCount c a) / n) :=
    mul_nonneg (by linarith) (add_nonneg (by linarith) (div_nonneg (by linarith) hn.le))
  linarith

/-- Under the hypotheses of Equation (6) (every colour of `x`, with `j ≥ 2` colours, has more
than `n/j − m` agents, `8 j m ≤ n`), every colour of `x` has expected new support at least
`n/j − 2m`: the supports are at most `M = n/j + (j − 1) m`, so `∑_b (c_b/n)² ≤ M/n`, and
`c ↦ c (1 + c/n − M/n)` is increasing, with value at least `n/j − 2m` at `c = n/j − m`. -/
lemma le_avg_colourCount_stepCol_of_forall_lt [Finite σ] {x : Fin n → σ} {m : ℝ} (hm : 0 ≤ m)
    (hj2 : 2 ≤ numColours x) (hjm : 8 * numColours x * m ≤ n)
    (hall : ∀ b ∈ univ.image x, (n : ℝ) / numColours x - m < colourCount x b) {a : σ}
    (ha : a ∈ univ.image x) :
    (n : ℝ) / numColours x - 2 * m ≤
      avg (fun r : Tgt3 n => (colourCount (stepCol x r) a : ℝ)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hM := colourCount_le_of_forall_lt hm (by omega) hall
  refine le_trans ?_ (le_avg_colourCount_stepCol x a hM)
  have hc := hall a ha
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = numColours x := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = colourCount x a := ⟨_, rfl⟩
  rw [← hJ] at hc hjm ⊢
  rw [← hcdef] at hc ⊢
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = n := ⟨_, rfl⟩
  rw [← hNdef] at hc hjm hN ⊢
  have hJ2 : (2 : ℝ) ≤ J := by rw [hJ]; exact_mod_cast hj2
  have hJ0 : (0 : ℝ) < J := by linarith
  -- `c₀ = N/J − m ∈ [0, N/J]`
  have hNJ : N / J * J = N := by field_simp
  have hmJ : m ≤ N / J / 8 := by
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ hJ0]
    linarith
  have hc00 : 0 ≤ N / J - m := by
    have : 0 ≤ N / J := by positivity
    linarith
  -- `1 − M/N ≥ 0`
  have hK : 0 ≤ 1 - (N / J + (J - 1) * m) / N := by
    rw [sub_nonneg, div_le_one hN]
    have h1 : N / J ≤ N / 2 := div_le_div_of_nonneg_left hN.le (by norm_num) hJ2
    nlinarith
  have hmono : (N / J - m) * (1 + (N / J - m) / N - (N / J + (J - 1) * m) / N) ≤
      c * (1 + c / N - (N / J + (J - 1) * m) / N) := by
    have e : c * (1 + c / N - (N / J + (J - 1) * m) / N) -
        (N / J - m) * (1 + (N / J - m) / N - (N / J + (J - 1) * m) / N) =
        (c - (N / J - m)) * ((1 - (N / J + (J - 1) * m) / N) + (c + (N / J - m)) / N) := by
      ring
    have : 0 ≤ (c - (N / J - m)) * ((1 - (N / J + (J - 1) * m) / N) + (c + (N / J - m)) / N) :=
      mul_nonneg (by linarith) (add_nonneg hK (div_nonneg (by linarith) hN.le))
    linarith
  have hval : (N / J - m) * (1 + (N / J - m) / N - (N / J + (J - 1) * m) / N) =
      (N / J - m) - m * ((N / J - m) * J / N) := by
    field_simp
    ring
  have hfrac : (N / J - m) * J / N ≤ 1 := by
    rw [div_le_one hN, sub_mul, hNJ]
    nlinarith
  have : m * ((N / J - m) * J / N) ≤ m := by
    calc m * ((N / J - m) * J / N) ≤ m * 1 := mul_le_mul_of_nonneg_left hfrac hm
      _ = m := mul_one m
  linarith

end Mean

section Tails

variable {n : ℕ} {σ : Type*} [DecidableEq σ] [NeZero n]

/-- **Chernoff upper tail for the new support of a colour**, at a threshold `k`: if the mean is
at most `μ` with `0 < μ < k`, then `P(C_a' ≥ k) ≤ exp(−(k − μ)²/(k + μ))`. -/
theorem avg_colourCount_stepCol_ge (c : Fin n → σ) (a : σ) {μ k : ℝ} (hμ0 : 0 < μ)
    (hμk : μ < k) (hmean : avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) ≤ μ) :
    avg (fun r : Tgt3 n => if k ≤ (colourCount (stepCol c r) a : ℝ) then (1 : ℝ) else 0) ≤
      Real.exp (-((k - μ) ^ 2 / (k + μ))) := by
  have hδ : 0 < (k - μ) / μ := div_pos (by linarith) hμ0
  have h := avg_chernoff_upper (adoptInd c a) (adoptInd_zero_one c a) hδ
    ((sum_avg_adoptInd c a).trans_le hmean)
  have hμne : μ ≠ 0 := hμ0.ne'
  have hkμ : k + μ ≠ 0 := by linarith
  have e1 : (1 + (k - μ) / μ) * μ = k := by field_simp; ring
  have e2 : ((k - μ) / μ) ^ 2 * μ / (2 + (k - μ) / μ) = (k - μ) ^ 2 / (k + μ) := by
    rw [show 2 + (k - μ) / μ = (k + μ) / μ by field_simp; ring]
    field_simp
  rw [e1, e2] at h
  rw [show (fun r : Tgt3 n => if k ≤ (colourCount (stepCol c r) a : ℝ) then (1 : ℝ) else 0) =
      fun r : Tgt3 n => if k ≤ ∑ v, adoptInd c a v (r v) then (1 : ℝ) else 0 from
      funext fun r => by rw [colourCount_stepCol_eq_sum]]
  exact h

/-- **Chernoff lower tail for the new support of a colour**, at a threshold `k`: if the mean is
at least `μ` with `0 < k < μ`, then `P(C_a' ≤ k) ≤ exp(−(μ − k)²/(2μ))`. -/
theorem avg_colourCount_stepCol_le_tail (c : Fin n → σ) (a : σ) {μ k : ℝ} (hk0 : 0 < k)
    (hkμ : k < μ) (hmean : μ ≤ avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ))) :
    avg (fun r : Tgt3 n => if (colourCount (stepCol c r) a : ℝ) ≤ k then (1 : ℝ) else 0) ≤
      Real.exp (-((μ - k) ^ 2 / (2 * μ))) := by
  have hμ0 : 0 < μ := hk0.trans hkμ
  have hδ0 : 0 < (μ - k) / μ := div_pos (by linarith) hμ0
  have hδ1 : (μ - k) / μ < 1 := by
    rw [div_lt_one hμ0]
    linarith
  have h := avg_chernoff_lower (adoptInd c a) (adoptInd_zero_one c a) hδ0 hδ1
    (hmean.trans_eq (sum_avg_adoptInd c a).symm)
  have hμne : μ ≠ 0 := hμ0.ne'
  have e1 : (1 - (μ - k) / μ) * μ = k := by field_simp; ring
  have e2 : ((μ - k) / μ) ^ 2 * μ / 2 = (μ - k) ^ 2 / (2 * μ) := by field_simp
  rw [e1, e2] at h
  rw [show (fun r : Tgt3 n => if (colourCount (stepCol c r) a : ℝ) ≤ k then (1 : ℝ) else 0) =
      fun r : Tgt3 n => if ∑ v, adoptInd c a v (r v) ≤ k then (1 : ℝ) else 0 from
      funext fun r => by rw [colourCount_stepCol_eq_sum]]
  exact h

/-- **Anti-concentration of the new support of a colour** (replaces the Central Limit Theorem of
BCNPT16, Equation (4)): if the agents' variances add up to `σ² ≥ 1`, the new support is at mean
absolute distance at least `(9/256) σ` from any fixed value `θ`. If the mean is at distance at
least `σ/4` from `θ`, this is Jensen's inequality; otherwise, on the Paley–Zygmund event
`σ² ≤ 4 S²` (probability at least `9/64`) the centered sum `S` is at least `σ/2` in absolute
value. -/
theorem avg_abs_colourCount_stepCol_sub_ge (c : Fin n → σ) (a : σ) (θ : ℝ)
    (hσ : 1 ≤ ∑ v, variance (adoptInd c a v)) :
    9 / 256 * √(∑ v, variance (adoptInd c a v)) ≤
      avg (fun r : Tgt3 n => |(colourCount (stepCol c r) a : ℝ) - θ|) := by
  obtain ⟨V, hV⟩ : ∃ V, V = ∑ v, variance (adoptInd c a v) := ⟨_, rfl⟩
  rw [← hV] at hσ ⊢
  obtain ⟨s, hs⟩ : ∃ s, s = √V := ⟨_, rfl⟩
  rw [← hs]
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ v, avg (adoptInd c a v) := ⟨_, rfl⟩
  have hmean : avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) = μ := by
    rw [hμ, sum_avg_adoptInd]
  by_cases hb : s / 4 ≤ |μ - θ|
  · have h1 : avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ) - θ) = μ - θ := by
      rw [avg_sub, avg_const, hmean]
    have h2 : avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ) - θ) ≤
        avg (fun r : Tgt3 n => |(colourCount (stepCol c r) a : ℝ) - θ|) :=
      avg_le_avg fun r => le_abs_self _
    have h3 : 0 ≤ avg (fun r : Tgt3 n => |(colourCount (stepCol c r) a : ℝ) - θ| +
        ((colourCount (stepCol c r) a : ℝ) - θ)) :=
      avg_nonneg fun r => by linarith [neg_abs_le ((colourCount (stepCol c r) a : ℝ) - θ)]
    rw [avg_add] at h3
    rw [h1] at h2 h3
    have h4 : |μ - θ| ≤ avg (fun r : Tgt3 n => |(colourCount (stepCol c r) a : ℝ) - θ|) := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  · push Not at hb
    have hpz : 9 / 64 ≤ avg (fun r : Tgt3 n =>
        if V ≤ 4 * (∑ v, (adoptInd c a v (r v) - avg (adoptInd c a v))) ^ 2 then (1 : ℝ)
        else 0) := by
      rw [hV]
      exact avg_pz_zero_one (adoptInd c a) (fun v y => adoptInd_zero_one c a v y) (hV ▸ hσ)
    have hpt : ∀ r : Tgt3 n, s / 4 *
        (if V ≤ 4 * (∑ v, (adoptInd c a v (r v) - avg (adoptInd c a v))) ^ 2 then (1 : ℝ)
          else 0) ≤ |(colourCount (stepCol c r) a : ℝ) - θ| := by
      intro r
      split_ifs with hE
      · obtain ⟨S, hS⟩ : ∃ S, S = ∑ v, (adoptInd c a v (r v) - avg (adoptInd c a v)) :=
          ⟨_, rfl⟩
        rw [← hS] at hE
        have hC : (colourCount (stepCol c r) a : ℝ) - θ = S + (μ - θ) := by
          rw [colourCount_stepCol_eq_sum, hS, sum_sub_distrib, hμ]
          ring
        have hsS : s ≤ 2 * |S| := by
          have : V ≤ (2 * S) ^ 2 := by nlinarith
          have h' := Real.sqrt_le_sqrt this
          rw [Real.sqrt_sq_eq_abs, abs_mul, abs_two] at h'
          rw [hs]
          exact h'
        rw [hC]
        have := abs_sub_abs_le_abs_sub S (-(μ - θ))
        rw [sub_neg_eq_add, abs_neg] at this
        linarith
      · rw [mul_zero]
        exact abs_nonneg _
    calc 9 / 256 * s = s / 4 * (9 / 64) := by ring
      _ ≤ s / 4 * avg (fun r : Tgt3 n =>
          if V ≤ 4 * (∑ v, (adoptInd c a v (r v) - avg (adoptInd c a v))) ^ 2 then (1 : ℝ)
          else 0) := mul_le_mul_of_nonneg_left hpz (by positivity)
      _ = avg (fun r : Tgt3 n => s / 4 *
          (if V ≤ 4 * (∑ v, (adoptInd c a v (r v) - avg (adoptInd c a v))) ^ 2 then (1 : ℝ)
            else 0)) := (avg_const_mul _ _).symm
      _ ≤ _ := avg_le_avg hpt

/-- **Variance near the uniform configuration** (for BCNPT16, Equation (4)): if every colour of
`x` (`j ≥ 2` colours) has more than `n/j − n u` agents with `j u ≤ 1/250`, the agents' variances
for the new support of each colour add up to at least `n/(4j)`. The adoption probability
`p = X (1 + X − ‖x‖²)` (`X = c_a/n`) lies between `(1 − 1/250)²/j` and `(1/2 + 1/250)(1 + 1/250)`,
and the variance is `n p (1 − p)`. -/
lemma sum_variance_adoptInd_ge [Finite σ] {x : Fin n → σ} {u : ℝ} (hu : 0 ≤ u)
    (hj2 : 2 ≤ numColours x) (hju : numColours x * u ≤ 1 / 250)
    (hall : ∀ b ∈ univ.image x, (n : ℝ) / numColours x - n * u < colourCount x b) {a : σ}
    (ha : a ∈ univ.image x) :
    (n : ℝ) / (4 * numColours x) ≤ ∑ v, variance (adoptInd x a v) := by
  have := Fintype.ofFinite σ
  have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hM := colourCount_le_of_forall_lt (mul_nonneg hN.le hu) (by omega) hall
  have hS2 := sum_sq_div_le hN hM
  have hS1 : 1 / (numColours x : ℝ) ≤ ∑ b, ((colourCount x b : ℝ) / n) ^ 2 := by
    have hJ0 : (0 : ℝ) < numColours x := by
      have : 0 < numColours x := by omega
      exact_mod_cast this
    have hsq := sq_le_numColours_mul_sum_sq x
    simp only [div_pow, ← sum_div]
    rw [div_le_div_iff₀ hJ0 (by positivity)]
    linarith
  have hlo := hall a ha
  have hhi := hM a
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (colourCount x a : ℝ) / n := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ b, ((colourCount x b : ℝ) / n) ^ 2 := ⟨_, rfl⟩
  have hv : ∀ v, variance (adoptInd x a v) = X * (1 + X - S) * (1 - X * (1 + X - S)) := by
    intro v
    have h := avg_adoptInd x a v
    rw [← hX, ← hS] at h
    rw [variance_of_zero_one (adoptInd_zero_one x a v),
      show Dynamics.avg (adoptInd x a v) = X * (1 + X - S) from h]
  rw [sum_congr rfl fun v _ => hv v, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hS] at hS1 hS2
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = numColours x := ⟨_, rfl⟩
  rw [← hJ] at hju hlo hhi hS1 hS2 ⊢
  have hJ2 : (2 : ℝ) ≤ J := by rw [hJ]; exact_mod_cast hj2
  have hJ0 : (0 : ℝ) < J := by linarith
  -- `X` and `S` in terms of `1/J` and `u`
  have hXlo : 1 / J - u < X := by
    rw [hX, lt_div_iff₀ hN]
    have e : (1 / J - u) * n = n / J - n * u := by ring
    linarith
  have hXhi : X ≤ 1 / J + (J - 1) * u := by
    rw [hX, div_le_iff₀ hN]
    have e : (1 / J + (J - 1) * u) * n = n / J + (J - 1) * (n * u) := by ring
    linarith
  have hS2' : S ≤ 1 / J + (J - 1) * u := by
    have e : (n / J + (J - 1) * (n * u)) / n = 1 / J + (J - 1) * u := by field_simp
    linarith
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hJu1 : (J - 1) * u ≤ 1 / 250 := by
    have : (J - 1) * u ≤ J * u := mul_le_mul_of_nonneg_right (by linarith) hu
    linarith
  have hJinv : 1 / J ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hJ0 (by norm_num)]
    linarith
  have huJ : u ≤ 1 / 250 / J := by
    rw [le_div_iff₀ hJ0]
    linarith
  -- bounds on the adoption probability `p = X (1 + X − S)`
  have hYlo : 1 - 1 / 250 ≤ 1 + X - S := by
    have e : (J - 1) * u = J * u - u := by ring
    linarith
  have hYhi : 1 + X - S ≤ 1 + 1 / 250 := by linarith
  have hplo : (1 - 1 / 250) / J * (1 - 1 / 250) ≤ X * (1 + X - S) := by
    have hX' : (1 - 1 / 250) / J ≤ X := by
      have e : (1 - 1 / 250) / J = 1 / J - 1 / 250 / J := by ring
      linarith
    exact mul_le_mul hX' hYlo (by norm_num) hX0
  have hphi : X * (1 + X - S) ≤ (1 / 2 + 1 / 250) * (1 + 1 / 250) :=
    mul_le_mul (by linarith) hYhi (by linarith) (by norm_num)
  have hp0 : 0 ≤ X * (1 + X - S) := le_trans (by positivity) hplo
  have hpp : (1 - 1 / 250) / J * (1 - 1 / 250) * (1 - (1 / 2 + 1 / 250) * (1 + 1 / 250)) ≤
      X * (1 + X - S) * (1 - X * (1 + X - S)) :=
    mul_le_mul hplo (by linarith) (by norm_num) hp0
  have hc : (1 : ℝ) / 4 ≤
      (1 - 1 / 250) * (1 - 1 / 250) * (1 - (1 / 2 + 1 / 250) * (1 + 1 / 250)) := by
    norm_num
  calc (n : ℝ) / (4 * J) = n * (1 / 4 / J) := by ring
    _ ≤ n * ((1 - 1 / 250) * (1 - 1 / 250) * (1 - (1 / 2 + 1 / 250) * (1 + 1 / 250)) / J) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc hJ0.le) hN.le
    _ = n * ((1 - 1 / 250) / J * (1 - 1 / 250) * (1 - (1 / 2 + 1 / 250) * (1 + 1 / 250))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpp hN.le

end Tails

end ThreeMajority
