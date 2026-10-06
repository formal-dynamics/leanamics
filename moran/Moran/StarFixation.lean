import Moran.PushPull
import Moran.StarAlgebra
import Moran.StarKernel

/-! # Fixation probabilities on the star (MOR-3)

From the invariance of `starPotential` (`starPotential_apply`), the fixation probability on the
star from any configuration `s` is `(1 - Φ s) / (1 - Φ (all mutant))` for `r ≠ 1`
(`star_fixation_eq`), by the invariant method `fixation_eq_of_invariant` of MOR-2. Evaluating
the potential on single mutants gives the closed forms from a leaf, from the centre and from a
uniformly random vertex. For the neutral case we reuse `push_fixation` (VOT-4): on every
connected graph a neutral single mutant at a uniformly random vertex fixes with probability
`1 / N` (`neutral_uniform_fixation`).
-/

namespace Moran
open Dynamics Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Generic facts on fixation -/

omit [DecidableEq V] in
/-- An observable equal to `1` on the all-mutant configuration, `0` on the all-resident one and
between `0` and `1` elsewhere is sandwiched as required by `fixation_eq_of_invariant`. -/
lemma sandwich_of_bounds [Nonempty V] (ψ : Config V → ℝ) (h1 : ψ (fun _ => true) = 1)
    (h0 : ψ (fun _ => false) = 0) (hb : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1) (t : Config V) :
    allMutant t ≤ ψ t ∧ ψ t ≤ allMutant t + unfixed t := by
  by_cases ht : t = fun _ => true
  · subst ht
    rw [allMutant_true, h1, unfixed_const]
    constructor <;> norm_num
  · by_cases hf : t = fun _ => false
    · subst hf
      rw [allMutant_false, h0, unfixed_const]
      constructor <;> norm_num
    · have ha : allMutant t = 0 := by rw [allMutant, if_neg ht]
      have hu : unfixed t = 1 := unfixed_of_mixed t (by
        rintro ⟨c, hc⟩
        cases c with
        | false => exact hf hc
        | true => exact ht hc)
      rw [ha, hu, zero_add]
      exact hb t

/-- The all-mutant configuration has fixed: its fixation probability is `1`. -/
lemma fixation_true [Nonempty V] (K : Kernel (Config V)) : fixation K (fun _ => true) = 1 := by
  refine le_antisymm (ciSup_le fun t => fixation_le_one K t _) ?_
  refine le_ciSup_of_le ⟨1, ?_⟩ 0 ?_
  · rintro _ ⟨t, rfl⟩
    exact fixation_le_one K t _
  · rw [Kernel.iterate_zero, allMutant_true]

/-- The uniform average of a function of the vertices of the star with `n` leaves that takes
the same value `a` on every leaf. -/
lemma star_uniform_expect [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    (F : V → ℝ) {a : ℝ} (hF : ∀ v, v ≠ c → F v = a) :
    (Distribution.uniform V).expect F = (F c + n * a) / (n + 1) := by
  rw [Distribution.uniform_expect, avg, ← add_sum_erase univ _ (mem_univ c),
    sum_congr rfl fun v hv => hF v (ne_of_mem_erase hv), sum_const,
    card_erase_of_mem (mem_univ c), card_univ, hn, nsmul_eq_mul]
  push_cast
  simp

/-- **Neutral fixation from a uniformly random vertex.** On every connected graph with at least
two vertices, a neutral single mutant at a uniformly random vertex fixes with probability `1/N`
(from `push_fixation`, VOT-4). -/
lemma neutral_uniform_fixation [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (h1 : (0 : ℝ) < 1) :
    (Distribution.uniform V).expect
        (fun v => fixation (moranKernel G 1 h1) (fun w => decide (w = v))) =
      1 / Fintype.card V := by
  have hP := pushValue_total_pos G hc
  have hsingle : ∀ v, pushValue G (fun w => decide (w = v)) = (G.degree v : ℝ)⁻¹ := by
    intro v
    unfold pushValue
    have : univ.filter (fun w => decide (w = v) = true) = {v} := by
      ext w
      simp
    rw [this, sum_singleton]
  have hall : pushValue G (fun _ => true) = ∑ v, (G.degree v : ℝ)⁻¹ := by
    unfold pushValue
    congr 1
    ext v
    simp
  rw [Distribution.uniform_expect, avg]
  simp_rw [push_fixation G hc, hsingle]
  rw [← sum_div, ← hall, div_self hP.ne']

/-! ### The potential on special configurations -/

/-- The potential of the all-mutant configuration is `q ^ n * κ`. -/
lemma starPotential_true (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) (r : ℝ) :
    starPotential c n r (fun _ => true) = starRatio n r ^ n * starCentreWeight n r := by
  rw [starPotential_of_true rfl, leafMutants_true c hn]

/-- The potential of the all-resident configuration is `1`. -/
lemma starPotential_false (c : V) (n : ℕ) (r : ℝ) : starPotential c n r (fun _ => false) = 1 := by
  rw [starPotential_of_false rfl, leafMutants_false, pow_zero]

/-- The potential of a single mutant on a leaf is `q`. -/
lemma starPotential_single_leaf {c v : V} (hv : v ≠ c) (n : ℕ) (r : ℝ) :
    starPotential c n r (fun w => decide (w = v)) = starRatio n r := by
  rw [starPotential_of_false (by simpa using hv.symm), leafMutants_single_leaf hv, pow_one]

/-- The potential of a single mutant at the centre is `κ`. -/
lemma starPotential_single_centre (c : V) (n : ℕ) (r : ℝ) :
    starPotential c n r (fun w => decide (w = c)) = starCentreWeight n r := by
  rw [starPotential_of_true (by simp), leafMutants_single_centre, pow_zero, one_mul]

/-- For `r > 1` the potential lies between its all-mutant value and `1`. -/
lemma starPotential_bounds_of_gt (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ}
    (hr : 1 < r) (t : Config V) :
    starPotential c n r (fun _ => true) ≤ starPotential c n r t ∧
      starPotential c n r t ≤ 1 := by
  have hq0 := (starRatio_pos n (zero_lt_one.trans hr)).le
  have hq1 := starRatio_le_one n hr.le
  have hk0 := (starCentreWeight_pos n (zero_lt_one.trans hr)).le
  have hk1 := (starCentreWeight_lt_one n hr).le
  have hL := leafMutants_le c hn t
  rw [starPotential_true c hn]
  unfold starPotential
  have hi0 : 0 ≤ (if t c = true then starCentreWeight n r else 1) := by split <;> linarith
  have hi1 : (if t c = true then starCentreWeight n r else 1) ≤ 1 := by split <;> linarith
  have hik : starCentreWeight n r ≤ (if t c = true then starCentreWeight n r else 1) := by
    split <;> linarith
  exact ⟨mul_le_mul (pow_le_pow_of_le_one hq0 hq1 hL) hik hk0 (pow_nonneg hq0 _),
    mul_le_one₀ (pow_le_one₀ hq0 hq1) hi0 hi1⟩

/-- For `r < 1` the potential lies between `1` and its all-mutant value. -/
lemma starPotential_bounds_of_lt (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) (t : Config V) :
    1 ≤ starPotential c n r t ∧
      starPotential c n r t ≤ starPotential c n r (fun _ => true) := by
  have hq1 := one_le_starRatio n hr0 hr.le
  have hk1 := (one_lt_starCentreWeight n hr0 hr).le
  have hL := leafMutants_le c hn t
  rw [starPotential_true c hn]
  unfold starPotential
  have hi1 : 1 ≤ (if t c = true then starCentreWeight n r else 1) := by split <;> linarith
  have hik : (if t c = true then starCentreWeight n r else 1) ≤ starCentreWeight n r := by
    split <;> linarith
  exact ⟨one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1) hi1,
    mul_le_mul (pow_le_pow_right₀ hq1 hL) hik (by linarith) (pow_nonneg (by linarith) _)⟩

/-! ### Fixation on the star -/

/-- The normalized potential `(1 - Φ t) / (1 - Φ (all mutant))` lies in `[0, 1]`. -/
lemma starPsi_bounds (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≠ 1) (t : Config V) :
    0 ≤ (1 - starPotential c n r t) / (1 - starPotential c n r (fun _ => true)) ∧
      (1 - starPotential c n r t) / (1 - starPotential c n r (fun _ => true)) ≤ 1 := by
  have hD := star_denom_ne_zero n hr hr1
  rw [mul_comm, ← starPotential_true c hn] at hD
  rcases hr1.lt_or_gt with h | h
  · obtain ⟨h1, h2⟩ := starPotential_bounds_of_lt c hn hr h t
    have hneg : 1 - starPotential c n r (fun _ => true) < 0 :=
      lt_of_le_of_ne (by linarith) hD
    exact ⟨div_nonneg_of_nonpos (by linarith) hneg.le, (div_le_one_of_neg hneg).mpr (by linarith)⟩
  · obtain ⟨h1, h2⟩ := starPotential_bounds_of_gt c hn h t
    have hpos : 0 < 1 - starPotential c n r (fun _ => true) :=
      lt_of_le_of_ne (by linarith) hD.symm
    exact ⟨div_nonneg (by linarith) hpos.le, div_le_one_of_le₀ (by linarith) hpos.le⟩

/-- **Fixation on the star from any configuration** (the content of `star_fixation`). -/
lemma star_fixation_eq [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) (s : Config V) :
    fixation (moranKernel (starGraph c) r hr) s =
      (1 - starPotential c n r s) / (1 - starPotential c n r (fun _ => true)) := by
  have hD := star_denom_ne_zero n hr hr1
  rw [mul_comm, ← starPotential_true c hn] at hD
  set D := 1 - starPotential c n r (fun _ => true) with hDdef
  have hinv : (moranKernel (starGraph c) r hr).apply
      (fun t => (1 - starPotential c n r t) / D) = fun t => (1 - starPotential c n r t) / D := by
    funext t
    rw [Kernel.apply]
    have hcomm : ∀ t' : Config V,
        (1 - starPotential c n r t') / D = D⁻¹ * (1 - starPotential c n r t') := fun t' => by
      rw [div_eq_mul_inv, mul_comm]
    simp_rw [hcomm]
    rw [Distribution.expect_mul, Distribution.expect_sub, Distribution.expect_const,
      ← Kernel.apply, starPotential_apply c hn hr t]
  refine fixation_eq_of_invariant _ _ (unfixed_step _ hr)
    (unfixed_access _ (connected_starGraph c) hr) hinv ?_ (allMutant_step _ hr) s
  refine sandwich_of_bounds _ ?_ ?_ (starPsi_bounds c hn hr hr1)
  · exact div_self hD
  · rw [starPotential_false, sub_self, zero_div]

/-- The fixation probability of a single mutant on a leaf (the content of
`star_fixation_leaf`). -/
lemma star_fixation_single_leaf [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {v : V} (hv : v ≠ c) :
    fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = v)) =
      (1 - starRatio n r) / (1 - starCentreWeight n r * starRatio n r ^ n) := by
  rw [star_fixation_eq c hn hr hr1, starPotential_single_leaf hv, starPotential_true c hn,
    mul_comm (starRatio n r ^ n)]

/-- The fixation probability of a single mutant at the centre (the content of
`star_fixation_centre`). -/
lemma star_fixation_single_centre [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = c)) =
      (1 - starCentreWeight n r) / (1 - starCentreWeight n r * starRatio n r ^ n) := by
  rw [star_fixation_eq c hn hr hr1, starPotential_single_centre, starPotential_true c hn,
    mul_comm (starRatio n r ^ n)]

/-- The fixation probability of a single mutant at a uniformly random vertex (the content of
`star_fixation_uniform`). -/
lemma star_fixation_uniform_eq [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    (Distribution.uniform V).expect
        (fun v => fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = v))) =
      (n * (1 - starRatio n r) + (1 - starCentreWeight n r)) /
        ((n + 1) * (1 - starCentreWeight n r * starRatio n r ^ n)) := by
  rw [star_uniform_expect c hn _ fun v hv => star_fixation_single_leaf c hn hr hr1 hv,
    star_fixation_single_centre c hn hr hr1]
  have hD := star_denom_ne_zero n hr hr1
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end Moran
