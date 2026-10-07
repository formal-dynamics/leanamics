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
`1 / N` (`neutral_uniform_fixation` in `PushPull`).
-/

namespace Moran
open Dynamics Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Generic facts on fixation -/

/-- The all-mutant configuration has fixed: its fixation probability is `1`. -/
lemma fixation_true [Nonempty V] (K : Kernel (Config V)) : fixation K (fun _ => true) = 1 := by
  have hle : ∀ t, K.iterate t allMutant (fun _ => true) ≤ 1 := fun t => by
    rw [iterate_allMutant]
    exact K.event_le_one _ t _
  refine le_antisymm (ciSup_le hle) ?_
  refine le_ciSup_of_le ⟨1, ?_⟩ 0 ?_
  · rintro _ ⟨t, rfl⟩
    exact hle t
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

/-! ### Fixation on the star -/

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
  refine fixation_eq_of_invariant _ _ hinv ?_ ?_ (allMutant_step _ hr) s
    (moran_unfixed_tendsto _ (connected_starGraph c) hr s)
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
