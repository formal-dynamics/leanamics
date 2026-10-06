import Moran.StarDefs

/-! # The Birth–death step on the star (MOR-3)

Degrees and offspring placement on the star `starGraph c` with `n` leaves, how a step changes
the number of mutant leaves, and the edge-by-edge cancellation behind the invariance of
`starPotential`: for every leaf `ℓ`, the expected change of the potential along the two
orientations `(c, ℓ)` and `(ℓ, c)` of the edge `{c, ℓ}` vanishes. These encode the system
(5.1)–(5.2) of Broom–Rychtář (2008).
-/

namespace Moran
open Dynamics Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Degrees and offspring placement -/

/-- The centre of the star with `n` leaves has degree `n`. -/
lemma star_degree_centre (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) :
    (starGraph c).degree c = n := by
  rw [degree_starGraph_center, hn, Nat.add_sub_cancel]

omit [DecidableEq V] in
/-- A star with a leaf `v ≠ c` has at least one leaf. -/
lemma star_leaves_ne_zero {c v : V} (hv : v ≠ c) {n : ℕ} (hn : Fintype.card V = n + 1) :
    n ≠ 0 := by
  rintro rfl
  exact hv (Fintype.card_le_one_iff.mp (le_of_eq hn) v c)

/-- The centre places its offspring on a given leaf with probability `1/n`. -/
lemma star_target_centre_leaf {c v : V} {n : ℕ} (hn : Fintype.card V = n + 1) (hv : v ≠ c) :
    target (starGraph c) c v = (n : ℝ)⁻¹ := by
  rw [target, star_degree_centre c hn, if_neg (star_leaves_ne_zero hv hn),
    if_pos (starGraph_center_adj hv.symm)]

/-- A leaf places its offspring on the centre. -/
lemma star_target_leaf_centre {c v : V} (hv : v ≠ c) : target (starGraph c) v c = 1 := by
  rw [target, degree_starGraph_of_ne_center hv, if_neg one_ne_zero,
    if_pos (starGraph_center_adj' hv.symm), Nat.cast_one, inv_one]

/-- A leaf never places its offspring on a leaf. -/
lemma star_target_leaf_leaf {c v w : V} (hv : v ≠ c) (hw : w ≠ c) :
    target (starGraph c) v w = 0 := by
  rw [target, degree_starGraph_of_ne_center hv, if_neg one_ne_zero, if_neg]
  simp [starGraph_adj, hv, hw]

/-- A sum over ordered pairs that vanishes on `(c, c)` and on pairs of leaves is a sum over the
edges `{c, ℓ}` of the star, in both orientations. -/
lemma star_sum_pairs (c : V) (g : V → V → ℝ) (hcc : g c c = 0)
    (hleaf : ∀ u w, u ≠ c → w ≠ c → g u w = 0) :
    ∑ p : V × V, g p.1 p.2 = ∑ ℓ ∈ univ.erase c, (g c ℓ + g ℓ c) := by
  rw [Fintype.sum_prod_type, ← add_sum_erase univ _ (mem_univ c),
    ← add_sum_erase univ _ (mem_univ c), hcc, zero_add, sum_add_distrib]
  congr 1
  refine sum_congr rfl fun u hu => ?_
  have hu : u ≠ c := ne_of_mem_erase hu
  rw [← add_sum_erase univ _ (mem_univ c),
    sum_eq_zero fun w hw => hleaf u w hu (ne_of_mem_erase hw), add_zero]

/-! ### Mutant leaves after one step -/

/-- Changing the type of the centre does not change the number of mutant leaves. -/
lemma leafMutants_update_centre (c : V) (s : Config V) (b : Bool) :
    leafMutants c (Function.update s c b) = leafMutants c s := by
  unfold leafMutants
  congr 1
  ext v
  by_cases hv : v = c
  · simp [hv]
  · simp [hv]

/-- A resident leaf turning mutant adds one mutant leaf. -/
lemma leafMutants_update_gain {c w : V} (hw : w ≠ c) (s : Config V) (hsw : s w = false) :
    leafMutants c (Function.update s w true) = leafMutants c s + 1 := by
  unfold leafMutants
  have hmem : w ∉ univ.filter (fun v => v ≠ c ∧ s v = true) := by simp [hsw]
  have hfilter : univ.filter (fun v => v ≠ c ∧ Function.update s w true v = true) =
      insert w (univ.filter fun v => v ≠ c ∧ s v = true) := by
    ext v
    by_cases hv : v = w
    · subst hv
      simp [hw]
    · simp [hv]
  rw [hfilter, card_insert_of_notMem hmem]

/-- A mutant leaf turning resident removes one mutant leaf. -/
lemma leafMutants_update_loss {c w : V} (hw : w ≠ c) (s : Config V) (hsw : s w = true) :
    leafMutants c s = leafMutants c (Function.update s w false) + 1 := by
  have h := leafMutants_update_gain hw (Function.update s w false) (by simp)
  rwa [Function.update_idem, ← hsw, Function.update_eq_self] at h

/-- At most `n` leaves are mutants. -/
lemma leafMutants_le (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) (s : Config V) :
    leafMutants c s ≤ n := by
  unfold leafMutants
  calc (univ.filter fun v => v ≠ c ∧ s v = true).card ≤ (univ.erase c).card :=
        card_le_card fun v hv => by
          simp only [mem_filter] at hv
          exact mem_erase.mpr ⟨hv.2.1, mem_univ v⟩
    _ = n := by rw [card_erase_of_mem (mem_univ c), card_univ, hn, Nat.add_sub_cancel]

/-- In the all-mutant configuration all `n` leaves are mutants. -/
lemma leafMutants_true (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) :
    leafMutants c (fun _ => true) = n := by
  unfold leafMutants
  have : (univ.filter fun v : V => v ≠ c ∧ true = true) = univ.erase c := by
    ext v
    simp
  rw [this, card_erase_of_mem (mem_univ c), card_univ, hn, Nat.add_sub_cancel]

/-- In the all-resident configuration no leaf is a mutant. -/
lemma leafMutants_false (c : V) : leafMutants c (fun _ => false) = 0 := by
  simp [leafMutants]

/-- A single mutant on a leaf is one mutant leaf. -/
lemma leafMutants_single_leaf {c v : V} (hv : v ≠ c) :
    leafMutants c (fun w => decide (w = v)) = 1 := by
  unfold leafMutants
  have : (univ.filter fun w : V => w ≠ c ∧ decide (w = v) = true) = {v} := by
    ext w
    by_cases hw : w = v
    · subst hw
      simp [hv]
    · simp [hw]
  rw [this, card_singleton]

/-- A single mutant at the centre is no mutant leaf. -/
lemma leafMutants_single_centre (c : V) : leafMutants c (fun w => decide (w = c)) = 0 := by
  unfold leafMutants
  rw [card_eq_zero, filter_eq_empty_iff]
  intro w _ h
  exact h.1 (of_decide_eq_true h.2)

/-! ### The potential: values and edge-by-edge cancellation -/

/-- The potential with a resident centre is `q ^ (#mutant leaves)`. -/
lemma starPotential_of_false {c : V} {s : Config V} (hs : s c = false) (n : ℕ) (r : ℝ) :
    starPotential c n r s = starRatio n r ^ leafMutants c s := by
  simp [starPotential, hs]

/-- The potential with a mutant centre is `q ^ (#mutant leaves) * κ`. -/
lemma starPotential_of_true {c : V} {s : Config V} (hs : s c = true) (n : ℕ) (r : ℝ) :
    starPotential c n r s = starRatio n r ^ leafMutants c s * starCentreWeight n r := by
  simp [starPotential, hs]

/-- Balance along an edge whose leaf is a mutant and centre a resident:
`(1 - q)/n + r q (κ - 1) = 0`. -/
lemma star_balance_leaf {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) :
    (n : ℝ)⁻¹ * (1 - starRatio n r) + r * (starRatio n r * (starCentreWeight n r - 1)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : (n : ℝ) * r + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + r ≠ 0 := by positivity
  unfold starRatio starCentreWeight
  field_simp
  ring

/-- Balance along an edge whose centre is a mutant and leaf a resident:
`r κ (q - 1)/n + 1 - κ = 0`. -/
lemma star_balance_centre {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) :
    r * (n : ℝ)⁻¹ * (starCentreWeight n r * (starRatio n r - 1)) +
      (1 - starCentreWeight n r) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : (n : ℝ) * r + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + r ≠ 0 := by positivity
  unfold starRatio starCentreWeight
  field_simp
  ring

/-- **Edge cancellation.** Along the edge `{c, ℓ}` of the star, the fitness-weighted changes of
the potential when the centre reproduces onto `ℓ` (probability `1/n` of placement) and when `ℓ`
reproduces onto the centre cancel. -/
lemma star_edge_cancel (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ} (hr : 0 < r)
    (s : Config V) {ℓ : V} (hℓ : ℓ ≠ c) :
    fitness r s c * (n : ℝ)⁻¹ *
        (starPotential c n r (Function.update s ℓ (s c)) - starPotential c n r s) +
      fitness r s ℓ * (starPotential c n r (Function.update s c (s ℓ)) -
        starPotential c n r s) = 0 := by
  have hn0 := star_leaves_ne_zero hℓ hn
  have hcℓ : c ≠ ℓ := hℓ.symm
  have e1 : ∀ b, s ℓ = b → Function.update s ℓ b = s := fun b h => by
    rw [← h]; exact Function.update_eq_self _ _
  have e2 : ∀ b, s c = b → Function.update s c b = s := fun b h => by
    rw [← h]; exact Function.update_eq_self _ _
  cases hc : s c <;> cases hl : s ℓ
  · rw [e1 false hl, e2 false hc]
    ring
  · -- mutant leaf, resident centre
    have hL := leafMutants_update_loss hℓ s hl
    have h1 : starPotential c n r (Function.update s ℓ false) =
        starRatio n r ^ leafMutants c (Function.update s ℓ false) :=
      starPotential_of_false (by rw [Function.update_of_ne hcℓ, hc]) n r
    have h2 : starPotential c n r (Function.update s c true) =
        starRatio n r ^ leafMutants c s * starCentreWeight n r := by
      rw [starPotential_of_true (by simp), leafMutants_update_centre]
    rw [h1, h2, starPotential_of_false hc, hL]
    simp only [fitness, hc, hl, if_true, Bool.false_eq_true, if_false]
    have hb := star_balance_leaf hn0 hr
    set x := starRatio n r ^ leafMutants c (Function.update s ℓ false)
    have : 1 * (n : ℝ)⁻¹ * (x - starRatio n r ^ (leafMutants c (Function.update s ℓ false) + 1)) +
        r * (starRatio n r ^ (leafMutants c (Function.update s ℓ false) + 1) *
          starCentreWeight n r - starRatio n r ^ (leafMutants c (Function.update s ℓ false) + 1))
        = x * ((n : ℝ)⁻¹ * (1 - starRatio n r) +
          r * (starRatio n r * (starCentreWeight n r - 1))) := by
      rw [pow_succ]
      ring
    rw [this, hb, mul_zero]
  · -- mutant centre, resident leaf
    have h1 : starPotential c n r (Function.update s ℓ true) =
        starRatio n r ^ (leafMutants c s + 1) * starCentreWeight n r := by
      rw [starPotential_of_true (by rw [Function.update_of_ne hcℓ, hc]),
        leafMutants_update_gain hℓ s hl]
    have h2 : starPotential c n r (Function.update s c false) =
        starRatio n r ^ leafMutants c s := by
      rw [starPotential_of_false (by simp), leafMutants_update_centre]
    rw [h1, h2, starPotential_of_true hc]
    simp only [fitness, hc, hl, if_true, Bool.false_eq_true, if_false]
    have hb := star_balance_centre hn0 hr
    have : r * (n : ℝ)⁻¹ * (starRatio n r ^ (leafMutants c s + 1) * starCentreWeight n r -
          starRatio n r ^ leafMutants c s * starCentreWeight n r) +
        1 * (starRatio n r ^ leafMutants c s -
          starRatio n r ^ leafMutants c s * starCentreWeight n r)
        = starRatio n r ^ leafMutants c s * (r * (n : ℝ)⁻¹ *
          (starCentreWeight n r * (starRatio n r - 1)) + (1 - starCentreWeight n r)) := by
      rw [pow_succ]
      ring
    rw [this, hb, mul_zero]
  · rw [e1 true hl, e2 true hc]
    ring

/-- **Invariance of the star potential** under one Birth–death step (the content of
`star_potential_invariant`). -/
lemma starPotential_apply [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    {r : ℝ} (hr : 0 < r) (s : Config V) :
    (moranKernel (starGraph c) r hr).apply (starPotential c n r) s =
      starPotential c n r s := by
  rw [Kernel.apply, moranKernel, Distribution.map_expect, Distribution.expect]
  have hsplit : ∀ p : V × V, (pairDist (starGraph c) r hr s).weight p *
      starPotential c n r (Function.update s p.2 (s p.1)) =
      (pairDist (starGraph c) r hr s).weight p * starPotential c n r s +
        (pairDist (starGraph c) r hr s).weight p *
          (starPotential c n r (Function.update s p.2 (s p.1)) - starPotential c n r s) :=
    fun p => by ring
  simp_rw [hsplit, sum_add_distrib, ← sum_mul, (pairDist (starGraph c) r hr s).sum_one, one_mul]
  have hzero : ∑ p : V × V, (pairDist (starGraph c) r hr s).weight p *
      (starPotential c n r (Function.update s p.2 (s p.1)) - starPotential c n r s) = 0 := by
    rw [star_sum_pairs c (fun u w => (pairDist (starGraph c) r hr s).weight (u, w) *
      (starPotential c n r (Function.update s w (s u)) - starPotential c n r s))]
    · refine sum_eq_zero fun ℓ hℓ => ?_
      have hℓ : ℓ ≠ c := ne_of_mem_erase hℓ
      simp only [pairDist_weight]
      rw [star_target_centre_leaf hn hℓ, star_target_leaf_centre hℓ]
      have h := star_edge_cancel c hn hr s hℓ
      calc fitness r s c / totalFitness r s * (n : ℝ)⁻¹ *
              (starPotential c n r (Function.update s ℓ (s c)) - starPotential c n r s) +
            fitness r s ℓ / totalFitness r s * 1 *
              (starPotential c n r (Function.update s c (s ℓ)) - starPotential c n r s)
          = (totalFitness r s)⁻¹ * (fitness r s c * (n : ℝ)⁻¹ *
              (starPotential c n r (Function.update s ℓ (s c)) - starPotential c n r s) +
            fitness r s ℓ * (starPotential c n r (Function.update s c (s ℓ)) -
              starPotential c n r s)) := by ring
        _ = 0 := by rw [h, mul_zero]
    · simp only [Function.update_eq_self, sub_self, mul_zero]
    · intro u w hu hw
      simp only [pairDist_weight]
      rw [star_target_leaf_leaf hu hw, mul_zero, zero_mul]
  rw [hzero, add_zero]

end Moran
