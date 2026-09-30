import Dynamics.Absorption

/-! # The Moran process and the isothermal theorem (MOR-1, MOR-2)

Birth–death Moran process on a finite graph: mutants have fitness `r > 0`, residents
fitness `1`. In each step a parent is chosen with probability proportional to its fitness,
and its offspring replaces a uniformly random neighbour (an isolated parent replaces itself,
so nothing changes).

On a regular graph, in every configuration a step increases the number of mutants with
exactly `r` times the probability that it decreases it. Hence `(1/r)^(#mutants)` is invariant
in expectation, and on a connected regular graph the fixation probability from `k` mutants is
Moran's formula `(1 - r^{-k}) / (1 - r^{-n})` (for `r ≠ 1`), or `k/n` in the neutral case.
This is the "if" direction of the isothermal theorem of Lieberman, Hauert and Nowak (2005);
the complete graph gives Moran's classical formula (1958).
-/

namespace Moran
open Dynamics Finset Filter Topology SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A configuration marks each vertex as mutant (`true`) or resident (`false`). -/
abbrev Config (V : Type*) := V → Bool

/-- Number of mutants. -/
def mutants (s : Config V) : ℕ := (univ.filter fun i => s i = true).card

/-- Fitness: `r` for mutants, `1` for residents. -/
def fitness (r : ℝ) (s : Config V) (u : V) : ℝ := if s u then r else 1

/-- Total fitness of the population. -/
def totalFitness (r : ℝ) (s : Config V) : ℝ := ∑ u, fitness r s u

/-- Offspring placement: a uniformly random neighbour of the parent `u`, or `u` itself if it
has no neighbour. -/
noncomputable def target (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) : ℝ :=
  if G.degree u = 0 then (if w = u then 1 else 0)
  else (if G.Adj u w then (G.degree u : ℝ)⁻¹ else 0)

omit [Fintype V] [DecidableEq V] in
lemma fitness_pos {r : ℝ} (hr : 0 < r) (s : Config V) (u : V) : 0 < fitness r s u := by
  unfold fitness
  cases s u
  · norm_num
  · exact hr

omit [DecidableEq V] in
lemma totalFitness_nonneg {r : ℝ} (hr : 0 < r) (s : Config V) : 0 ≤ totalFitness r s :=
  Finset.sum_nonneg fun u _ => (fitness_pos hr s u).le

omit [DecidableEq V] in
lemma totalFitness_pos [Nonempty V] {r : ℝ} (hr : 0 < r) (s : Config V) :
    0 < totalFitness r s :=
  Finset.sum_pos (fun u _ => fitness_pos hr s u) univ_nonempty

lemma target_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) : 0 ≤ target G u w := by
  unfold target
  by_cases hdeg : G.degree u = 0
  · simp [hdeg]
    split_ifs <;> norm_num
  · simp [hdeg]
    split_ifs
    · positivity
    · rfl

lemma target_sum_one (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    ∑ w, target G u w = 1 := by
  classical
  by_cases hdeg : G.degree u = 0
  · have htarget : ∀ w, target G u w = if w = u then 1 else 0 := by
      intro w
      simp [target, hdeg]
    simp_rw [htarget]
    exact Fintype.sum_ite_eq' u (fun _ : V => (1 : ℝ))
  · have htarget : ∀ w, target G u w =
        if G.Adj u w then (G.degree u : ℝ)⁻¹ else 0 := by
      intro w
      simp [target, hdeg]
    simp_rw [htarget]
    rw [← Finset.sum_filter]
    have hnf : univ.filter (fun w => G.Adj u w) = G.neighborFinset u := by
      ext w
      simp [mem_neighborFinset]
    rw [hnf, Finset.sum_const, nsmul_eq_mul, card_neighborFinset_eq_degree]
    exact mul_inv_cancel₀ (by exact_mod_cast hdeg)

/-- The weights of (parent, offspring position) pairs are nonnegative. -/
theorem pair_weight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (s : Config V) (p : V × V) :
    0 ≤ fitness r s p.1 / totalFitness r s * target G p.1 p.2 := by
  exact mul_nonneg (div_nonneg (fitness_pos hr s p.1).le (totalFitness_nonneg hr s))
    (target_nonneg G p.1 p.2)

/-- The weights of (parent, offspring position) pairs sum to one. -/
theorem pair_weight_sum_one [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ}
    (hr : 0 < r) (s : Config V) :
    ∑ p : V × V, fitness r s p.1 / totalFitness r s * target G p.1 p.2 = 1 := by
  have hF : totalFitness r s ≠ 0 := (totalFitness_pos hr s).ne'
  rw [Fintype.sum_prod_type]
  have hinner : ∀ u, ∑ w, fitness r s u / totalFitness r s * target G u w =
      fitness r s u / totalFitness r s := by
    intro u
    rw [← Finset.mul_sum, target_sum_one G u, mul_one]
  simp_rw [hinner, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← totalFitness]
  exact mul_inv_cancel₀ hF

/-- Distribution of the (parent, offspring position) pair in one Birth–death step. -/
noncomputable def pairDist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hr : 0 < r) (s : Config V) : Distribution (V × V) where
  weight p := fitness r s p.1 / totalFitness r s * target G p.1 p.2
  nonneg p := pair_weight_nonneg G hr s p
  sum_one := pair_weight_sum_one G hr s

/-- The Birth–death Moran kernel: the offspring copies the parent's type. -/
noncomputable def moranKernel [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hr : 0 < r) : Kernel (Config V) :=
  fun s => (pairDist G r hr s).map (fun p => Function.update s p.2 (s p.1))

/-- Indicator of fixation (every vertex is a mutant). -/
def allMutant (s : Config V) : ℝ := if s = fun _ => true then 1 else 0

/-- Indicator that neither type has taken over yet. -/
noncomputable def unfixed (s : Config V) : ℝ := by
  classical
  exact if ∃ c, s = fun _ => c then 0 else 1

/-- Fixation probability: the supremum of the finite-time fixation probabilities. -/
noncomputable def fixation (K : Kernel (Config V)) (s : Config V) : ℝ :=
  ⨆ t, K.iterate t allMutant s

omit [DecidableEq V] in
lemma mutants_le_card (s : Config V) : mutants s ≤ Fintype.card V := by
  simpa [mutants, Finset.card_univ] using card_filter_le univ (fun i => s i = true)

omit [DecidableEq V] in
lemma mutants_true {s : Config V} (h : s = fun _ => true) : mutants s = Fintype.card V := by
  subst h
  unfold mutants
  have : univ.filter (fun i : V => true = true) = univ := by
    ext i
    simp
  rw [this, Finset.card_univ]

omit [DecidableEq V] in
lemma mutants_false {s : Config V} (h : s = fun _ => false) : mutants s = 0 := by
  subst h
  unfold mutants
  have : univ.filter (fun i : V => false = true) = ∅ := by
    ext i
    simp
  rw [this, Finset.card_empty]

omit [DecidableEq V] in
lemma config_of_mutants_eq_card {s : Config V} (h : mutants s = Fintype.card V) :
    s = fun _ => true := by
  unfold mutants at h
  rw [← Finset.card_univ (α := V)] at h
  have hfilter : univ.filter (fun i => s i = true) = univ :=
    eq_of_subset_of_card_le (filter_subset _ _) (Nat.le_of_eq h.symm)
  funext i
  have hi : i ∈ univ.filter (fun j => s j = true) := by
    rw [hfilter]
    exact mem_univ i
  exact (mem_filter.mp hi).2

lemma mutants_update_gain (s : Config V) {w : V} (hw : s w = false) :
    mutants (Function.update s w true) = mutants s + 1 := by
  unfold mutants
  have hmem : w ∉ univ.filter (fun i => s i = true) := by simp [hw]
  have hfilter : univ.filter (fun i => Function.update s w true i = true) =
      insert w (univ.filter fun i => s i = true) := by
    ext i
    simp only [mem_filter, mem_insert, mem_univ, true_and, Function.update_apply]
    by_cases hi : i = w
    · subst hi
      simp
    · simp [hi]
  rw [hfilter, card_insert_of_notMem hmem]

lemma mutants_update_loss (s : Config V) {w : V} (hw : s w = true) :
    mutants (Function.update s w false) = mutants s - 1 := by
  unfold mutants
  have hmem : w ∈ univ.filter (fun i => s i = true) := by simp [hw]
  have hfilter : univ.filter (fun i => Function.update s w false i = true) =
      (univ.filter fun i => s i = true).erase w := by
    ext i
    simp only [mem_filter, mem_erase, mem_univ, true_and, Function.update_apply]
    by_cases hi : i = w
    · subst hi
      simp [hw]
    · simp [hi]
  rw [hfilter, card_erase_of_mem hmem]

omit [DecidableEq V] in
lemma mutants_pos_of_true {s : Config V} {w : V} (hw : s w = true) : 1 ≤ mutants s := by
  unfold mutants
  have : w ∈ univ.filter (fun i => s i = true) := by simp [hw]
  exact Nat.succ_le_of_lt (card_pos.mpr ⟨w, this⟩)

omit [Fintype V] [DecidableEq V] in
lemma div_mul_inv_eq (a b c : ℝ) : (a / b) * c⁻¹ = a / (b * c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]

omit [Fintype V] [DecidableEq V] in
lemma one_div_pow_pred {r : ℝ} (hr : r ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    (1 / r) ^ (k - 1) = (1 / r) ^ k * r := by
  have h1 : (1 / r) * r = 1 := by
    rw [one_div, inv_mul_cancel₀ hr]
  calc
    (1 / r) ^ (k - 1) = (1 / r) ^ (k - 1) * ((1 / r) * r) := by rw [h1, mul_one]
    _ = (1 / r) ^ (k - 1) * (1 / r) * r := by rw [← mul_assoc]
    _ = (1 / r) ^ (k - 1 + 1) * r := by rw [← pow_succ]
    _ = (1 / r) ^ k * r := by rw [Nat.sub_add_cancel hk]

/-- `1` when a mutant parent replaces a resident, else `0`. -/
def upInd (s : Config V) (p : V × V) : ℝ :=
  if s p.1 = true ∧ s p.2 = false then 1 else 0

/-- `1` when a resident parent replaces a mutant, else `0`. -/
def downInd (s : Config V) (p : V × V) : ℝ :=
  if s p.1 = false ∧ s p.2 = true then 1 else 0

/-- Number of oriented edges from type `b` to the opposite type. -/
def orientedCut (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) (b : Bool) : ℝ :=
  ∑ p : V × V, if s p.1 = b ∧ s p.2 = not b ∧ G.Adj p.1 p.2 then 1 else 0

omit [DecidableEq V] in
lemma orientedCut_symm (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) (b : Bool) :
    orientedCut G s b = orientedCut G s (not b) := by
  unfold orientedCut
  refine Fintype.sum_equiv (Equiv.prodComm V V) _ _ ?_
  intro p
  have hnot : not (not b) = b := by cases b <;> rfl
  simp only [Equiv.prodComm_apply, Prod.swap]
  apply ite_congr
  · apply propext
    rw [hnot, adj_comm]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3⟩
  · intro _; rfl
  · intro _; rfl

@[simp] lemma pairDist_weight [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hr : 0 < r) (s : Config V) (p : V × V) :
    (pairDist G r hr s).weight p =
      fitness r s p.1 / totalFitness r s * target G p.1 p.2 := rfl

/-- Total weight of mutant-increasing steps. -/
noncomputable def birthMass [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hr : 0 < r) (s : Config V) : ℝ :=
  ∑ p, (pairDist G r hr s).weight p * upInd s p

/-- Total weight of mutant-decreasing steps. -/
noncomputable def deathMass [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hr : 0 < r) (s : Config V) : ℝ :=
  ∑ p, (pairDist G r hr s).weight p * downInd s p

lemma mass_isolated [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (s : Config V) (hdeg : ∀ i, G.degree i = 0) (b : Bool) :
    ∑ p, (pairDist G r hr s).weight p * (if s p.1 = b ∧ s p.2 = not b then 1 else 0) = 0 := by
  refine sum_eq_zero fun p _ => ?_
  by_cases h : s p.1 = b ∧ s p.2 = not b
  · rcases h with ⟨hp1, hp2⟩
    by_cases heq : p.2 = p.1
    · have hb : b = not b := hp1.symm.trans (by rw [heq] at hp2; exact hp2)
      cases b <;> simp at hb
    · rw [if_pos ⟨hp1, hp2⟩, pairDist_weight, target, if_pos (hdeg p.1), if_neg heq,
        mul_zero, zero_mul]
  · rw [if_neg h, mul_zero]

lemma typed_mass [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : d ≠ 0)
    (hreg : ∀ i, G.degree i = d) {r : ℝ} (hr : 0 < r) (s : Config V) (b : Bool) (c : ℝ)
    (hfit : ∀ u, s u = b → fitness r s u = c) :
    ∑ p, (pairDist G r hr s).weight p * (if s p.1 = b ∧ s p.2 = not b then 1 else 0) =
      c / (totalFitness r s * (d : ℝ)) * orientedCut G s b := by
  have hpoint : ∀ p, (pairDist G r hr s).weight p *
      (if s p.1 = b ∧ s p.2 = not b then 1 else 0) =
      c / (totalFitness r s * (d : ℝ)) *
        (if s p.1 = b ∧ s p.2 = not b ∧ G.Adj p.1 p.2 then 1 else 0) := by
    intro p
    by_cases hb : s p.1 = b
    · by_cases hw : s p.2 = not b
      · by_cases hadj : G.Adj p.1 p.2
        · rw [if_pos ⟨hb, hw⟩, if_pos ⟨hb, hw, hadj⟩, mul_one, mul_one, pairDist_weight]
          have hdeg : G.degree p.1 ≠ 0 := by
            rw [hreg p.1]
            exact hd
          rw [target, if_neg hdeg, if_pos hadj, hreg p.1, hfit p.1 hb, div_mul_inv_eq]
        · rw [if_pos ⟨hb, hw⟩, if_neg (fun h => hadj h.2.2), mul_one, mul_zero, pairDist_weight]
          have hdeg : G.degree p.1 ≠ 0 := by
            rw [hreg p.1]
            exact hd
          rw [target, if_neg hdeg, if_neg hadj, mul_zero]
      · rw [if_neg (fun h => hw h.2), if_neg (fun h => hw h.2.1), mul_zero, mul_zero]
    · rw [if_neg (fun h => hb h.1), if_neg (fun h => hb h.1), mul_zero, mul_zero]
  simp_rw [hpoint, ← Finset.mul_sum]
  rfl

lemma birth_indicator [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ) (hr : 0 < r)
    (s : Config V) :
    birthMass G r hr s =
      ∑ p, (pairDist G r hr s).weight p * (if s p.1 = true ∧ s p.2 = not true then 1 else 0) := by
  unfold birthMass upInd
  rfl

lemma death_indicator [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ) (hr : 0 < r)
    (s : Config V) :
    deathMass G r hr s =
      ∑ p, (pairDist G r hr s).weight p *
        (if s p.1 = false ∧ s p.2 = not false then 1 else 0) := by
  unfold deathMass downInd
  rfl

/-- On a regular graph the probability of gaining a mutant is `r` times the probability of losing one. -/
lemma birth_eq_r_death [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : ∀ i, G.degree i = d) {r : ℝ} (hr : 0 < r) (s : Config V) :
    birthMass G r hr s = r * deathMass G r hr s := by
  by_cases hd : d = 0
  · have hdeg : ∀ i, G.degree i = 0 := fun i => by rw [hreg i, hd]
    have hb := mass_isolated G hr s hdeg true
    have hdth := mass_isolated G hr s hdeg false
    rw [birth_indicator, death_indicator, hb, hdth, mul_zero]
  · have hb := typed_mass G hd hreg hr s true r (fun u hu => by simp [fitness, hu])
    have hdth := typed_mass G hd hreg hr s false 1 (fun u hu => by simp [fitness, hu])
    rw [birth_indicator, death_indicator, hb, hdth]
    have hcut : orientedCut G s true = orientedCut G s false := orientedCut_symm G s true
    rw [hcut, div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_assoc]

lemma pot_after {r : ℝ} (hr0 : r ≠ 0) (s : Config V) (u w : V) :
    (1 / r) ^ mutants (Function.update s w (s u)) =
      (1 / r) ^ mutants s +
        ((1 / r) ^ mutants s * (1 / r - 1)) * upInd s (u, w) +
        ((1 / r) ^ mutants s * (r - 1)) * downInd s (u, w) := by
  cases hu : s u <;> cases hw : s w
  · have hup : upInd s (u, w) = 0 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 0 := by simp [downInd, hu, hw]
    have heq : Function.update s w false = s := by
      rw [← hw]
      exact Function.update_eq_self _ _
    rw [heq, hup, hdown, mul_zero, mul_zero, add_zero, add_zero]
  · have hup : upInd s (u, w) = 0 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 1 := by simp [downInd, hu, hw]
    rw [hup, hdown, mul_zero, add_zero, mul_one, mutants_update_loss s hw,
      one_div_pow_pred hr0 (mutants_pos_of_true hw)]
    conv_lhs =>
      arg 2
      rw [show r = 1 + (r - 1) by ring]
    rw [mul_add, mul_one]
  · have hup : upInd s (u, w) = 1 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 0 := by simp [downInd, hu, hw]
    rw [hup, hdown, mul_one, mul_zero, add_zero, mutants_update_gain s hw, pow_succ]
    conv_lhs =>
      arg 2
      rw [show 1 / r = 1 + (1 / r - 1) by ring]
    rw [mul_add, mul_one]
  · have hup : upInd s (u, w) = 0 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 0 := by simp [downInd, hu, hw]
    have heq : Function.update s w true = s := by
      rw [← hw]
      exact Function.update_eq_self _ _
    rw [heq, hup, hdown, mul_zero, mul_zero, add_zero, add_zero]

lemma mutants_after (s : Config V) (u w : V) :
    (mutants (Function.update s w (s u)) : ℝ) =
      (mutants s : ℝ) + 1 * upInd s (u, w) + (-1) * downInd s (u, w) := by
  cases hu : s u <;> cases hw : s w
  · have hup : upInd s (u, w) = 0 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 0 := by simp [downInd, hu, hw]
    have heq : Function.update s w false = s := by
      rw [← hw]
      exact Function.update_eq_self _ _
    rw [heq, hup, hdown]
    ring
  · have hup : upInd s (u, w) = 0 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 1 := by simp [downInd, hu, hw]
    rw [mutants_update_loss s hw, hup, hdown, Nat.cast_sub (mutants_pos_of_true hw)]
    ring
  · have hup : upInd s (u, w) = 1 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 0 := by simp [downInd, hu, hw]
    rw [mutants_update_gain s hw, hup, hdown, Nat.cast_add, Nat.cast_one]
    ring
  · have hup : upInd s (u, w) = 0 := by simp [upInd, hu, hw]
    have hdown : downInd s (u, w) = 0 := by simp [downInd, hu, hw]
    have heq : Function.update s w true = s := by
      rw [← hw]
      exact Function.update_eq_self _ _
    rw [heq, hup, hdown]
    ring

lemma apply_affine [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (s : Config V) (f : Config V → ℝ) (cUp cDown : ℝ)
    (hupd : ∀ u w, f (Function.update s w (s u)) =
      f s + cUp * upInd s (u, w) + cDown * downInd s (u, w)) :
    (moranKernel G r hr).apply f s =
      f s + cUp * birthMass G r hr s + cDown * deathMass G r hr s := by
  rw [Kernel.apply, moranKernel, Distribution.map_expect, Distribution.expect]
  have hpt : ∀ p, (pairDist G r hr s).weight p * f (Function.update s p.2 (s p.1)) =
      (pairDist G r hr s).weight p * f s +
        (pairDist G r hr s).weight p * (cUp * upInd s p) +
        (pairDist G r hr s).weight p * (cDown * downInd s p) := by
    intro p
    rw [hupd p.1 p.2, mul_add, mul_add]
  simp_rw [hpt, Finset.sum_add_distrib]
  have h1 : ∑ p, (pairDist G r hr s).weight p * f s = f s := by
    rw [← Finset.sum_mul, (pairDist G r hr s).sum_one, one_mul]
  have h2 : ∑ p, (pairDist G r hr s).weight p * (cUp * upInd s p) =
      cUp * birthMass G r hr s := by
    simp_rw [fun p => mul_left_comm ((pairDist G r hr s).weight p) cUp (upInd s p)]
    rw [← Finset.mul_sum]
    rfl
  have h3 : ∑ p, (pairDist G r hr s).weight p * (cDown * downInd s p) =
      cDown * deathMass G r hr s := by
    simp_rw [fun p => mul_left_comm ((pairDist G r hr s).weight p) cDown (downInd s p)]
    rw [← Finset.mul_sum]
    rfl
  rw [h1, h2, h3]

/-- **Invariance.** On a regular graph, `(1/r)^(#mutants)` is preserved in expectation by one
Moran step. -/
theorem moran_potential_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ i, G.degree i = d) {r : ℝ} (hr : 0 < r) (s : Config V) :
    (moranKernel G r hr).apply (fun t => (1 / r) ^ mutants t) s = (1 / r) ^ mutants s := by
  have hbirth := birth_eq_r_death G d hreg hr s
  rw [apply_affine G hr s (fun t => (1 / r) ^ mutants t)
    ((1 / r) ^ mutants s * (1 / r - 1)) ((1 / r) ^ mutants s * (r - 1))
    (fun u w => pot_after hr.ne' s u w)]
  have hcancel (ρ A B D : ℝ) :
      ρ + (ρ * A) * (r * D) + (ρ * B) * D = ρ + ρ * (A * r + B) * D := by ring
  rw [hbirth, hcancel]
  have hcoef : (1 / r - 1) * r + (r - 1) = 0 := by
    rw [sub_mul, one_div, inv_mul_cancel₀ hr.ne', one_mul]
    ring
  rw [hcoef, mul_zero, zero_mul, add_zero]

/-- **Neutral invariance.** On a regular graph with `r = 1`, the number of mutants is preserved
in expectation by one Moran step. -/
theorem moran_mutants_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ i, G.degree i = d) (s : Config V) :
    (moranKernel G 1 one_pos).apply (fun t => (mutants t : ℝ)) s = mutants s := by
  have hbirth := birth_eq_r_death G d hreg one_pos s
  simp only [one_mul] at hbirth
  rw [apply_affine G one_pos s (fun t => (mutants t : ℝ)) 1 (-1) (fun u w => mutants_after s u w)]
  rw [hbirth]
  ring

omit [DecidableEq V] in
lemma unfixed_binary (s : Config V) : unfixed s = 0 ∨ unfixed s = 1 := by
  unfold unfixed
  split <;> simp

omit [DecidableEq V] in
lemma unfixed_const (c : Bool) : unfixed (fun _ : V => c) = 0 := by
  unfold unfixed
  exact if_pos ⟨c, rfl⟩

omit [DecidableEq V] in
lemma unfixed_of_mixed (s : Config V) (h : ¬ ∃ c, s = fun _ => c) : unfixed s = 1 := by
  unfold unfixed
  exact if_neg h

omit [DecidableEq V] in
lemma unfixed_le_one (s : Config V) : unfixed s ≤ 1 := by
  rcases unfixed_binary s with h | h <;> simp [h]

omit [DecidableEq V] in
lemma allMutant_nonneg (s : Config V) : 0 ≤ allMutant s := by
  unfold allMutant
  split <;> norm_num

omit [DecidableEq V] in
lemma allMutant_le_one (s : Config V) : allMutant s ≤ 1 := by
  unfold allMutant
  split <;> norm_num

omit [DecidableEq V] in
lemma allMutant_true : allMutant (fun _ : V => true) = 1 := by
  simp [allMutant]

omit [DecidableEq V] in
lemma allMutant_false [Nonempty V] : allMutant (fun _ : V => false) = 0 := by
  have hne : (fun _ : V => false) ≠ fun _ => true := by
    intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    have := congr_fun h v
    simp at this
  rw [allMutant, if_neg hne]

lemma moran_constant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (c : Bool) (f : Config V → ℝ) :
    (moranKernel G r hr).apply f (fun _ => c) = f (fun _ => c) := by
  rw [Kernel.apply, moranKernel, Distribution.map_expect]
  have : ∀ p : V × V, Function.update (fun _ : V => c) p.2 ((fun _ => c) p.1) = fun _ => c :=
    fun p => Function.update_eq_self p.2 (fun _ => c)
  simp_rw [this]
  exact (pairDist G r hr (fun _ => c)).expect_const _

omit [Fintype V] [DecidableEq V] in
lemma expect_lt_one {α : Type*} [Fintype α] (p : Distribution α) (f : α → ℝ)
    (hf : ∀ a, f a ≤ 1) (b : α) (hb : 0 < p.weight b) (hfb : f b < 1) : p.expect f < 1 := by
  calc
    p.expect f < p.expect (fun _ => 1) :=
      sum_lt_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a) (p.nonneg a))
        ⟨b, mem_univ b, mul_lt_mul_of_pos_left hfb hb⟩
    _ = 1 := p.expect_const 1

omit [Fintype V] [DecidableEq V] in
lemma map_weight_pos {α β : Type*} [Fintype α] [Fintype β] (p : Distribution α) (f : α → β)
    (a : α) (ha : 0 < p.weight a) : 0 < (p.map f).weight (f a) := by
  classical
  dsimp only [Distribution.map]
  refine lt_of_lt_of_le ?_ (single_le_sum (fun x _ => ?_) (mem_univ a))
  · rw [if_pos rfl]
    exact ha
  · split
    · exact p.nonneg x
    · exact le_rfl

lemma moran_weight_pos [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (s : Config V) {u w : V} (hadj : G.Adj u w) (hu : s u = true) :
    0 < (moranKernel G r hr s).weight (Function.update s w true) := by
  unfold moranKernel
  have hmap : Function.update s w (s u) = Function.update s w true := by simp [hu]
  rw [← hmap]
  refine map_weight_pos (pairDist G r hr s) _ (u, w) ?_
  rw [pairDist_weight]
  have hdeg : 0 < G.degree u := hadj.degree_pos_left
  rw [show fitness r s u = r by simp [fitness, hu]]
  rw [show target G u w = (G.degree u : ℝ)⁻¹ by rw [target, if_neg hdeg.ne', if_pos hadj]]
  exact mul_pos (div_pos hr (totalFitness_pos hr s)) (inv_pos.mpr (by exact_mod_cast hdeg))

lemma unfixed_step [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (s : Config V) : (moranKernel G r hr).apply unfixed s ≤ unfixed s := by
  by_cases hs : ∃ c, s = fun _ => c
  · obtain ⟨c, rfl⟩ := hs
    rw [moran_constant G hr c unfixed]
  · rw [unfixed_of_mixed s hs]
    rw [Kernel.apply]
    calc
      (moranKernel G r hr s).expect unfixed ≤ (moranKernel G r hr s).expect (fun _ => 1) :=
        (moranKernel G r hr s).expect_mono unfixed_le_one
      _ = 1 := (moranKernel G r hr s).expect_const 1

lemma unfixed_access [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    {r : ℝ} (hr : 0 < r) (s : Config V) :
    ∃ n, (moranKernel G r hr).iterate n unfixed s < 1 := by
  classical
  suffices ∀ k, ∀ s : Config V, Fintype.card V - mutants s = k →
      ∃ n, (moranKernel G r hr).iterate n unfixed s < 1 from this _ s rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro s hk
    by_cases hconst : ∃ c, s = fun _ => c
    · obtain ⟨c, rfl⟩ := hconst
      refine ⟨0, ?_⟩
      rw [Kernel.iterate_zero, unfixed_const]
      norm_num
    · have htrue : ∃ u, s u = true := by
        by_contra h
        push Not at h
        apply hconst
        refine ⟨false, ?_⟩
        funext v
        cases hv : s v
        · rfl
        · exact (h v hv).elim
      have hfalse : ∃ w, s w = false := by
        by_contra h
        push Not at h
        apply hconst
        refine ⟨true, ?_⟩
        funext v
        cases hv : s v
        · exact (h v hv).elim
        · rfl
      obtain ⟨u, hu⟩ := htrue
      obtain ⟨w0, hw0⟩ := hfalse
      obtain ⟨walk⟩ := hc u w0
      obtain ⟨d, _, hfst, hsnd⟩ := walk.exists_boundary_dart {i | s i = true} hu
        (by simpa using hw0)
      have hdu : s d.fst = true := by simpa using hfst
      have hdw : s d.snd = false := by
        cases hsd : s d.snd
        · rfl
        · exact (hsnd (by simp [hsd])).elim
      let t := Function.update s d.snd true
      have hgain : mutants t = mutants s + 1 := mutants_update_gain s hdw
      have hsm : mutants s < Fintype.card V := by
        refine lt_of_le_of_ne (mutants_le_card s) ?_
        intro heq
        rw [config_of_mutants_eq_card heq] at hdw
        simp at hdw
      have hlt : Fintype.card V - mutants t < k := by
        rw [hgain, ← hk]
        omega
      obtain ⟨n, hn⟩ := ih (Fintype.card V - mutants t) hlt t rfl
      refine ⟨n + 1, ?_⟩
      rw [Kernel.iterate_succ]
      exact expect_lt_one (moranKernel G r hr s) ((moranKernel G r hr).iterate n unfixed)
        (fun a => by
          have hle := (moranKernel G r hr).iterate_mono n unfixed_le_one a
          simp [Kernel.iterate_const] at hle
          exact hle)
        t (moran_weight_pos G hr s d.adj hdu) hn

/-- **Absorption.** On a connected graph, the probability that neither type has fixed tends to
zero. -/
theorem moran_unfixed_tendsto [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {r : ℝ} (hr : 0 < r) (s : Config V) :
    Tendsto (fun t => (moranKernel G r hr).iterate t unfixed s) atTop (𝓝 0) :=
  (moranKernel G r hr).finite_absorption unfixed unfixed_binary (unfixed_step G hr)
    (unfixed_access G hc hr) s

lemma allMutant_step [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (s : Config V) : allMutant s ≤ (moranKernel G r hr).apply allMutant s := by
  by_cases hs : s = fun _ => true
  · subst hs
    rw [moran_constant G hr true allMutant]
  · rw [allMutant, if_neg hs, Kernel.apply]
    exact (moranKernel G r hr s).expect_nonneg allMutant_nonneg

lemma fixation_mono [Nonempty V] (K : Kernel (Config V))
    (hstep : ∀ t, allMutant t ≤ K.apply allMutant t) (s : Config V) :
    Monotone fun n => K.iterate n allMutant s := by
  apply monotone_nat_of_le_succ
  intro n
  rw [K.iterate_add_time]
  exact K.iterate_mono n hstep s

lemma fixation_le_one [Nonempty V] (K : Kernel (Config V)) (n : ℕ) (s : Config V) :
    K.iterate n allMutant s ≤ 1 := by
  have hle := K.iterate_mono n allMutant_le_one s
  simp [Kernel.iterate_const] at hle
  exact hle

lemma fixation_tendsto [Nonempty V] (K : Kernel (Config V))
    (hstep : ∀ t, allMutant t ≤ K.apply allMutant t) (s : Config V) :
    Tendsto (fun n => K.iterate n allMutant s) atTop (𝓝 (fixation K s)) :=
  tendsto_atTop_ciSup (fixation_mono K hstep s)
    ⟨1, by rintro _ ⟨n, rfl⟩; exact fixation_le_one K n s⟩

/-- Compare an invariant observable with fixation once it is sandwiched by `unfixed`. -/
lemma fixation_eq_of_invariant [Nonempty V] (K : Kernel (Config V)) (ψ : Config V → ℝ)
    (hstepU : ∀ t, K.apply unfixed t ≤ unfixed t)
    (hacc : ∀ t, ∃ n, K.iterate n unfixed t < 1)
    (hinv : K.apply ψ = ψ)
    (hsand : ∀ t, allMutant t ≤ ψ t ∧ ψ t ≤ allMutant t + unfixed t)
    (habs : ∀ t, allMutant t ≤ K.apply allMutant t) (s : Config V) :
    fixation K s = ψ s := by
  have htend := fixation_tendsto K habs s
  have herr : ∀ n, 0 ≤ ψ s - K.iterate n allMutant s ∧
      ψ s - K.iterate n allMutant s ≤ K.iterate n unfixed s := by
    intro n
    have hinvn := congrFun (K.iterate_invariant hinv n) s
    have hlo := K.iterate_mono n (fun t => (hsand t).1) s
    have hhi := K.iterate_mono n (fun t => (hsand t).2) s
    rw [hinvn] at hlo hhi
    rw [K.iterate_add] at hhi
    constructor <;> linarith
  have hz : Tendsto (fun n => ψ s - K.iterate n allMutant s) atTop (𝓝 0) :=
    squeeze_zero (fun n => (herr n).1) (fun n => (herr n).2)
      (K.finite_absorption unfixed unfixed_binary hstepU hacc s)
  have hprob : Tendsto (fun n => K.iterate n allMutant s) atTop (𝓝 (ψ s)) := by
    have hcst : Tendsto (fun _ : ℕ => ψ s) atTop (𝓝 (ψ s)) := tendsto_const_nhds
    simpa using hcst.sub hz
  exact tendsto_nhds_unique htend hprob

omit [Fintype V] [DecidableEq V] in
lemma one_div_pow_ne_one {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    (1 / r) ^ n ≠ 1 := by
  intro h
  rcases (pow_eq_one_iff_of_ne_zero hn).mp h with h | ⟨h, _⟩
  · rw [div_eq_iff hr.ne'] at h
    simp only [one_mul] at h
    exact hr1 h.symm
  · linarith [div_pos one_pos hr]

noncomputable def moranPsi (r : ℝ) (t : Config V) : ℝ :=
  (1 - (1 / r) ^ mutants t) / (1 - (1 / r) ^ Fintype.card V)

noncomputable def neutralPsi (t : Config V) : ℝ := (mutants t : ℝ) / Fintype.card V

omit [DecidableEq V] in
lemma moranPsi_bounds [Nonempty V] {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (t : Config V) :
    0 ≤ moranPsi r t ∧ moranPsi r t ≤ 1 := by
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hk : mutants t ≤ Fintype.card V := mutants_le_card t
  have hpos : 0 < 1 / r := div_pos one_pos hr
  unfold moranPsi
  rcases hr1.lt_or_gt with hlt | hgt
  · have ha : 1 < 1 / r := (one_lt_div hr).mpr hlt
    have hpow : (1 / r) ^ mutants t ≤ (1 / r) ^ Fintype.card V :=
      pow_le_pow_right₀ ha.le hk
    have hnum : 1 - (1 / r) ^ mutants t ≤ 0 := sub_nonpos.mpr (one_le_pow₀ ha.le)
    have hden : 1 - (1 / r) ^ Fintype.card V < 0 := sub_neg.mpr (one_lt_pow₀ ha hn)
    have hle : 1 - (1 / r) ^ Fintype.card V ≤ 1 - (1 / r) ^ mutants t :=
      sub_le_sub_left hpow 1
    exact ⟨div_nonneg_of_nonpos hnum hden.le, (div_le_one_iff).2 (Or.inr (Or.inr ⟨hden, hle⟩))⟩
  · have ha : 1 / r < 1 := (div_lt_one hr).mpr hgt
    have hpow : (1 / r) ^ Fintype.card V ≤ (1 / r) ^ mutants t :=
      pow_le_pow_of_le_one hpos.le ha.le hk
    have hnum : 0 ≤ 1 - (1 / r) ^ mutants t := sub_nonneg.mpr (pow_le_one₀ hpos.le ha.le)
    have hden : 0 < 1 - (1 / r) ^ Fintype.card V := sub_pos.mpr (pow_lt_one₀ hpos.le ha hn)
    have hle : 1 - (1 / r) ^ mutants t ≤ 1 - (1 / r) ^ Fintype.card V :=
      sub_le_sub_left hpow 1
    exact ⟨div_nonneg hnum hden.le, (div_le_one hden).mpr hle⟩

omit [DecidableEq V] in
lemma moranPsi_all [Nonempty V] {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    moranPsi r (fun _ : V => true) = 1 := by
  unfold moranPsi
  rw [mutants_true rfl]
  have hn : (1 / r) ^ Fintype.card V ≠ 1 :=
    one_div_pow_ne_one hr hr1 (Fintype.card_ne_zero (α := V))
  exact div_self (sub_ne_zero.mpr hn.symm)

omit [DecidableEq V] in
lemma moranPsi_none {r : ℝ} : moranPsi r (fun _ : V => false) = 0 := by
  unfold moranPsi
  rw [mutants_false rfl, pow_zero, sub_self, zero_div]

omit [DecidableEq V] in
lemma moranPsi_sandwich [Nonempty V] {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (t : Config V) :
    allMutant t ≤ moranPsi r t ∧ moranPsi r t ≤ allMutant t + unfixed t := by
  by_cases ht : t = fun _ => true
  · subst ht
    rw [allMutant_true, moranPsi_all hr hr1, unfixed_const]
    constructor <;> norm_num
  · by_cases hf : t = fun _ => false
    · subst hf
      rw [allMutant_false, moranPsi_none, unfixed_const]
      constructor <;> norm_num
    · have ha : allMutant t = 0 := by rw [allMutant, if_neg ht]
      have hu : unfixed t = 1 := unfixed_of_mixed t (by
        rintro ⟨c, hc⟩
        cases c with
        | false => exact hf hc
        | true => exact ht hc)
      rw [ha, hu, zero_add]
      exact moranPsi_bounds hr hr1 t

lemma moranPsi_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : ∀ i, G.degree i = d) {r : ℝ} (hr : 0 < r) (s : Config V) :
    (moranKernel G r hr).apply (moranPsi r) s = moranPsi r s := by
  unfold moranPsi
  rw [Kernel.apply]
  have hcomm : ∀ t : Config V,
      (1 - (1 / r) ^ mutants t) / (1 - (1 / r) ^ Fintype.card V) =
        (1 - (1 / r) ^ Fintype.card V)⁻¹ * (1 - (1 / r) ^ mutants t) := by
    intro t
    rw [div_eq_mul_inv, mul_comm]
  simp_rw [hcomm]
  rw [Distribution.expect_mul, Distribution.expect_sub, Distribution.expect_const]
  have hpot : (moranKernel G r hr s).expect (fun t => (1 / r) ^ mutants t) =
      (1 / r) ^ mutants s := by
    rw [← Kernel.apply]
    exact moran_potential_invariant G d hreg hr s
  rw [hpot, mul_comm]

omit [DecidableEq V] in
lemma neutralPsi_bounds [Nonempty V] (t : Config V) : 0 ≤ neutralPsi t ∧ neutralPsi t ≤ 1 := by
  unfold neutralPsi
  have hn : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  exact ⟨div_nonneg (Nat.cast_nonneg _) hn.le,
    (div_le_one hn).mpr (by exact_mod_cast mutants_le_card t)⟩

omit [DecidableEq V] in
lemma neutralPsi_all [Nonempty V] : neutralPsi (fun _ : V => true) = 1 := by
  unfold neutralPsi
  rw [mutants_true rfl]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

omit [DecidableEq V] in
lemma neutralPsi_none : neutralPsi (fun _ : V => false) = 0 := by
  unfold neutralPsi
  rw [mutants_false rfl, Nat.cast_zero, zero_div]

omit [DecidableEq V] in
lemma neutralPsi_sandwich [Nonempty V] (t : Config V) :
    allMutant t ≤ neutralPsi t ∧ neutralPsi t ≤ allMutant t + unfixed t := by
  by_cases ht : t = fun _ => true
  · subst ht
    rw [allMutant_true, neutralPsi_all, unfixed_const]
    constructor <;> norm_num
  · by_cases hf : t = fun _ => false
    · subst hf
      rw [allMutant_false, neutralPsi_none, unfixed_const]
      constructor <;> norm_num
    · have ha : allMutant t = 0 := by rw [allMutant, if_neg ht]
      have hu : unfixed t = 1 := unfixed_of_mixed t (by
        rintro ⟨c, hc⟩
        cases c with
        | false => exact hf hc
        | true => exact ht hc)
      rw [ha, hu, zero_add]
      exact neutralPsi_bounds t

lemma neutralPsi_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : ∀ i, G.degree i = d) (s : Config V) :
    (moranKernel G 1 one_pos).apply neutralPsi s = neutralPsi s := by
  unfold neutralPsi
  rw [Kernel.apply]
  have hcomm : ∀ t : Config V,
      (mutants t : ℝ) / Fintype.card V = (Fintype.card V : ℝ)⁻¹ * (mutants t : ℝ) := by
    intro t
    rw [div_eq_mul_inv, mul_comm]
  simp_rw [hcomm]
  rw [Distribution.expect_mul]
  have hmut : (moranKernel G 1 one_pos s).expect (fun t => (mutants t : ℝ)) = mutants s := by
    rw [← Kernel.apply]
    exact moran_mutants_invariant G d hreg s
  rw [hmut, mul_comm]

/-- **Isothermal theorem ("if" direction).** On a connected regular graph, the fixation
probability from `k` mutants is Moran's formula `(1 - r^{-k}) / (1 - r^{-n})`. -/
theorem isothermal [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (d : ℕ) (hreg : ∀ i, G.degree i = d) {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (s : Config V) :
    fixation (moranKernel G r hr) s =
      (1 - (1 / r) ^ mutants s) / (1 - (1 / r) ^ Fintype.card V) := by
  have hinv : (moranKernel G r hr).apply (moranPsi r) = moranPsi r := by
    funext t
    exact moranPsi_invariant G d hreg hr t
  exact fixation_eq_of_invariant (moranKernel G r hr) (moranPsi r)
    (unfixed_step G hr) (unfixed_access G hc hr) hinv (moranPsi_sandwich hr hr1)
    (allMutant_step G hr) s

/-- **Neutral case.** On a connected regular graph with `r = 1`, the fixation probability is the
initial fraction of mutants. -/
theorem isothermal_neutral [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (d : ℕ) (hreg : ∀ i, G.degree i = d) (s : Config V) :
    fixation (moranKernel G 1 one_pos) s = (mutants s : ℝ) / Fintype.card V := by
  have hinv : (moranKernel G 1 one_pos).apply neutralPsi = neutralPsi := by
    funext t
    exact neutralPsi_invariant G d hreg t
  exact fixation_eq_of_invariant (moranKernel G 1 one_pos) neutralPsi
    (unfixed_step G one_pos) (unfixed_access G hc one_pos) hinv neutralPsi_sandwich
    (allMutant_step G one_pos) s

/-- **Moran's formula (1958).** On the complete graph, the fixation probability from `k`
mutants is `(1 - r^{-k}) / (1 - r^{-n})`. -/
theorem moran_formula [Nonempty V] {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (s : Config V) :
    fixation (moranKernel (⊤ : SimpleGraph V) r hr) s =
      (1 - (1 / r) ^ mutants s) / (1 - (1 / r) ^ Fintype.card V) :=
  isothermal (⊤ : SimpleGraph V) connected_top (Fintype.card V - 1)
    (fun v => complete_graph_degree v) hr hr1 s

end Moran
