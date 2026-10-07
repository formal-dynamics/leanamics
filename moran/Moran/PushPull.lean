import Moran.Isothermal

/-! # Push versus pull: neutral fixation on arbitrary graphs (VOT-4)

Two sequential neutral voter dynamics on a finite graph:

* **push** (Birth–death, the neutral Moran process `moranKernel G 1`): a uniformly random vertex
  places a copy of its type on a uniformly random neighbour;
* **pull** (death–Birth, `pullKernel G`): a uniformly random vertex adopts the type of a uniformly
  random neighbour.

On the complete graph they coincide, but on an irregular graph they do not: from a mutant set
`S` on a connected graph, push fixes with probability `∑_{v ∈ S} 1/deg v / ∑_v 1/deg v`, while
pull fixes with probability `∑_{v ∈ S} deg v / ∑_v deg v`. Each follows from an invariant
"reproductive value" (`1/deg` for push, `deg` for pull), whose expected change vanishes edge by
edge on every graph.
-/

namespace Moran
open Dynamics Finset Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weight of the pair (vertex that updates, neighbour it copies) in one death–Birth step. -/
noncomputable def pullWeight (G : SimpleGraph V) [DecidableRel G.Adj] (p : V × V) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ * target G p.1 p.2

/-- The death–Birth pair weights are nonnegative. -/
theorem pull_weight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (p : V × V) :
    0 ≤ pullWeight G p := by
  unfold pullWeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (target_nonneg G p.1 p.2)

/-- The death–Birth pair weights sum to one. -/
theorem pull_weight_sum_one [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ p : V × V, pullWeight G p = 1 := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ u, ∑ w, pullWeight G (u, w) = (Fintype.card V : ℝ)⁻¹ := by
    intro u
    unfold pullWeight
    rw [← Finset.mul_sum, target_sum_one, mul_one]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]

/-- Distribution of (vertex that updates, neighbour it copies). -/
noncomputable def pullDist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Distribution (V × V) where
  weight := pullWeight G
  nonneg := pull_weight_nonneg G
  sum_one := pull_weight_sum_one G

/-- The death–Birth (sequential pull voter) kernel: a uniformly random vertex adopts the type of
a uniformly random neighbour (an isolated vertex keeps its type). -/
noncomputable def pullKernel [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Kernel (Config V) :=
  fun s => (pullDist G).map (fun p => Function.update s p.1 (s p.2))

/-- Reproductive value of the mutants under push: `∑_{v mutant} 1 / deg v`. -/
noncomputable def pushValue (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) : ℝ :=
  ∑ v ∈ univ.filter (fun v => s v = true), (G.degree v : ℝ)⁻¹

/-- Reproductive value of the mutants under pull: `∑_{v mutant} deg v`. -/
noncomputable def pullValue (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) : ℝ :=
  ∑ v ∈ univ.filter (fun v => s v = true), (G.degree v : ℝ)

/-- Indicator of the mutant type, as a real number. -/
def typeInd (s : Config V) (v : V) : ℝ := if s v = true then 1 else 0

omit [Fintype V] [DecidableEq V] in
lemma typeInd_true {s : Config V} {v : V} (h : s v = true) : typeInd s v = 1 := by
  simp [typeInd, h]

omit [Fintype V] [DecidableEq V] in
lemma typeInd_false {s : Config V} {v : V} (h : s v = false) : typeInd s v = 0 := by
  simp [typeInd, h]

lemma pushValue_gain (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) {w : V}
    (hw : s w = false) :
    pushValue G (Function.update s w true) = pushValue G s + (G.degree w : ℝ)⁻¹ := by
  unfold pushValue
  have hmem : w ∉ univ.filter (fun i => s i = true) := by simp [hw]
  have hfilter : univ.filter (fun i => Function.update s w true i = true) =
      insert w (univ.filter fun i => s i = true) := by
    ext i
    simp only [mem_filter, mem_insert, mem_univ, true_and, Function.update_apply]
    by_cases hi : i = w
    · subst hi
      simp
    · simp [hi]
  rw [hfilter, Finset.sum_insert hmem]
  exact add_comm _ _

lemma pushValue_loss (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) {w : V}
    (hw : s w = true) :
    pushValue G (Function.update s w false) = pushValue G s - (G.degree w : ℝ)⁻¹ := by
  unfold pushValue
  have hmem : w ∈ univ.filter (fun i => s i = true) := by simp [hw]
  have hfilter : univ.filter (fun i => Function.update s w false i = true) =
      (univ.filter fun i => s i = true).erase w := by
    ext i
    simp only [mem_filter, mem_erase, mem_univ, true_and, Function.update_apply]
    by_cases hi : i = w
    · subst hi
      simp [hw]
    · simp [hi]
  rw [hfilter]
  have hsum := Finset.sum_erase_add (univ.filter fun i => s i = true)
    (fun i => (G.degree i : ℝ)⁻¹) hmem
  rw [← hsum]
  ring

lemma pullValue_gain (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) {u : V}
    (hu : s u = false) :
    pullValue G (Function.update s u true) = pullValue G s + (G.degree u : ℝ) := by
  unfold pullValue
  have hmem : u ∉ univ.filter (fun i => s i = true) := by simp [hu]
  have hfilter : univ.filter (fun i => Function.update s u true i = true) =
      insert u (univ.filter fun i => s i = true) := by
    ext i
    simp only [mem_filter, mem_insert, mem_univ, true_and, Function.update_apply]
    by_cases hi : i = u
    · subst hi
      simp
    · simp [hi]
  rw [hfilter, Finset.sum_insert hmem]
  exact add_comm _ _

lemma pullValue_loss (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) {u : V}
    (hu : s u = true) :
    pullValue G (Function.update s u false) = pullValue G s - (G.degree u : ℝ) := by
  unfold pullValue
  have hmem : u ∈ univ.filter (fun i => s i = true) := by simp [hu]
  have hfilter : univ.filter (fun i => Function.update s u false i = true) =
      (univ.filter fun i => s i = true).erase u := by
    ext i
    simp only [mem_filter, mem_erase, mem_univ, true_and, Function.update_apply]
    by_cases hi : i = u
    · subst hi
      simp [hu]
    · simp [hi]
  rw [hfilter]
  have hsum := Finset.sum_erase_add (univ.filter fun i => s i = true)
    (fun i => (G.degree i : ℝ)) hmem
  rw [← hsum]
  ring

/-- Updating `w` to the type of `u` changes push value by `(1_{s u} - 1_{s w}) / deg w`. -/
lemma pushValue_update (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) (w u : V) :
    pushValue G (Function.update s w (s u)) =
      pushValue G s + (typeInd s u - typeInd s w) * (G.degree w : ℝ)⁻¹ := by
  cases hu : s u <;> cases hw : s w
  · have heq : Function.update s w false = s := by
      rw [← hw]
      exact Function.update_eq_self _ _
    rw [heq]
    simp only [typeInd, hu, hw, sub_self, zero_mul, add_zero]
  · rw [pushValue_loss G s hw]
    simp only [typeInd, hu, hw]
    rw [if_neg (by decide : ¬ false = true), if_true]
    ring
  · rw [pushValue_gain G s hw]
    simp only [typeInd, hu, hw]
    rw [if_true, if_neg (by decide : ¬ false = true)]
    ring
  · have heq : Function.update s w true = s := by
      rw [← hw]
      exact Function.update_eq_self _ _
    rw [heq]
    simp only [typeInd, hu, hw, sub_self, zero_mul, add_zero]

/-- Updating `u` to the type of `w` changes pull value by `(1_{s w} - 1_{s u}) * deg u`. -/
lemma pullValue_update (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) (u w : V) :
    pullValue G (Function.update s u (s w)) =
      pullValue G s + (typeInd s w - typeInd s u) * (G.degree u : ℝ) := by
  cases hw : s w <;> cases hu : s u
  · have heq : Function.update s u false = s := by
      rw [← hu]
      exact Function.update_eq_self _ _
    rw [heq]
    simp only [typeInd, hu, hw, sub_self, zero_mul, add_zero]
  · rw [pullValue_loss G s hu]
    simp only [typeInd, hu, hw]
    rw [if_neg (by decide : ¬ false = true), if_true]
    ring
  · rw [pullValue_gain G s hu]
    simp only [typeInd, hu, hw]
    rw [if_true, if_neg (by decide : ¬ false = true)]
    ring
  · have heq : Function.update s u true = s := by
      rw [← hu]
      exact Function.update_eq_self _ _
    rw [heq]
    simp only [typeInd, hu, hw, sub_self, zero_mul, add_zero]

omit [DecidableEq V] in
/-- A function on ordered pairs that changes sign under swapping the coordinates sums to zero. -/
lemma sum_swap_neg {f : V × V → ℝ} (h : ∀ u w, f (w, u) = - f (u, w)) :
    ∑ p : V × V, f p = 0 := by
  have hs : ∑ p, f (Equiv.prodComm V V p) = - ∑ p, f p := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    rintro ⟨u, w⟩ _
    exact h u w
  have hc : ∑ p, f (Equiv.prodComm V V p) = ∑ p, f p :=
    Equiv.sum_comp (Equiv.prodComm V V) f
  exact CharZero.eq_neg_self_iff.mp (hc.symm.trans hs)

omit [Fintype V] [DecidableEq V] in
lemma neutral_fitness (s : Config V) (u : V) : fitness 1 s u = 1 := by
  cases h : s u <;> simp [fitness, h]

omit [DecidableEq V] in
lemma neutral_totalFitness (s : Config V) : totalFitness 1 s = Fintype.card V := by
  unfold totalFitness
  simp_rw [neutral_fitness]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma pair_weight_neutral [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Config V) (p : V × V) :
    (pairDist G 1 one_pos s).weight p = (Fintype.card V : ℝ)⁻¹ * target G p.1 p.2 := by
  rw [pairDist_weight, neutral_fitness, neutral_totalFitness, div_eq_mul_inv, one_mul]

/-- Push increment of one pair, zero off edges and antisymmetric on edges. -/
lemma push_increment (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) (u w : V) :
    target G u w * ((typeInd s u - typeInd s w) * (G.degree w : ℝ)⁻¹) =
      if G.Adj u w then
        (typeInd s u - typeInd s w) * ((G.degree u : ℝ) * G.degree w)⁻¹
      else 0 := by
  by_cases hdeg : G.degree u = 0
  · have hnot : ¬ G.Adj u w := fun hadj => hadj.degree_pos_left.ne' hdeg
    rw [if_neg hnot, target, if_pos hdeg]
    by_cases hwu : w = u
    · subst hwu
      rw [sub_self, zero_mul, mul_zero]
    · rw [if_neg hwu, zero_mul]
  · by_cases hadj : G.Adj u w
    · rw [if_pos hadj, target, if_neg hdeg, if_pos hadj, mul_inv]
      ring
    · rw [if_neg hadj, target, if_neg hdeg, if_neg hadj, zero_mul]

/-- Pull increment of one pair: an edge contributes `±1`, independent of the degree. -/
lemma pull_increment (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) (u w : V) :
    target G u w * ((typeInd s w - typeInd s u) * (G.degree u : ℝ)) =
      if G.Adj u w then typeInd s w - typeInd s u else 0 := by
  by_cases hadj : G.Adj u w
  · have hdeg : (G.degree u : ℝ) ≠ 0 := by exact_mod_cast hadj.degree_pos_left.ne'
    rw [if_pos hadj, target, if_neg hadj.degree_pos_left.ne', if_pos hadj]
    calc
      (G.degree u : ℝ)⁻¹ * ((typeInd s w - typeInd s u) * (G.degree u : ℝ))
          = (typeInd s w - typeInd s u) *
              ((G.degree u : ℝ)⁻¹ * (G.degree u : ℝ)) := by ring
      _ = (typeInd s w - typeInd s u) * 1 := by rw [inv_mul_cancel₀ hdeg]
      _ = typeInd s w - typeInd s u := by ring
  · rw [if_neg hadj]
    by_cases hdeg : G.degree u = 0
    · simp [hdeg]
    · rw [target, if_neg hdeg, if_neg hadj, zero_mul]

/-- **Push invariant.** On every graph, the neutral Birth–death step preserves
`∑_{v mutant} 1/deg v` in expectation. -/
theorem push_value_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Config V) :
    (moranKernel G 1 one_pos).apply (pushValue G) s = pushValue G s := by
  rw [Kernel.apply, moranKernel, Distribution.map_expect, Distribution.expect]
  have hsplit : ∀ p : V × V,
      (pairDist G 1 one_pos s).weight p *
          pushValue G (Function.update s p.2 (s p.1)) =
        (pairDist G 1 one_pos s).weight p * pushValue G s +
          (pairDist G 1 one_pos s).weight p *
            ((typeInd s p.1 - typeInd s p.2) * (G.degree p.2 : ℝ)⁻¹) := by
    intro p
    rw [pushValue_update G s p.2 p.1, mul_add]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hbase : ∑ p : V × V, (pairDist G 1 one_pos s).weight p * pushValue G s =
      pushValue G s := by
    rw [← Finset.sum_mul, (pairDist G 1 one_pos s).sum_one, one_mul]
  have hrest : ∑ p : V × V, (pairDist G 1 one_pos s).weight p *
      ((typeInd s p.1 - typeInd s p.2) * (G.degree p.2 : ℝ)⁻¹) = 0 := by
    have hterm : ∀ p : V × V,
        (pairDist G 1 one_pos s).weight p *
            ((typeInd s p.1 - typeInd s p.2) * (G.degree p.2 : ℝ)⁻¹) =
          (Fintype.card V : ℝ)⁻¹ * (if G.Adj p.1 p.2 then
            (typeInd s p.1 - typeInd s p.2) *
              ((G.degree p.1 : ℝ) * G.degree p.2)⁻¹ else 0) := by
      intro p
      rw [pair_weight_neutral G s p, mul_assoc, push_increment G s p.1 p.2]
    simp_rw [hterm, ← Finset.mul_sum]
    refine mul_eq_zero_of_right _ ?_
    refine sum_swap_neg ?_
    intro u w
    by_cases hadj : G.Adj u w
    · rw [if_pos hadj.symm, if_pos hadj]
      rw [mul_comm ((G.degree w : ℝ)) (G.degree u : ℝ)]
      ring
    · rw [if_neg (fun h => hadj h.symm), if_neg hadj]
      exact neg_zero.symm
  rw [hbase, hrest, add_zero]

/-- **Pull invariant.** On every graph, the death–Birth step preserves `∑_{v mutant} deg v` in
expectation. -/
theorem pull_value_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Config V) :
    (pullKernel G).apply (pullValue G) s = pullValue G s := by
  rw [Kernel.apply, pullKernel, Distribution.map_expect, Distribution.expect]
  -- `(pullDist G).weight` is `pullWeight` by definition; `simp` will not unfold the projection.
  simp_rw [show ∀ p, (pullDist G).weight p = pullWeight G p from fun _ => rfl]
  have hsplit : ∀ p : V × V,
      pullWeight G p * pullValue G (Function.update s p.1 (s p.2)) =
        pullWeight G p * pullValue G s +
          pullWeight G p * ((typeInd s p.2 - typeInd s p.1) * (G.degree p.1 : ℝ)) := by
    intro p
    rw [pullValue_update G s p.1 p.2, mul_add]
  rw [Finset.sum_congr rfl (fun p _ => hsplit p), Finset.sum_add_distrib]
  have hbase : ∑ p : V × V, pullWeight G p * pullValue G s = pullValue G s := by
    rw [← Finset.sum_mul, pull_weight_sum_one, one_mul]
  have hrest : ∑ p : V × V,
      pullWeight G p * ((typeInd s p.2 - typeInd s p.1) * (G.degree p.1 : ℝ)) = 0 := by
    have hterm : ∀ p : V × V,
        pullWeight G p * ((typeInd s p.2 - typeInd s p.1) * (G.degree p.1 : ℝ)) =
          (Fintype.card V : ℝ)⁻¹ *
            (if G.Adj p.1 p.2 then typeInd s p.2 - typeInd s p.1 else 0) := by
      intro p
      rw [pullWeight, mul_assoc, pull_increment G s p.1 p.2]
    simp_rw [hterm, ← Finset.mul_sum]
    refine mul_eq_zero_of_right _ ?_
    refine sum_swap_neg ?_
    intro u w
    by_cases hadj : G.Adj u w
    · rw [if_pos hadj.symm, if_pos hadj]
      ring
    · rw [if_neg (fun h => hadj h.symm), if_neg hadj]
      exact neg_zero.symm
  rw [hbase, hrest, add_zero]

lemma pull_constant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : Bool)
    (f : Config V → ℝ) :
    (pullKernel G).apply f (fun _ => c) = f (fun _ => c) := by
  rw [Kernel.apply, pullKernel, Distribution.map_expect]
  have hupd : ∀ p : V × V,
      Function.update (fun _ : V => c) p.1 ((fun _ => c) p.2) = fun _ => c :=
    fun p => Function.update_eq_self p.1 (fun _ => c)
  simp_rw [hupd]
  exact (pullDist G).expect_const _

lemma pull_unfixed_step [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) :
    (pullKernel G).apply unfixed s ≤ unfixed s := by
  by_cases hs : ∃ c, s = fun _ => c
  · obtain ⟨c, rfl⟩ := hs
    rw [pull_constant G c unfixed]
  · rw [unfixed_of_mixed s hs, Kernel.apply]
    calc
      (pullKernel G s).expect unfixed ≤ (pullKernel G s).expect (fun _ => 1) :=
        (pullKernel G s).expect_mono unfixed_le_one
      _ = 1 := (pullKernel G s).expect_const 1

lemma pull_move_weight_pos [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Config V) {u w : V} (hadj : G.Adj u w) :
    0 < (pullKernel G s).weight (Function.update s u (s w)) := by
  unfold pullKernel
  refine map_weight_pos (pullDist G) (fun p => Function.update s p.1 (s p.2)) (u, w) ?_
  have hweight : (pullDist G).weight (u, w) = pullWeight G (u, w) := rfl
  rw [hweight]
  unfold pullWeight
  rw [target, if_neg hadj.degree_pos_left.ne', if_pos hadj]
  exact mul_pos (inv_pos.mpr (by exact_mod_cast Fintype.card_pos))
    (inv_pos.mpr (by exact_mod_cast hadj.degree_pos_left))

lemma pull_unfixed_access [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (s : Config V) :
    ∃ n, (pullKernel G).iterate n unfixed s < 1 := by
  classical
  suffices ∀ k, ∀ s : Config V, Fintype.card V - mutants s = k →
      ∃ n, (pullKernel G).iterate n unfixed s < 1 from this _ s rfl
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
      exact expect_lt_one (pullKernel G s) ((pullKernel G).iterate n unfixed)
        (fun a => by
          have hle := (pullKernel G).iterate_mono n unfixed_le_one a
          simp [Kernel.iterate_const] at hle
          exact hle)
        t (by
          have hEq : Function.update s d.snd (s d.fst) = t := by
            unfold t
            rw [hdu]
          rw [← hEq]
          exact pull_move_weight_pos G s d.adj.symm)
        hn

lemma pull_allMutant_step [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) :
    allMutant s ≤ (pullKernel G).apply allMutant s := by
  by_cases hs : s = fun _ => true
  · subst hs
    rw [pull_constant G true allMutant]
  · rw [allMutant, if_neg hs, Kernel.apply]
    exact (pullKernel G s).expect_nonneg allMutant_nonneg

/-- **Absorption under pull.** On a connected graph, the probability that neither type has fixed
tends to zero. -/
theorem pull_unfixed_tendsto [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (s : Config V) :
    Tendsto (fun t => (pullKernel G).iterate t unfixed s) atTop (𝓝 0) :=
  (pullKernel G).finite_absorption unfixed unfixed_binary (pull_unfixed_step G)
    (pull_unfixed_access G hc) s

omit [DecidableEq V] in
lemma pushValue_false (G : SimpleGraph V) [DecidableRel G.Adj] :
    pushValue G (fun _ => false) = 0 := by
  unfold pushValue
  have hfilter : univ.filter (fun v : V => (fun _ => false) v = true) = ∅ := by
    ext v
    simp
  rw [hfilter, Finset.sum_empty]

omit [DecidableEq V] in
lemma pushValue_total_pos [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) : 0 < pushValue G (fun _ => true) := by
  unfold pushValue
  have hfilter : univ.filter (fun v => (fun _ : V => true) v = true) = univ := by
    ext v
    simp
  rw [hfilter]
  refine Finset.sum_pos ?_ univ_nonempty
  intro v _
  exact inv_pos.mpr (by exact_mod_cast hc.preconnected.degree_pos_of_nontrivial v)

omit [DecidableEq V] in
lemma pullValue_false (G : SimpleGraph V) [DecidableRel G.Adj] :
    pullValue G (fun _ => false) = 0 := by
  unfold pullValue
  have hfilter : univ.filter (fun v : V => (fun _ => false) v = true) = ∅ := by
    ext v
    simp
  rw [hfilter, Finset.sum_empty]

omit [DecidableEq V] in
lemma pullValue_total_pos [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) : 0 < pullValue G (fun _ => true) := by
  unfold pullValue
  have hfilter : univ.filter (fun v => (fun _ : V => true) v = true) = univ := by
    ext v
    simp
  rw [hfilter]
  refine Finset.sum_pos ?_ univ_nonempty
  intro v _
  exact_mod_cast hc.preconnected.degree_pos_of_nontrivial v

lemma pushRatio_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) :
    (moranKernel G 1 one_pos).apply
        (fun t => pushValue G t / pushValue G (fun _ => true)) s =
      pushValue G s / pushValue G (fun _ => true) := by
  rw [Kernel.apply]
  have hcomm : ∀ t : Config V,
      pushValue G t / pushValue G (fun _ => true) =
        (pushValue G (fun _ => true))⁻¹ * pushValue G t := by
    intro t
    rw [div_eq_mul_inv, mul_comm]
  simp_rw [hcomm, Distribution.expect_mul]
  have hexp : (moranKernel G 1 one_pos s).expect (pushValue G) = pushValue G s := by
    rw [← Kernel.apply]
    exact push_value_invariant G s
  rw [hexp]

lemma pullRatio_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Config V) :
    (pullKernel G).apply (fun t => pullValue G t / pullValue G (fun _ => true)) s =
      pullValue G s / pullValue G (fun _ => true) := by
  rw [Kernel.apply]
  have hcomm : ∀ t : Config V,
      pullValue G t / pullValue G (fun _ => true) =
        (pullValue G (fun _ => true))⁻¹ * pullValue G t := by
    intro t
    rw [div_eq_mul_inv, mul_comm]
  simp_rw [hcomm, Distribution.expect_mul]
  have hexp : (pullKernel G s).expect (pullValue G) = pullValue G s := by
    rw [← Kernel.apply]
    exact pull_value_invariant G s
  rw [hexp]

/-- **Push fixation.** On a connected graph with at least two vertices, neutral Birth–death
fixes with probability `∑_{v ∈ S} 1/deg v / ∑_v 1/deg v`. -/
theorem push_fixation [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (s : Config V) :
    fixation (moranKernel G 1 one_pos) s = pushValue G s / pushValue G (fun _ => true) := by
  exact fixation_eq_of_invariant (moranKernel G 1 one_pos)
    (fun t => pushValue G t / pushValue G (fun _ => true))
    (funext fun t => pushRatio_invariant G t) (div_self (pushValue_total_pos G hc).ne')
    (by rw [pushValue_false, zero_div]) (allMutant_step G one_pos) s
    (moran_unfixed_tendsto G hc one_pos s)

/-- **Pull fixation.** On a connected graph with at least two vertices, death–Birth fixes with
probability `∑_{v ∈ S} deg v / ∑_v deg v`. -/
theorem pull_fixation [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (s : Config V) :
    fixation (pullKernel G) s = pullValue G s / pullValue G (fun _ => true) := by
  exact fixation_eq_of_invariant (pullKernel G)
    (fun t => pullValue G t / pullValue G (fun _ => true))
    (funext fun t => pullRatio_invariant G t) (div_self (pullValue_total_pos G hc).ne')
    (by rw [pullValue_false, zero_div]) (pull_allMutant_step G) s (pull_unfixed_tendsto G hc s)

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

end Moran
