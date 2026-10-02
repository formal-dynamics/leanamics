import Mathlib

/-! # Averaging dynamics on graphs

In every round each node replaces its value by the average of its neighbours' values (the
expectation of the value at one step of the random walk). The degree-weighted sum of the values
is conserved, values stay within the initial range, and on a connected graph containing an odd
closed walk (i.e. a connected non-bipartite graph) every node's value converges to the
degree-weighted average `∑ deg v · x v / ∑ deg v` of the initial values. On a connected bipartite
graph with at least two nodes this fails: the values `±1` of a proper 2-colouring alternate forever.
-/

namespace Averaging
open Finset Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One round of averaging: every node takes the average of its neighbours' values. -/
noncomputable def avgStep (x : V → ℝ) : V → ℝ :=
  fun v => (∑ u ∈ G.neighborFinset v, x u) / G.degree v

/-- `t` rounds of averaging. -/
noncomputable def avgIter : ℕ → (V → ℝ) → V → ℝ
  | 0, x => x
  | t + 1, x => avgStep G (avgIter t x)

/-- The degree-weighted average of the values (their mean under the stationary distribution of
the random walk). -/
noncomputable def degAvg (x : V → ℝ) : ℝ :=
  (∑ v, (G.degree v : ℝ) * x v) / ∑ v, (G.degree v : ℝ)

open SimpleGraph

/-! ### Conservation and the maximum principle -/

omit [DecidableEq V] in
lemma degree_mul_avgStep (x : V → ℝ) (v : V) :
    (G.degree v : ℝ) * avgStep G x v = ∑ u ∈ G.neighborFinset v, x u := by
  rw [avgStep]
  rcases eq_or_ne (G.degree v) 0 with hv | hv
  · have hempty : G.neighborFinset v = ∅ := by
      apply card_eq_zero.mp
      rw [card_neighborFinset_eq_degree, hv]
    simp [hv, hempty]
  · exact mul_div_cancel₀ _ (by exact_mod_cast hv)

omit [DecidableEq V] in
/-- Swap a sum over neighbours of `v` with a sum over all vertices. -/
lemma sum_sum_neighbor_comm (v : V) (f : V → V → ℝ) :
    ∑ u, ∑ w ∈ G.neighborFinset v, f w u = ∑ w ∈ G.neighborFinset v, ∑ u, f w u := by
  exact Finset.sum_comm' (t' := G.neighborFinset v) (s' := fun _ => univ) (h := fun _ _ => Iff.rfl)

omit [DecidableEq V] in
lemma sum_sum_neighbor (x : V → ℝ) :
    ∑ v, ∑ u ∈ G.neighborFinset v, x u = ∑ u, (G.degree u : ℝ) * x u := by
  rw [Finset.sum_comm' (h := fun v u =>
    (by simp [mem_neighborFinset, adj_comm] :
      v ∈ univ ∧ u ∈ G.neighborFinset v ↔ v ∈ G.neighborFinset u ∧ u ∈ univ))]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul]

omit [DecidableEq V] in
/-- The degree-weighted sum is conserved by a round. -/
theorem degree_weighted_sum_step (x : V → ℝ) :
    ∑ v, (G.degree v : ℝ) * avgStep G x v = ∑ v, (G.degree v : ℝ) * x v := by
  simp_rw [degree_mul_avgStep]
  exact sum_sum_neighbor G x

omit [DecidableEq V] in
/-- Maximum principle: without isolated nodes, a round never exceeds an upper bound. -/
theorem avgStep_le (hdeg : ∀ v, 0 < G.degree v) {x : V → ℝ} {M : ℝ} (hM : ∀ v, x v ≤ M) (v : V) :
    avgStep G x v ≤ M := by
  rw [avgStep, div_le_iff₀ (by exact_mod_cast hdeg v)]
  refine (sum_le_sum fun u _ => hM u).trans ?_
  rw [sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul, mul_comm]

omit [DecidableEq V] in
/-- Minimum principle: without isolated nodes, a round never goes below a lower bound. -/
theorem le_avgStep (hdeg : ∀ v, 0 < G.degree v) {x : V → ℝ} {m : ℝ} (hm : ∀ v, m ≤ x v) (v : V) :
    m ≤ avgStep G x v := by
  rw [avgStep, le_div_iff₀ (by exact_mod_cast hdeg v)]
  refine le_trans ?_ (sum_le_sum fun u _ => hm u)
  rw [sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul, mul_comm]

/-! ### Transition weights of the random walk -/

lemma sup'_irrel {β α : Type*} [SemilatticeSup α] {s : Finset β} (H₁ H₂ : s.Nonempty)
    (f : β → α) : s.sup' H₁ f = s.sup' H₂ f := by
  rw [← WithBot.coe_inj]

lemma inf'_irrel {β α : Type*} [SemilatticeInf α] {s : Finset β} (H₁ H₂ : s.Nonempty)
    (f : β → α) : s.inf' H₁ f = s.inf' H₂ f := by
  rw [← WithTop.coe_inj]

omit [DecidableEq V] in
lemma degree_weighted_sum_iter (t : ℕ) (x : V → ℝ) :
    ∑ v, (G.degree v : ℝ) * avgIter G t x v = ∑ v, (G.degree v : ℝ) * x v := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show avgIter G (t + 1) x = avgStep G (avgIter G t x) from rfl, degree_weighted_sum_step,
      ih]

omit [DecidableEq V] in
lemma avgIter_add (s t : ℕ) (x : V → ℝ) :
    avgIter G (t + s) x = avgIter G s (avgIter G t x) := by
  induction s with
  | zero => rw [Nat.add_zero]; rfl
  | succ s ih =>
    rw [show avgIter G (t + (s + 1)) x = avgStep G (avgIter G (t + s) x) from rfl, ih]
    rfl

/-- Probability of going from `v` to `u` in exactly `t` steps of the random walk. -/
noncomputable def transW : ℕ → V → V → ℝ
  | 0, v, u => if v = u then 1 else 0
  | t + 1, v, u => (∑ w ∈ G.neighborFinset v, transW t w u) / (G.degree v : ℝ)

lemma transW_nonneg (t : ℕ) (v u : V) : 0 ≤ transW G t v u := by
  induction t generalizing v with
  | zero =>
    simp only [transW]
    split_ifs <;> norm_num
  | succ t ih =>
    simp only [transW]
    exact div_nonneg (sum_nonneg fun w _ => ih w) (by exact_mod_cast Nat.zero_le _)

lemma transW_sum (hdeg : ∀ v, 0 < G.degree v) (t : ℕ) (v : V) :
    ∑ u, transW G t v u = 1 := by
  induction t generalizing v with
  | zero => simp only [transW, Finset.sum_ite_eq, mem_univ, ite_true]
  | succ t ih =>
    simp only [transW]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, sum_sum_neighbor_comm]
    simp_rw [ih]
    rw [Finset.sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one,
      mul_inv_cancel₀ (by exact_mod_cast (hdeg v).ne')]

lemma avgIter_eq_sum_transW (t : ℕ) (x : V → ℝ) (v : V) :
    avgIter G t x v = ∑ u, transW G t v u * x u := by
  induction t generalizing v with
  | zero => simp only [avgIter, transW, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ,
      ite_true]
  | succ t ih =>
    rw [show avgIter G (t + 1) x v = avgStep G (avgIter G t x) v from rfl, avgStep]
    simp only [transW]
    simp_rw [ih]
    calc
      (∑ w ∈ G.neighborFinset v, ∑ u, transW G t w u * x u) / (G.degree v : ℝ)
          = (∑ u, ∑ w ∈ G.neighborFinset v, transW G t w u * x u) / (G.degree v : ℝ) := by
            rw [← sum_sum_neighbor_comm]
        _ = (∑ u, (∑ w ∈ G.neighborFinset v, transW G t w u) * x u) / (G.degree v : ℝ) := by
            simp_rw [← Finset.sum_mul]
        _ = ∑ u, ((∑ w ∈ G.neighborFinset v, transW G t w u) / (G.degree v : ℝ)) * x u := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul]
            refine sum_congr rfl fun _ _ => ?_
            ring

lemma transW_pos_of_walk (hdeg : ∀ v, 0 < G.degree v) {t : ℕ} {v u : V} (p : G.Walk v u)
    (hp : p.length = t) : 0 < transW G t v u := by
  induction t generalizing v u p with
  | zero =>
    have hv : v = u := Walk.eq_of_length_eq_zero hp
    simp [transW, hv, zero_lt_one]
  | succ t ih =>
    have hlt : 0 < p.length := by omega
    obtain ⟨w, hadj, q, rfl⟩ := (Walk.not_nil_iff (p := p)).mp (Walk.not_nil_iff_lt_length.mpr hlt)
    have hq : q.length = t := by
      rw [Walk.length_cons] at hp
      omega
    simp only [transW]
    refine div_pos ?_ (by exact_mod_cast hdeg v)
    refine sum_pos' (fun z _ => transW_nonneg G t z u) ?_
    exact ⟨w, (G.mem_neighborFinset v w).mpr hadj, ih q hq⟩

/-! ### Walks of one common length -/

omit [DecidableEq V] in
lemma degree_pos_of_connected_odd (hc : G.Connected)
    (hodd : ∃ (a : V) (p : G.Walk a a), Odd p.length) (v : V) : 0 < G.degree v := by
  obtain ⟨a, p, hp⟩ := hodd
  have hlen : 0 < p.length := by
    obtain ⟨k, hk⟩ := hp
    omega
  obtain ⟨w, hadj, _, rfl⟩ :=
    (Walk.not_nil_iff (p := p)).mp (Walk.not_nil_iff_lt_length.mpr hlen)
  haveI : Nontrivial V := ⟨⟨a, w, hadj.ne⟩⟩
  exact hc.preconnected.degree_pos_of_nontrivial v

/-- `k` trips back and forth along an edge, a closed walk of length `2k`. -/
def roundTrip {u w : V} (h : G.Adj u w) : ℕ → G.Walk u u
  | 0 => Walk.nil
  | k + 1 => (Walk.cons h (Walk.cons h.symm Walk.nil)).append (roundTrip h k)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma roundTrip_length {u w : V} (h : G.Adj u w) (k : ℕ) :
    (roundTrip G h k).length = 2 * k := by
  induction k with
  | zero =>
    rw [roundTrip]
    rfl
  | succ k ih =>
    rw [roundTrip, Walk.length_append, Walk.length_cons, Walk.length_cons, Walk.length_nil, ih]
    omega

omit [DecidableEq V] in
lemma exists_walk_add_even {v u : V} (p : G.Walk v u) (hdeg : 0 < G.degree u) (k : ℕ) :
    ∃ q : G.Walk v u, q.length = p.length + 2 * k := by
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj u).mp hdeg
  refine ⟨p.append (roundTrip G hw k), ?_⟩
  rw [Walk.length_append, roundTrip_length G]

omit [DecidableEq V] in
lemma exists_uniform_walk_length (hc : G.Connected)
    (hodd : ∃ (a : V) (p : G.Walk a a), Odd p.length) :
    ∃ L, 0 < L ∧ ∀ v u, ∃ p : G.Walk v u, p.length = L := by
  obtain ⟨a, cyc, hodd_cyc⟩ := hodd
  have hcyc : 0 < cyc.length := by
    obtain ⟨k, hk⟩ := hodd_cyc
    omega
  refine ⟨2 * (Fintype.card V - 1) + cyc.length, by omega, fun v u => ?_⟩
  obtain ⟨pva, hpva, hlen_pva⟩ := hc.exists_path_of_dist v a
  obtain ⟨pau, hpau, hlen_pau⟩ := hc.exists_path_of_dist a u
  have hdv : G.dist v a ≤ Fintype.card V - 1 := by
    have hlt := hpva.length_lt
    rw [hlen_pva] at hlt
    omega
  have hdu : G.dist a u ≤ Fintype.card V - 1 := by
    have hlt := hpau.length_lt
    rw [hlen_pau] at hlt
    omega
  let base0 : G.Walk v u := pva.append pau
  let base1 : G.Walk v u := pva.append (cyc.append pau)
  have hbase0 : base0.length = G.dist v a + G.dist a u := by
    unfold base0
    rw [Walk.length_append, hlen_pva, hlen_pau]
  have hbase1 : base1.length = G.dist v a + G.dist a u + cyc.length := by
    unfold base1
    rw [Walk.length_append, Walk.length_append, hlen_pva, hlen_pau]
    omega
  have h0le : base0.length ≤ 2 * (Fintype.card V - 1) + cyc.length := by
    rw [hbase0]
    omega
  have h1le : base1.length ≤ 2 * (Fintype.card V - 1) + cyc.length := by
    rw [hbase1]
    omega
  have hdegu : 0 < G.degree u := degree_pos_of_connected_odd G hc ⟨a, cyc, hodd_cyc⟩ u
  let L := 2 * (Fintype.card V - 1) + cyc.length
  by_cases hEven : Even (L - base1.length)
  · obtain ⟨q, hq⟩ := exists_walk_add_even G base1 hdegu ((L - base1.length) / 2)
    refine ⟨q, ?_⟩
    rw [hq, Nat.two_mul_div_two_of_even hEven]
    exact Nat.add_sub_of_le h1le
  · have hOdd1 : Odd (L - base1.length) := Nat.not_even_iff_odd.mp hEven
    have hgap : L - base0.length = (L - base1.length) + cyc.length := by
      have h01 : base0.length ≤ base1.length := by
        rw [hbase0, hbase1]
        omega
      omega
    have hEven0 : Even (L - base0.length) := by
      rw [hgap]
      exact hOdd1.add_odd hodd_cyc
    obtain ⟨q, hq⟩ := exists_walk_add_even G base0 hdegu ((L - base0.length) / 2)
    refine ⟨q, ?_⟩
    rw [hq, Nat.two_mul_div_two_of_even hEven0]
    exact Nat.add_sub_of_le h0le

/-! ### Range of a configuration -/

omit [DecidableEq V] in
noncomputable def fMax [Nonempty V] (f : V → ℝ) : ℝ := univ.sup' univ_nonempty f

omit [DecidableEq V] in
noncomputable def fMin [Nonempty V] (f : V → ℝ) : ℝ := univ.inf' univ_nonempty f

omit [DecidableEq V] in
lemma le_fMax [Nonempty V] (f : V → ℝ) (v : V) : f v ≤ fMax f := by
  rw [fMax]
  have h := Finset.le_sup' f (mem_univ v)
  rwa [sup'_irrel ⟨v, mem_univ v⟩ univ_nonempty f] at h

omit [DecidableEq V] in
lemma fMin_le [Nonempty V] (f : V → ℝ) (v : V) : fMin f ≤ f v := by
  rw [fMin]
  have h := Finset.inf'_le f (mem_univ v)
  rwa [inf'_irrel ⟨v, mem_univ v⟩ univ_nonempty f] at h

omit [DecidableEq V] in
lemma exists_eq_fMax [Nonempty V] (f : V → ℝ) : ∃ v, fMax f = f v := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' univ_nonempty f
  exact ⟨v, by simpa [fMax] using hv⟩

omit [DecidableEq V] in
lemma exists_eq_fMin [Nonempty V] (f : V → ℝ) : ∃ v, fMin f = f v := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_inf' univ_nonempty f
  exact ⟨v, by simpa [fMin] using hv⟩

omit [DecidableEq V] in
lemma fMin_le_fMax [Nonempty V] (f : V → ℝ) : fMin f ≤ fMax f := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact (fMin_le f v).trans (le_fMax f v)

omit [DecidableEq V] in
lemma fMax_avgStep_le (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (x : V → ℝ) :
    fMax (avgStep G x) ≤ fMax x := by
  rw [fMax, sup'_le_iff]
  intro v _
  exact avgStep_le G hdeg (fun w => le_fMax x w) v

omit [DecidableEq V] in
lemma le_fMin_avgStep (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (x : V → ℝ) :
    fMin x ≤ fMin (avgStep G x) := by
  rw [show fMin (avgStep G x) = univ.inf' univ_nonempty (avgStep G x) from rfl, le_inf'_iff]
  intro v _
  exact le_avgStep G hdeg (fun w => fMin_le x w) v

omit [DecidableEq V] in
lemma fMax_antitone (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (x : V → ℝ) :
    Antitone fun t => fMax (avgIter G t x) := by
  refine antitone_nat_of_succ_le fun t => ?_
  rw [show avgIter G (t + 1) x = avgStep G (avgIter G t x) from rfl]
  exact fMax_avgStep_le G hdeg _

omit [DecidableEq V] in
lemma fMin_monotone (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (x : V → ℝ) :
    Monotone fun t => fMin (avgIter G t x) := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [show avgIter G (t + 1) x = avgStep G (avgIter G t x) from rfl]
  exact le_fMin_avgStep G hdeg _

noncomputable def transWMin [Nonempty V] (t : ℕ) : ℝ :=
  (univ : Finset (V × V)).inf' univ_nonempty fun p => transW G t p.1 p.2

lemma transWMin_le [Nonempty V] (t : ℕ) (v u : V) : transWMin G t ≤ transW G t v u := by
  rw [transWMin]
  have h := Finset.inf'_le (fun p => transW G t p.1 p.2) (mem_univ (v, u))
  rwa [inf'_irrel ⟨(v, u), mem_univ _⟩ univ_nonempty _] at h

lemma transWMin_pos [Nonempty V] {t : ℕ} (h : ∀ v u, 0 < transW G t v u) : 0 < transWMin G t := by
  rw [transWMin, lt_inf'_iff]
  intro p _
  exact h p.1 p.2

/-- Doeblin: a stochastic kernel bounded below by `δ` contracts the range by `1 - |V| δ`. -/
lemma range_avgIter_le (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (L : ℕ) (δ : ℝ)
    (hδ : ∀ v u, δ ≤ transW G L v u) (y : V → ℝ) :
    fMax (avgIter G L y) - fMin (avgIter G L y) ≤
      (1 - (Fintype.card V : ℝ) * δ) * (fMax y - fMin y) := by
  obtain ⟨vMax, hvMax⟩ := exists_eq_fMax (avgIter G L y)
  obtain ⟨vMin, hvMin⟩ := exists_eq_fMin (avgIter G L y)
  rw [hvMax, hvMin]
  simp_rw [avgIter_eq_sum_transW G]
  have hsplit (v : V) :
      ∑ u, transW G L v u * y u =
        ∑ u, (transW G L v u - δ) * y u + δ * ∑ u, y u := by
    calc
      ∑ u, transW G L v u * y u
          = ∑ u, ((transW G L v u - δ) * y u + δ * y u) := by
            refine sum_congr rfl fun _ _ => ?_
            ring
        _ = ∑ u, (transW G L v u - δ) * y u + ∑ u, δ * y u := Finset.sum_add_distrib
        _ = ∑ u, (transW G L v u - δ) * y u + δ * ∑ u, y u := by rw [← Finset.mul_sum]
  rw [hsplit vMax, hsplit vMin]
  have hcancel :
      (∑ u, (transW G L vMax u - δ) * y u + δ * ∑ u, y u) -
          (∑ u, (transW G L vMin u - δ) * y u + δ * ∑ u, y u) =
        ∑ u, (transW G L vMax u - δ) * y u - ∑ u, (transW G L vMin u - δ) * y u := by
    ring
  rw [hcancel]
  have hcoeff (v : V) :
      ∑ u, (transW G L v u - δ) = 1 - (Fintype.card V : ℝ) * δ := by
    rw [Finset.sum_sub_distrib, transW_sum G hdeg L v, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hnn (v u : V) : 0 ≤ transW G L v u - δ := sub_nonneg.mpr (hδ v u)
  have hup (v : V) :
      ∑ u, (transW G L v u - δ) * y u ≤ (1 - (Fintype.card V : ℝ) * δ) * fMax y := by
    calc
      ∑ u, (transW G L v u - δ) * y u ≤ ∑ u, (transW G L v u - δ) * fMax y := by
        refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (le_fMax y u) (hnn v u)
      _ = (∑ u, (transW G L v u - δ)) * fMax y := by rw [← Finset.sum_mul]
      _ = (1 - (Fintype.card V : ℝ) * δ) * fMax y := by rw [hcoeff v]
  have hlo (v : V) :
      (1 - (Fintype.card V : ℝ) * δ) * fMin y ≤ ∑ u, (transW G L v u - δ) * y u := by
    calc
      (1 - (Fintype.card V : ℝ) * δ) * fMin y = (∑ u, (transW G L v u - δ)) * fMin y := by
        rw [hcoeff v]
      _ = ∑ u, (transW G L v u - δ) * fMin y := by rw [Finset.sum_mul]
      _ ≤ ∑ u, (transW G L v u - δ) * y u := by
        refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (fMin_le y u) (hnn v u)
  refine (sub_le_sub (hup vMax) (hlo vMin)).trans (le_of_eq ?_)
  ring

lemma gap_iter (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (L : ℕ) (δ : ℝ)
    (hδ : ∀ v u, δ ≤ transW G L v u) (hρ : 0 ≤ 1 - (Fintype.card V : ℝ) * δ) (x : V → ℝ)
    (k : ℕ) :
    fMax (avgIter G (k * L) x) - fMin (avgIter G (k * L) x) ≤
      (1 - (Fintype.card V : ℝ) * δ) ^ k * (fMax x - fMin x) := by
  induction k with
  | zero =>
    simp only [Nat.zero_mul, avgIter, pow_zero, one_mul]
    exact le_rfl
  | succ k ih =>
    have hrec := range_avgIter_le G hdeg L δ hδ (avgIter G (k * L) x)
    rw [← avgIter_add, ← Nat.succ_mul] at hrec
    refine (hrec.trans (mul_le_mul_of_nonneg_left ih hρ)).trans (le_of_eq ?_)
    ring

/-- Convergence: on a connected graph with an odd closed walk, every value converges to the
degree-weighted average of the initial values. -/
theorem tendsto_degAvg (hc : G.Connected) (hodd : ∃ (u : V) (p : G.Walk u u), Odd p.length)
    (x : V → ℝ) (v : V) :
    Tendsto (fun t => avgIter G t x v) atTop (𝓝 (degAvg G x)) := by
  haveI : Nonempty V := hc.nonempty
  have hdeg : ∀ w, 0 < G.degree w := fun w => degree_pos_of_connected_odd G hc hodd w
  obtain ⟨L, hLpos, hwalk⟩ := exists_uniform_walk_length G hc hodd
  have hposW : ∀ a b, 0 < transW G L a b := by
    intro a b
    obtain ⟨p, hp⟩ := hwalk a b
    exact transW_pos_of_walk G hdeg p hp
  let δ : ℝ := transWMin G L
  have hδle : ∀ a b, δ ≤ transW G L a b := fun a b => transWMin_le G L a b
  have hδpos : 0 < δ := transWMin_pos G hposW
  let ρ : ℝ := 1 - (Fintype.card V : ℝ) * δ
  have hρ0 : 0 ≤ ρ := by
    have hle : (Fintype.card V : ℝ) * δ ≤ 1 := by
      obtain ⟨w⟩ := hc.nonempty
      calc
        (Fintype.card V : ℝ) * δ = ∑ _ : V, δ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ u, transW G L w u := sum_le_sum fun u _ => hδle w u
        _ = 1 := transW_sum G hdeg L w
    exact sub_nonneg.mpr hle
  have hρlt : ρ < 1 := sub_lt_self _ (mul_pos (by exact_mod_cast Fintype.card_pos) hδpos)
  have hgap_le (k : ℕ) :
      fMax (avgIter G (k * L) x) - fMin (avgIter G (k * L) x) ≤
        ρ ^ k * (fMax x - fMin x) := by
    simpa [ρ] using gap_iter G hdeg L δ hδle hρ0 x k
  have hManti := fMax_antitone G hdeg x
  have hmmono := fMin_monotone G hdeg x
  have hMbdd : BddBelow (Set.range fun t => fMax (avgIter G t x)) := by
    refine ⟨fMin x, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (hmmono (Nat.zero_le t)).trans (fMin_le_fMax _)
  have hmbdd : BddAbove (Set.range fun t => fMin (avgIter G t x)) := by
    refine ⟨fMax x, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (fMin_le_fMax _).trans (hManti (Nat.zero_le t))
  have hMlim : Tendsto (fun t => fMax (avgIter G t x)) atTop
      (𝓝 (⨅ t, fMax (avgIter G t x))) :=
    tendsto_atTop_ciInf hManti hMbdd
  have hmlim : Tendsto (fun t => fMin (avgIter G t x)) atTop
      (𝓝 (⨆ t, fMin (avgIter G t x))) :=
    tendsto_atTop_ciSup hmmono hmbdd
  have hsub : Tendsto (fun k : ℕ => k * L) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone (fun _ _ hab => Nat.mul_le_mul_right _ hab) ?_
    intro b
    refine ⟨b, ?_⟩
    calc
      b = b * 1 := (Nat.mul_one b).symm
      _ ≤ b * L := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hLpos)
  have hgap0 : Tendsto (fun k => fMax (avgIter G (k * L) x) - fMin (avgIter G (k * L) x))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => sub_nonneg.mpr (fMin_le_fMax _)) hgap_le
    simpa using Filter.Tendsto.mul_const (fMax x - fMin x)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρlt)
  have hgapdiff : Tendsto (fun k => fMax (avgIter G (k * L) x) - fMin (avgIter G (k * L) x))
      atTop (𝓝 ((⨅ t, fMax (avgIter G t x)) - ⨆ t, fMin (avgIter G t x))) :=
    (hMlim.comp hsub).sub (hmlim.comp hsub)
  have heq : (⨅ t, fMax (avgIter G t x)) = ⨆ t, fMin (avgIter G t x) :=
    sub_eq_zero.mp (tendsto_nhds_unique hgapdiff hgap0)
  let c : ℝ := ⨆ t, fMin (avgIter G t x)
  have hcoord (w : V) : Tendsto (fun t => avgIter G t x w) atTop (𝓝 c) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hmlim ?_
      (fun t => fMin_le (avgIter G t x) w) (fun t => le_fMax (avgIter G t x) w)
    rw [show c = ⨆ t, fMin (avgIter G t x) from rfl, ← heq]
    exact hMlim
  have hsumt : Tendsto (fun t => ∑ w, (G.degree w : ℝ) * avgIter G t x w) atTop
      (𝓝 (∑ w, (G.degree w : ℝ) * c)) :=
    tendsto_finsetSum (univ : Finset V) fun w _ =>
      Filter.Tendsto.const_mul ((G.degree w : ℝ)) (hcoord w)
  have hsum0 : Tendsto (fun t => ∑ w, (G.degree w : ℝ) * avgIter G t x w) atTop
      (𝓝 (∑ w, (G.degree w : ℝ) * x w)) := by
    simp_rw [degree_weighted_sum_iter G]
    exact tendsto_const_nhds
  have hsum_eq : ∑ w, (G.degree w : ℝ) * c = ∑ w, (G.degree w : ℝ) * x w :=
    tendsto_nhds_unique hsumt hsum0
  have hpos_sum : 0 < ∑ w, (G.degree w : ℝ) := by
    refine sum_pos' (fun w _ => by exact_mod_cast Nat.zero_le (G.degree w)) ?_
    obtain ⟨w⟩ := hc.nonempty
    exact ⟨w, mem_univ _, by exact_mod_cast hdeg w⟩
  have hcavg : c = degAvg G x := by
    rw [degAvg, eq_div_iff (ne_of_gt hpos_sum), ← hsum_eq, Finset.mul_sum]
    refine sum_congr rfl fun _ _ => ?_
    ring
  rw [← hcavg]
  exact hcoord v

omit [DecidableEq V] in
/-- The odd closed walk is needed: on a connected bipartite graph with at least two nodes, some
initial values make no node converge. -/
theorem not_tendsto_of_colorable [Nontrivial V] (hc : G.Connected) (h2 : G.Colorable 2) :
    ∃ x : V → ℝ, ∀ v, ¬ ∃ c, Tendsto (fun t => avgIter G t x v) atTop (𝓝 c) := by
  obtain ⟨C⟩ := h2
  let x : V → ℝ := fun w => if C w = 0 then 1 else -1
  refine ⟨x, ?_⟩
  have hdeg : ∀ w, 0 < G.degree w := fun w => hc.preconnected.degree_pos_of_nontrivial w
  have hx_ne (w : V) : x w ≠ 0 := by
    by_cases h : C w = 0 <;> simp [x, h]
  have hopp {a b : V} (hab : G.Adj a b) : x b = -x a := by
    have hne : C a ≠ C b := C.valid hab
    simp only [x]
    generalize ha : C a = ca at hne ⊢
    generalize hb : C b = cb at hne ⊢
    fin_cases ca <;> fin_cases cb
    · exact (hne rfl).elim
    · norm_num
    · norm_num
    · exact (hne rfl).elim
  have hstep (w : V) : avgStep G x w = -x w := by
    rw [avgStep]
    have hcongr : ∑ u ∈ G.neighborFinset w, x u = ∑ u ∈ G.neighborFinset w, -x w := by
      refine sum_congr rfl fun u hu => hopp ((G.mem_neighborFinset w u).mp hu)
    rw [hcongr, sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (hdeg w).ne')
  have hlin (c : ℝ) (y : V → ℝ) (w : V) :
      avgStep G (fun u => c * y u) w = c * avgStep G y w := by
    simp only [avgStep]
    rw [← Finset.mul_sum, mul_div_assoc]
  have hiter (t : ℕ) (w : V) : avgIter G t x w = (-1 : ℝ) ^ t * x w := by
    induction t generalizing w with
    | zero => simp [avgIter]
    | succ t ih =>
      rw [show avgIter G (t + 1) x w = avgStep G (avgIter G t x) w from rfl]
      have hfun : avgIter G t x = fun z => (-1 : ℝ) ^ t * x z := by
        ext z
        exact ih z
      rw [hfun, hlin, hstep, pow_succ]
      ring
  intro v
  rintro ⟨c, hc⟩
  have hto_even : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone (fun _ _ hab => Nat.mul_le_mul_left _ hab) ?_
    intro b
    refine ⟨b, ?_⟩
    calc
      b = b * 1 := (Nat.mul_one b).symm
      _ ≤ b * 2 := Nat.mul_le_mul_left _ (by decide : 1 ≤ 2)
      _ = 2 * b := Nat.mul_comm _ _
  have hto_odd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone
      (fun _ _ hab => Nat.add_le_add_right (Nat.mul_le_mul_left _ hab) _) ?_
    intro b
    refine ⟨b, ?_⟩
    calc
      b ≤ 2 * b := by
        have h : b * 1 ≤ b * 2 := Nat.mul_le_mul_left _ (by decide : 1 ≤ 2)
        rw [Nat.mul_one, Nat.mul_comm] at h
        exact h
      _ ≤ 2 * b + 1 := Nat.le_add_right _ _
  have heq_even (k : ℕ) : avgIter G (2 * k) x v = x v := by
    rw [hiter, pow_mul, show ((-1 : ℝ) ^ 2) = 1 by norm_num, one_pow, one_mul]
  have heq_odd (k : ℕ) : avgIter G (2 * k + 1) x v = -x v := by
    rw [hiter, pow_succ, pow_mul, show ((-1 : ℝ) ^ 2) = 1 by norm_num, one_pow, one_mul,
      neg_one_mul]
  have hconst_even : Tendsto (fun k => avgIter G (2 * k) x v) atTop (𝓝 (x v)) := by
    simp_rw [heq_even]
    exact tendsto_const_nhds
  have hconst_odd : Tendsto (fun k => avgIter G (2 * k + 1) x v) atTop (𝓝 (-x v)) := by
    simp_rw [heq_odd]
    exact tendsto_const_nhds
  have hcv : c = x v := tendsto_nhds_unique (hc.comp hto_even) hconst_even
  have hcn : c = -x v := tendsto_nhds_unique (hc.comp hto_odd) hconst_odd
  have : x v = 0 := by linarith
  exact hx_ne v this

end Averaging
