import Epidemics.SmallWorldCollapse

/-! # Subcritical `SWG(n, c/n)`: all clusters are small (EPI-6)

[BCDPTZ22] Lemma C.1 (claim 2 of Theorem 2.1): below the threshold `p* = swgThreshold c`, every
connected component of the percolated `SWG(n, c/n)` has `O(log n)` nodes, w.h.p.

By `expect_prob_swg_eq` the percolated `SWG(n, q)` is the percolation of the complete graph with
independent coins, of probability `p` on the cycle edges and `p q = p c / n` on the other pairs.
Its clusters are explored breadth-first (`Explore`), giving every discovered node the weight `1`
if it was discovered through a cycle edge and `1 + p₀` otherwise (`swgWeight`), where
`p₀ = p* - ε`. A node discovered through a cycle edge has at most one undiscovered cycle
neighbour, any other node at most two, and every node has at most `n` other undiscovered
neighbours, each reached by a bridge with probability `p c / n`. With
`δ = 1 - p₀ - c p₀ (1 + p₀) > 0` (the subcritical condition, `lt_swgThreshold_iff`), the expected
weight discovered from a node of weight `w` is therefore at most `(1 - δ / 2) w` (`swg_step`):
this is the two-type Galton–Watson comparison behind the paper's variable
`W = Y + ∑_{j ≤ 2Y} L_j`, with the weights a left eigenvector of the mean
matrix. The supermartingale tail bound `Explore.prob_cluster_gt_le` and a union bound over the
`n` nodes conclude, with `β = 64 / δ²` and failure probability `2 / n`.
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

variable {n : ℕ}

/-! ### The union bound -/

section Union

variable {V Ω : Type*} [Fintype V] [Fintype Ω]

/-- **Union bound over the components**, for any random graph: if the cluster of every vertex
has more than `⌊L⌋₊` vertices with probability at most `β`, then all components have at most `L`
vertices with probability at least `1 - n β`. -/
theorem prob_components_le_of_tail' (P : Distribution Ω) (H : Ω → SimpleGraph V) {L β : ℝ}
    (hL : 0 ≤ L)
    (htail : ∀ s : V,
      P.prob (fun ω => ⌊L⌋₊ < ((H ω).connectedComponentMk s).supp.ncard) ≤ β) :
    1 - Fintype.card V * β ≤
      P.prob fun ω => ∀ K : (H ω).ConnectedComponent, (K.supp.ncard : ℝ) ≤ L := by
  have hbad : P.prob (fun ω => ¬∀ K : (H ω).ConnectedComponent, (K.supp.ncard : ℝ) ≤ L) ≤
      Fintype.card V * β := by
    calc _ ≤ P.prob (fun ω => ∃ s ∈ (univ : Finset V),
          ⌊L⌋₊ < ((H ω).connectedComponentMk s).supp.ncard) := by
          refine Distribution.prob_mono _ fun ω hω => ?_
          push Not at hω
          obtain ⟨K, hK⟩ := hω
          obtain ⟨s, rfl⟩ := K.exists_rep
          exact ⟨s, mem_univ s, (Nat.floor_lt hL).mpr hK⟩
      _ ≤ ∑ s : V, P.prob (fun ω => ⌊L⌋₊ < ((H ω).connectedComponentMk s).supp.ncard) :=
          prob_exists_le_sum _ _ _
      _ ≤ ∑ _s : V, β := sum_le_sum fun s _ => htail s
      _ = Fintype.card V * β := by rw [sum_const, card_univ, nsmul_eq_mul]
  linarith [prob_not P (fun ω => ∀ K : (H ω).ConnectedComponent, (K.supp.ncard : ℝ) ≤ L)]

end Union

/-! ### The weights and the one-step bound -/

/-- The weight of a node discovered through the pair `e`: `1` through a cycle edge, `1 + p₀`
through a bridge. -/
noncomputable def swgWeight (n : ℕ) (p₀ : ℝ) (e : Sym2 (Fin n)) : ℝ := by
  classical
  exact if e ∈ (cycleGraph n).edgeSet then 1 else 1 + p₀

lemma swgWeight_bounds {p₀ : ℝ} (h0 : 0 ≤ p₀) (h1 : p₀ ≤ 1) (e : Sym2 (Fin n)) :
    1 ≤ swgWeight n p₀ e ∧ swgWeight n p₀ e ≤ 2 := by
  unfold swgWeight
  split_ifs <;> constructor <;> linarith

/-- **One step of the exploration of the percolated `SWG(n, q)`**: if `p ≤ p₀`, `q n = c` and
`λ` dominates the two rows of the mean matrix (`p₀ + c p₀ (1 + p₀) ≤ λ` for a node discovered
through a cycle edge, `2 p₀ + c p₀ (1 + p₀) ≤ λ (1 + p₀)` for the root and a node discovered
through a bridge), then the expected weight discovered from the current node is at most `λ`
times its weight. -/
lemma swg_step {p p₀ q c lam : ℝ} (hp0 : 0 ≤ p) (hpp : p ≤ p₀) (hq0 : 0 ≤ q)
    (hqn : q * n = c) (hC : p₀ + c * p₀ * (1 + p₀) ≤ lam)
    (hB : 2 * p₀ + c * p₀ * (1 + p₀) ≤ lam * (1 + p₀)) (s : Fin n)
    (σ : Explore.State (Fin n)) (hσ : Explore.Inv (G := ⊤) (h := swgWeight n p₀) s (1 + p₀) σ)
    (hp : σ.proc < σ.order.length) :
    ∑ y ∈ Explore.fresh ⊤ σ σ.order[σ.proc],
        swgRate n p q s(σ.order[σ.proc], y) * swgWeight n p₀ s(σ.order[σ.proc], y) ≤
      lam * σ.wt σ.order[σ.proc] := by
  classical
  set v := σ.order[σ.proc]
  have hvo : v ∈ σ.order := List.getElem_mem hp
  have hp₀ : 0 ≤ p₀ := hp0.trans hpp
  have hc : 0 ≤ c := by rw [← hqn]; positivity
  set F := Explore.fresh ⊤ σ v
  set Fc := F.filter fun y => (cycleGraph n).Adj v y
  -- the sum splits into cycle neighbours and bridges
  have hsplit : ∑ y ∈ F, swgRate n p q s(v, y) * swgWeight n p₀ s(v, y) =
      p * Fc.card + (F.filter fun y => ¬(cycleGraph n).Adj v y).card * (p * q * (1 + p₀)) := by
    rw [← sum_filter_add_sum_filter_not F fun y => (cycleGraph n).Adj v y]
    congr 1
    · calc _ = ∑ _y ∈ Fc, p := sum_congr rfl fun y hy => by
            have := (mem_filter.mp hy).2
            simp only [swgRate, swgWeight, mem_edgeSet, if_pos this, mul_one]
        _ = p * Fc.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
    · calc _ = ∑ _y ∈ F.filter (fun y => ¬(cycleGraph n).Adj v y), p * q * (1 + p₀) :=
            sum_congr rfl fun y hy => by
              have := (mem_filter.mp hy).2
              simp only [swgRate, swgWeight, mem_edgeSet, if_neg this]
        _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hbridge : ((F.filter fun y => ¬(cycleGraph n).Adj v y).card : ℝ) * (p * q * (1 + p₀)) ≤
      c * p₀ * (1 + p₀) := by
    have hcard : ((F.filter fun y => ¬(cycleGraph n).Adj v y).card : ℝ) ≤ n := by
      have := card_le_univ (F.filter fun y => ¬(cycleGraph n).Adj v y)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    calc _ ≤ (n : ℝ) * (p * q * (1 + p₀)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = c * p * (1 + p₀) := by rw [← hqn]; ring
      _ ≤ c * p₀ * (1 + p₀) := by gcongr
  have hFc : Fc ⊆ (cycleGraph n).neighborFinset v := fun y hy => by
    rw [mem_filter] at hy
    exact (mem_neighborFinset _ _ _).mpr hy.2
  have hFc2 : (Fc.card : ℝ) ≤ 2 := by
    have := (card_le_card hFc).trans
      ((card_neighborFinset_eq_degree _ _).trans_le (cycleGraph_degree_le_two n v))
    exact_mod_cast this
  have hsum : ∑ y ∈ F, swgRate n p q s(v, y) * swgWeight n p₀ s(v, y) ≤
      p₀ * Fc.card + c * p₀ * (1 + p₀) := by
    rw [hsplit]
    have : p * Fc.card ≤ p₀ * Fc.card := mul_le_mul_of_nonneg_right hpp (Nat.cast_nonneg _)
    linarith
  -- the type of the current node
  by_cases hvs : v = s
  · rw [hvs, hσ.root_wt]
    rw [hvs] at hsum
    nlinarith
  obtain ⟨u, hu, -, hw⟩ := hσ.parent v hvo hvs
  rw [hw]
  by_cases huv : (cycleGraph n).Adj u v
  · -- discovered through a cycle edge: one cycle neighbour is already discovered
    have hFc1 : (Fc.card : ℝ) ≤ 1 := by
      have hsub : Fc ⊆ ((cycleGraph n).neighborFinset v).erase u := fun y hy => by
        refine mem_erase.mpr ⟨fun hyu => ?_, hFc hy⟩
        rw [mem_filter] at hy
        exact (Explore.mem_fresh.mp hy.1).1 (hyu ▸ hu)
      have h1 := card_le_card hsub
      rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr huv.symm),
        card_neighborFinset_eq_degree] at h1
      have h2 := cycleGraph_degree_le_two n v
      have : Fc.card ≤ 1 := by omega
      exact_mod_cast this
    have hwt : swgWeight n p₀ s(u, v) = 1 := by
      simp only [swgWeight, mem_edgeSet, if_pos huv]
    rw [hwt]
    nlinarith
  · have hwt : swgWeight n p₀ s(u, v) = 1 + p₀ := by
      simp only [swgWeight, mem_edgeSet, if_neg huv]
    rw [hwt]
    nlinarith

/-! ### The union-bound arithmetic -/

/-- For `n ≥ 2` and `0 < δ ≤ 1`, the tail of `Explore.prob_cluster_gt_le` at `θ = δ / 8`,
`κ = 1 + δ / 4`, `λ = 1 - δ / 2`, `wmin = 1`, `wmax = 2` and `t = ⌊(64 / δ²) log n⌋₊` is at most
`2 / n²`. -/
lemma swg_tail_arith {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 2 ≤ n) :
    (n : ℝ) * Real.exp (-(δ / 8 * ((1 - (1 + δ / 4) * (1 - δ / 2)) *
        (⌊64 / δ ^ 2 * Real.log n⌋₊ : ℕ) * 1 - 2))) ≤ 2 / n := by
  set L := 64 / δ ^ 2 * Real.log n with hL
  set k := ⌊L⌋₊
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hLnn : 0 ≤ L := by positivity
  have hk : L - 1 ≤ k := by linarith [Nat.lt_floor_add_one L]
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hδL : δ ^ 2 * L = 64 * Real.log n := by rw [hL]; field_simp
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  -- the exponent is at most `1/2 - 2 log n`
  have hexp : -(δ / 8 * ((1 - (1 + δ / 4) * (1 - δ / 2)) * (k : ℝ) * 1 - 2)) ≤
      1 / 2 - 2 * Real.log n := by
    have h1 : δ ^ 2 * (L - 1) ≤ δ ^ 2 * k := mul_le_mul_of_nonneg_left hk hδ2.le
    have h2 : 0 ≤ δ ^ 3 * k := by positivity
    nlinarith
  have hhalf : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hlogn : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
    rw [show 2 * Real.log n = Real.log n + Real.log n by ring, Real.exp_add,
      Real.exp_log hnpos]
    ring
  calc (n : ℝ) * Real.exp (-(δ / 8 * ((1 - (1 + δ / 4) * (1 - δ / 2)) * (k : ℝ) * 1 - 2)))
      ≤ n * Real.exp (1 / 2 - 2 * Real.log n) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hnpos.le
    _ = Real.exp (1 / 2) / n := by
        rw [Real.exp_sub, hlogn]
        field_simp
    _ ≤ 2 / n := div_le_div_of_nonneg_right hhalf hnpos.le

/-! ### Lemma C.1 -/

/-- **Lemma C.1 of [BCDPTZ22]** with explicit constants: let `c > 0`, `0 < p₀ < 1` with
`δ = 1 - p₀ - c p₀ (1 + p₀) > 0` (that is, `p₀ < p*`), and `n ≥ 2`. For `q n = c` and every
`p ≤ p₀`, with probability at least `1 - 2 / n` over the graph `swg n b` (`b ~ coins q`) and the
percolation `ω ~ coins p`, every connected component of `perc (swg n b) ω` has at most
`(64 / δ²) log n` nodes. -/
theorem swg_components_small {c p₀ : ℝ} (hp₀0 : 0 ≤ p₀) (hp₀1 : p₀ ≤ 1)
    (hδ : 0 < 1 - p₀ - c * p₀ * (1 + p₀)) (hc : 0 ≤ c) (hn : 2 ≤ n)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqn : q * n = c)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hpp : p ≤ p₀) :
    1 - 2 / n ≤ (coins q hq0 hq1).expect fun b => (coins p hp0 hp1).prob fun ω =>
      ∀ K : (perc (swg n b) ω).ConnectedComponent,
        (K.supp.ncard : ℝ) ≤ 64 / (1 - p₀ - c * p₀ * (1 + p₀)) ^ 2 * Real.log n := by
  set δ := 1 - p₀ - c * p₀ * (1 + p₀) with hδdef
  have hδ1 : δ ≤ 1 := by
    have : 0 ≤ c * p₀ * (1 + p₀) := by positivity
    linarith
  set L := 64 / δ ^ 2 * Real.log n
  have hL : 0 ≤ L := by have := Real.log_natCast_nonneg n; positivity
  rw [expect_prob_swg_eq hp0 hp1 hq0 hq1
    (fun H => ∀ K : H.ConnectedComponent, (K.supp.ncard : ℝ) ≤ L)]
  have hunion := prob_components_le_of_tail'
    (Distribution.independent fun e => Distribution.bernoulli (swgRate n p q e)
      (swgRate_nonneg hp0 hq0 e) (swgRate_le_one hp0 hp1 hq1 e))
    (fun ω => perc (⊤ : SimpleGraph (Fin n)) ω) hL fun s =>
      Explore.prob_cluster_gt_le (G := ⊤) (h := swgWeight n p₀) (swgRate n p q)
        (swgRate_nonneg hp0 hq0) (swgRate_le_one hp0 hp1 hq1) (w₀ := 1 + p₀) (wmin := 1)
        (wmax := 2) (lam := 1 - δ / 2) (θ := δ / 8) (κ := 1 + δ / 4)
        (swgWeight_bounds hp₀0 hp₀1) ⟨by linarith, by linarith⟩ zero_le_one (by positivity)
        (by linarith) (by linarith) (by nlinarith) s
        (fun σ hσ hp => swg_step hp0 hpp hq0 hqn (by nlinarith) (by nlinarith) s σ hσ hp) _
  rw [Fintype.card_fin] at hunion
  refine le_trans ?_ hunion
  linarith [swg_tail_arith (by linarith : 0 < δ) hδ1 hn]

end Epidemics
