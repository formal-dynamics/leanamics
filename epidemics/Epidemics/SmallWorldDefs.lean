import Epidemics.GiantEpidemic
import Epidemics.Subcritical

/-! # One-dimensional small-world graphs (EPI-6, definitions)

L. Becchetti, A. Clementi, R. Denni, F. Pasquale, L. Trevisan, I. Ziccardi, *Percolation and
epidemic processes in one-dimensional small-world networks*, arXiv:2103.16398 [BCDPTZ22].

A one-dimensional small-world graph on `n` nodes is the cycle `C_n` (Mathlib's `cycleGraph n`
on `Fin n`) together with random *bridges*:

* `SWG(n, q)` (Definition 1.1, `n ≥ 3`): the bridges are the edges of the Erdős–Rényi graph
  `G(n, q)`. As in EPI-3, `G(n, q)` is `perc ⊤ b` with i.i.d. Bernoulli(`q`) coins
  `b ~ coins q`, so `SWG(n, q)` is `swg n b` with `b ~ coins q`.
* `3-SWG(n)` (Definition 1.2, `n ≥ 4` even): the bridges are the edges of a uniformly random
  perfect matching `M ~ uniformMatching n` (a perfect matching of the complete graph in the sense
  of Mathlib's `Subgraph.IsPerfectMatching`), so `3-SWG(n)` is `swg3 n M`.

An edge that is both a cycle edge and a bridge is a single edge of the graph (the union of the
edge sets), as in the paper. Bond percolation with parameter `p` on a sampled graph `G` is
`perc G ω` with independent Bernoulli(`p`) coins `ω ~ coins p` (EPI-1). The probability of an
event over both the graph and the percolation is written as the iterated expectation
`(coins q).expect fun b => (coins p).prob fun ω => …` (resp. `(uniformMatching n hn).expect`),
the probability under the product of the two independent laws.

`swgThreshold c = (√(c² + 6c + 1) − c − 1) / (2c)` is the critical percolation probability of
`SWG(n, c/n)` (Theorems 2.1 and 2.4): the root in `(0, 1)` of `c p (1 + p) / (1 - p) = 1`, where
`c p` is the mean number of percolated bridges at a node and `(1 + p) / (1 - p)` the mean size of
the percolated cycle cluster around a node (the "local cluster", Fact A.4). For `3-SWG(n)` the
critical value is `1/2`, the root of `p ((1 + p) / (1 - p) - 1) = 2 p² / (1 - p) = 1` (§3.2).

Proved here: the algebra of the thresholds (`swgThreshold_spec`, `lt_swgThreshold_iff`, …),
existence of perfect matchings for even `n` (`PerfectMatching.nonempty`) and the degree bound
`swg3_degree_le` (`3-SWG(n)` has maximum degree `3`).
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

/-- Adjacency in the percolated graph is decidable when adjacency in the host graph is. -/
instance perc.decidableAdj {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) : DecidableRel (perc G ω).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ ω s(u, v) = true))

/-! ### The threshold of `SWG(n, c/n)` -/

/-- The critical percolation probability of `SWG(n, c/n)` ([BCDPTZ22] Theorems 2.1 and 2.4):
`p* = (√(c² + 6c + 1) − c − 1) / (2c)`. -/
noncomputable def swgThreshold (c : ℝ) : ℝ :=
  (Real.sqrt (c ^ 2 + 6 * c + 1) - c - 1) / (2 * c)

section Threshold

variable {c : ℝ}

/-- The defining equation of `p* = swgThreshold c`: `c p* (1 + p*) = 1 - p*`, i.e. the mean
offspring `c p (1 + p) / (1 - p)` of the exploration of [BCDPTZ22] §3.1 equals `1` at `p*`. -/
theorem swgThreshold_spec (hc : 0 < c) :
    c * swgThreshold c * (1 + swgThreshold c) = 1 - swgThreshold c := by
  unfold swgThreshold
  set s := Real.sqrt (c ^ 2 + 6 * c + 1)
  have hs : s ^ 2 = c ^ 2 + 6 * c + 1 := Real.sq_sqrt (by positivity)
  field_simp
  linear_combination hs

/-- `p* > 0`. -/
theorem swgThreshold_pos (hc : 0 < c) : 0 < swgThreshold c := by
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ c ^ 2 + 6 * c + 1)
  have h0 := Real.sqrt_nonneg (c ^ 2 + 6 * c + 1)
  unfold swgThreshold
  apply div_pos _ (by positivity)
  nlinarith

/-- `p* < 1`. -/
theorem swgThreshold_lt_one (hc : 0 < c) : swgThreshold c < 1 := by
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ c ^ 2 + 6 * c + 1)
  have h0 := Real.sqrt_nonneg (c ^ 2 + 6 * c + 1)
  unfold swgThreshold
  rw [div_lt_one (by positivity)]
  nlinarith

/-- Below the threshold the mean offspring is `< 1`: for `p ≥ 0`,
`p < p* ↔ c p (1 + p) < 1 - p`. -/
theorem lt_swgThreshold_iff (hc : 0 < c) {p : ℝ} (hp : 0 ≤ p) :
    p < swgThreshold c ↔ c * p * (1 + p) < 1 - p := by
  have hspec := swgThreshold_spec hc
  have hpos := swgThreshold_pos hc
  constructor
  · intro h
    nlinarith [mul_pos hc (sub_pos.mpr h)]
  · intro h
    by_contra hle
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr (not_lt.mp hle))]

/-- Above the threshold the mean offspring is `> 1`: for `p ≥ 0`,
`p* < p ↔ 1 - p < c p (1 + p)`. -/
theorem swgThreshold_lt_iff (hc : 0 < c) {p : ℝ} (hp : 0 ≤ p) :
    swgThreshold c < p ↔ 1 - p < c * p * (1 + p) := by
  have hspec := swgThreshold_spec hc
  have hpos := swgThreshold_pos hc
  constructor
  · intro h
    nlinarith [mul_pos hc (sub_pos.mpr h)]
  · intro h
    by_contra hle
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr (not_lt.mp hle))]

/-- For `c = 1` (one bridge per node on average, as in `3-SWG(n)`) the threshold is `√2 - 1`
([BCDPTZ22] §2.1). -/
theorem swgThreshold_one : swgThreshold 1 = Real.sqrt 2 - 1 := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  unfold swgThreshold
  norm_num [h8]
  ring

end Threshold

/-- The threshold `1/2` of `3-SWG(n)`: for `p ≥ 0`, `p < 1/2 ↔ 2 p² < 1 - p`, i.e. the mean
offspring `2 p² / (1 - p)` of the exploration of [BCDPTZ22] §3.2 is `< 1`. -/
theorem lt_half_iff {p : ℝ} (hp : 0 ≤ p) : p < 1 / 2 ↔ 2 * p ^ 2 < 1 - p := by
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hle
    nlinarith

/-! ### `SWG(n, q)` -/

/-- **`SWG(n, q)`** ([BCDPTZ22] Definition 1.1): the one-dimensional small-world graph on
`Fin n` whose bridges are given by the coins `b`: the cycle `C_n` together with the pairs
`{u, v}` with `b s(u, v) = true`. With `b ~ coins q` the bridges form the Erdős–Rényi graph
`G(n, q)` (`perc ⊤ b`), and `swg n b` is distributed as `SWG(n, q)`. -/
def swg (n : ℕ) (b : Sym2 (Fin n) → Bool) : SimpleGraph (Fin n) :=
  cycleGraph n ⊔ perc ⊤ b

/-- Adjacency in `swg n b` is decidable (cycle or open bridge). -/
instance swg.decidableAdj (n : ℕ) (b : Sym2 (Fin n) → Bool) : DecidableRel (swg n b).Adj :=
  inferInstanceAs (DecidableRel (cycleGraph n ⊔ perc ⊤ b).Adj)

/-! ### `3-SWG(n)` -/

/-- The perfect matchings on `V`: the perfect matchings of the complete graph on `V`, in the
sense of Mathlib (`Subgraph.IsPerfectMatching`; every vertex has exactly one neighbour,
`Subgraph.isPerfectMatching_iff`). -/
def PerfectMatching (V : Type*) : Type _ :=
  {M : (⊤ : SimpleGraph V).Subgraph // M.IsPerfectMatching}

/-- There are finitely many perfect matchings on a finite type (classical: being a perfect
matching is not decidable in general). -/
noncomputable instance PerfectMatching.instFintype {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype (PerfectMatching V) := by
  classical
  exact inferInstanceAs (Fintype {M : (⊤ : SimpleGraph V).Subgraph // M.IsPerfectMatching})

/-- A perfect matching on `V` exists when `|V|` is even (Mathlib's
`IsClique.even_iff_exists_isMatching` for the clique `V` of the complete graph). -/
theorem PerfectMatching.nonempty {V : Type*} [Fintype V] (h : Even (Fintype.card V)) :
    Nonempty (PerfectMatching V) := by
  obtain ⟨M, hMv, hM⟩ := ((IsClique.top (Set.univ : Set V)).even_iff_exists_isMatching
    Set.finite_univ).mp (by rwa [Set.ncard_univ, Nat.card_eq_fintype_card])
  exact ⟨⟨M, hM, fun v => by simp [hMv]⟩⟩

/-- **The uniformly random perfect matching** on `Fin n`, `n` even ([BCDPTZ22]
Definition 1.2). -/
noncomputable def uniformMatching (n : ℕ) (hn : Even n) :
    Distribution (PerfectMatching (Fin n)) :=
  haveI := PerfectMatching.nonempty (V := Fin n) (by rwa [Fintype.card_fin])
  Distribution.uniform _

/-- **`3-SWG(n)`** ([BCDPTZ22] Definition 1.2): the cycle `C_n` on `Fin n` together with the
edges of the perfect matching `M`. With `M ~ uniformMatching n hn`, `swg3 n M` is distributed as
`3-SWG(n)`. -/
def swg3 (n : ℕ) (M : PerfectMatching (Fin n)) : SimpleGraph (Fin n) :=
  cycleGraph n ⊔ M.1.spanningCoe

/-- Adjacency in `swg3 n M`, classically decidable (the matching is a Mathlib subgraph, whose
adjacency is not decidable in general; the value of `run` does not depend on this choice). -/
noncomputable instance swg3.decidableAdj (n : ℕ) (M : PerfectMatching (Fin n)) :
    DecidableRel (swg3 n M).Adj :=
  Classical.decRel _

/-- Every node of the cycle `C_n` has at most two neighbours. -/
theorem cycleGraph_degree_le_two (n : ℕ) (v : Fin n) : (cycleGraph n).degree v ≤ 2 := by
  match n, v with
  | 0, v => exact v.elim0
  | 1, v =>
    have := (cycleGraph 1).degree_lt_card_verts v
    rw [Fintype.card_fin] at this
    omega
  | n + 2, v => rw [cycleGraph_degree_two_le]; exact card_le_two

/-- `3-SWG(n)` has maximum degree at most `3` ([BCDPTZ22] §1: two cycle neighbours and one
matching partner). -/
theorem swg3_degree_le (n : ℕ) (M : PerfectMatching (Fin n)) (v : Fin n) :
    (swg3 n M).degree v ≤ 3 := by
  obtain ⟨w, -, hw⟩ := Subgraph.isPerfectMatching_iff.mp M.2 v
  have hsub : (swg3 n M).neighborFinset v ⊆ insert w ((cycleGraph n).neighborFinset v) := by
    intro y hy
    simp only [mem_neighborFinset, swg3, sup_adj, Subgraph.spanningCoe_adj] at hy
    rcases hy with h | h
    · exact mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr h)
    · exact mem_insert.mpr (Or.inl (hw y h))
  calc (swg3 n M).degree v = ((swg3 n M).neighborFinset v).card :=
        (card_neighborFinset_eq_degree _ _).symm
    _ ≤ (insert w ((cycleGraph n).neighborFinset v)).card := card_le_card hsub
    _ ≤ ((cycleGraph n).neighborFinset v).card + 1 := card_insert_le _ _
    _ ≤ 3 := by rw [card_neighborFinset_eq_degree]; linarith [cycleGraph_degree_le_two n v]

end Epidemics
