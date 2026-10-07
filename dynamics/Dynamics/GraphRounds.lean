import Dynamics.Uniform

/-!
# Graph-indexed rounds

Round types for dynamics on a finite simple graph `G`, to be averaged with `avg`, iterated with
`expList` and turned into kernels with `Kernel.ofStep`.

* `NeighborRound G`: a synchronous round in which every vertex samples one of its neighbours.
  It is the product over the vertices of their neighbour sets, so under the uniform
  distribution the samples are independent (`avg_neighborRound_prod`, `avg_neighborRound_mul`)
  and each is uniform among the neighbours (`avg_neighborRound_eval`). On the complete graph
  this is the round type `RumorPush.Tgt n` of `rumor_spread/`. A uniform vertex together with
  a uniform synchronous round is the sequential "random vertex, random neighbour" step
  (`avg_vertex_neighborRound`).
* `EdgeRound G`: a sequential step in which one oriented edge (a `SimpleGraph.Dart`) is
  activated. A uniform oriented edge is a uniform edge (`avg_edgeRound_edge`) with a uniform
  orientation (`avg_edgeRound_symm`); averages over it are sums over adjacent ordered pairs
  divided by `2 |E|` (`avg_edgeRound`), and its tail is degree-biased (`avg_edgeRound_fst`).

Uniform averages over the neighbours of `v` are written `avg (fun u : G.neighborSet v => g u)`,
equal to `(∑ u ∈ G.neighborFinset v, g u) / G.degree v` (`avg_neighborSet`).
-/

namespace Dynamics
open Finset

variable {V : Type*}

/-- A synchronous round on `G`: every vertex `v` picks a neighbour `r v`. Under the uniform
distribution the picks are independent and uniform among the neighbours. -/
abbrev NeighborRound (G : SimpleGraph V) := ∀ v : V, G.neighborSet v

/-- A sequential step on `G`: one oriented edge `(d.fst, d.snd)` of `G` is activated. Under the
uniform distribution this is a uniform edge with a uniform orientation. -/
abbrev EdgeRound (G : SimpleGraph V) := G.Dart

/-! ### Uniform neighbours and synchronous rounds: every vertex samples a neighbour -/

section Neighbor
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The uniform average over the neighbours of `v` is their sum divided by the degree. -/
theorem avg_neighborSet (v : V) (g : V → ℝ) :
    avg (fun u : G.neighborSet v => g u) = (∑ u ∈ G.neighborFinset v, g u) / G.degree v := by
  unfold avg
  rw [SimpleGraph.card_neighborSet_eq_degree,
    Finset.sum_subtype (p := fun u => u ∈ G.neighborSet v) (G.neighborFinset v)
      (fun u => by simp) g]

/-- With no isolated vertex, every neighbour set is nonempty. -/
theorem nonempty_neighborSet (hd : ∀ v, 0 < G.degree v) (v : V) : Nonempty (G.neighborSet v) :=
  Fintype.card_pos_iff.1 (by rw [SimpleGraph.card_neighborSet_eq_degree]; exact hd v)

/-- Synchronous rounds exist as soon as no vertex is isolated. -/
theorem neighborRound_nonempty (hd : ∀ v, 0 < G.degree v) : Nonempty (NeighborRound G) := by
  have := nonempty_neighborSet G hd
  infer_instance

variable [DecidableEq V]

/-- The number of synchronous rounds is the product of the degrees. -/
theorem card_neighborRound : Fintype.card (NeighborRound G) = ∏ v, G.degree v := by
  simp only [Fintype.card_pi, SimpleGraph.card_neighborSet_eq_degree]

/-- **Independence**: in a uniform synchronous round the vertices sample their neighbours
independently, so averages of products over the vertices factor. -/
theorem avg_neighborRound_prod (f : V → V → ℝ) :
    avg (fun r : NeighborRound G => ∏ v, f v (r v))
      = ∏ v, avg (fun u : G.neighborSet v => f v u) := by
  unfold avg
  rw [← Fintype.prod_sum (fun v (u : G.neighborSet v) => f v u), Fintype.card_pi,
    Nat.cast_prod, ← Finset.prod_div_distrib]

/-- **Marginal**: in a uniform synchronous round each vertex samples a uniform neighbour. -/
theorem avg_neighborRound_eval (hd : ∀ v, 0 < G.degree v) (v : V) (g : V → ℝ) :
    avg (fun r : NeighborRound G => g (r v)) = avg (fun u : G.neighborSet v => g u) := by
  have := nonempty_neighborSet G hd
  have key := avg_neighborRound_prod G (fun w u => if w = v then g u else 1)
  simp only [Fintype.prod_ite_eq'] at key
  rw [key, Finset.prod_eq_single v (fun w _ hw => by simp [hw, avg_const]) (by simp)]
  simp

/-- **Pairwise independence**: in a uniform synchronous round two distinct vertices sample
their neighbours independently. -/
theorem avg_neighborRound_mul (hd : ∀ v, 0 < G.degree v) {v w : V} (hvw : v ≠ w)
    (g h : V → ℝ) :
    avg (fun r : NeighborRound G => g (r v) * h (r w))
      = avg (fun u : G.neighborSet v => g u) * avg (fun u : G.neighborSet w => h u) := by
  have := nonempty_neighborSet G hd
  have key := avg_neighborRound_prod G
    (fun x u => if x = v then g u else if x = w then h u else 1)
  rw [Finset.prod_eq_mul v w hvw (fun x _ hx => by simp [hx.1, hx.2, avg_const]) (by simp)
    (by simp)] at key
  simp only [if_true, if_neg hvw.symm] at key
  rw [← key]
  congr 1
  funext r
  rw [Finset.prod_eq_mul v w hvw (fun x _ hx => by simp [hx.1, hx.2]) (by simp) (by simp)]
  simp [hvw.symm]

/-- **Linearity over the vertices**: the average of a sum of one-vertex observables is the sum of
their neighbour averages. -/
theorem avg_neighborRound_sum (hd : ∀ v, 0 < G.degree v) (f : V → V → ℝ) :
    avg (fun r : NeighborRound G => ∑ v, f v (r v))
      = ∑ v, avg (fun u : G.neighborSet v => f v u) := by
  rw [avg_sum]
  exact Finset.sum_congr rfl fun v _ => avg_neighborRound_eval G hd v (f v)

/-- **Random vertex, then random neighbour**: a uniform vertex `v` together with a uniform
synchronous round `r` realizes the sequential step "a uniform vertex `v` and a uniform neighbour
`r v` of `v`" (the death–Birth scheduler), so `V × NeighborRound G` is its round type. -/
theorem avg_vertex_neighborRound (hd : ∀ v, 0 < G.degree v) (F : V → V → ℝ) :
    avg (fun p : V × NeighborRound G => F p.1 (p.2 p.1))
      = avg (fun v => avg (fun u : G.neighborSet v => F v u)) := by
  simp_rw [← avg_neighborRound_eval G hd _ (F _)]
  unfold avg
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div, div_div,
    mul_comm]

end Neighbor

/-! ### Sequential rounds: one uniformly random oriented edge per step -/

section Edge

/-- Sequential steps exist as soon as `G` has an edge. -/
theorem edgeRound_nonempty (G : SimpleGraph V) {u v : V} (h : G.Adj u v) :
    Nonempty (EdgeRound G) := by
  exact ⟨⟨(u, v), h⟩⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Uniform orientation**: averages are invariant under reversing the activated edge. -/
theorem avg_edgeRound_symm (F : V → V → ℝ) :
    avg (fun d : EdgeRound G => F d.snd d.fst) = avg (fun d : EdgeRound G => F d.fst d.snd) := by
  exact avg_equiv (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive)
    (fun d : EdgeRound G => F d.fst d.snd)

variable [DecidableEq V]

/-- **Uniform oriented edge**: the average over the activated oriented edge is the sum over the
adjacent ordered pairs divided by `2 |E|`. -/
theorem avg_edgeRound (F : V → V → ℝ) :
    avg (fun d : EdgeRound G => F d.fst d.snd)
      = (∑ v, ∑ u ∈ G.neighborFinset v, F v u) / (2 * G.edgeFinset.card) := by
  unfold avg
  rw [G.dart_card_eq_twice_card_edges]
  push_cast
  congr 1
  rw [← Finset.sum_fiberwise Finset.univ (fun d : G.Dart => d.fst) (fun d => F d.fst d.snd)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [G.dart_fst_fiber v, Finset.sum_image fun x _ y _ h => G.dartOfNeighborSet_injective v h]
  exact (Finset.sum_subtype (p := fun u => u ∈ G.neighborSet v) (G.neighborFinset v)
    (fun u => by simp) (F v)).symm

/-- **Uniform edge**: the underlying edge of a uniform oriented edge is a uniform edge. -/
theorem avg_edgeRound_edge (g : Sym2 V → ℝ) :
    avg (fun d : EdgeRound G => g d.edge) = avg (fun e : G.edgeSet => g e) := by
  unfold avg
  rw [G.dart_card_eq_twice_card_edges, ← SimpleGraph.card_edgeSet,
    ← Finset.sum_fiberwise_of_maps_to (g := SimpleGraph.Dart.edge) (t := G.edgeFinset)
      (fun d _ => by simp)]
  rw [Finset.sum_subtype (p := fun e => e ∈ G.edgeSet) G.edgeFinset (fun e => by simp)
    (fun e => ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.edge = e), g d.edge)]
  have h2 : ∀ e : G.edgeSet,
      ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.edge = e), g d.edge = 2 * g e := by
    intro e
    rw [Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.1 hd).2]),
      Finset.sum_const, G.dart_edge_fiber_card e e.2, nsmul_eq_mul]
    norm_num
  simp_rw [h2, ← Finset.mul_sum]
  push_cast
  rw [mul_div_mul_left _ _ two_ne_zero]

/-- **Degree bias**: the tail of a uniform oriented edge is `v` with probability
`deg v / 2 |E|`. -/
theorem avg_edgeRound_fst (g : V → ℝ) :
    avg (fun d : EdgeRound G => g d.fst)
      = (∑ v, G.degree v * g v) / (2 * G.edgeFinset.card) := by
  rw [avg_edgeRound G (fun v _ => g v)]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

end Edge

end Dynamics
