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
  Plain sums over the darts are double sums over the adjacent ordered pairs (`sum_dart`, via
  `dartEquiv`); differences along a walk telescope over its darts (`walk_sum_darts`), and
  squared differences over distinct darts are bounded by the Dirichlet energy
  (`sum_darts_sq_le`).
  On the complete graph `⊤` it is a uniform ordered pair of distinct vertices
  (`edgeRoundTopEquiv`, `card_edgeRound_top`, `sum_edgeRound_top`), the scheduler of population
  protocols. A one-way protocol updates the responder `d.snd` against the initiator `d.fst`
  (`oneWayStep`).

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

/-- One step of a one-way pairwise protocol with transition rule `δ` on the activated oriented
edge `d`: the responder `d.snd` takes `δ (s d.snd) (s d.fst)` against the initiator `d.fst`, and
every other vertex keeps its state. -/
def oneWayStep [DecidableEq V] {G : SimpleGraph V} {S : Type*} (δ : S → S → S) (s : V → S)
    (d : EdgeRound G) : V → S :=
  Function.update s d.snd (δ (s d.snd) (s d.fst))

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
      = ∏ v, avg (fun u : G.neighborSet v => f v u) :=
  avg_pi_prod fun v (u : G.neighborSet v) => f v u

/-- **Marginal**: in a uniform synchronous round each vertex samples a uniform neighbour. -/
theorem avg_neighborRound_eval (hd : ∀ v, 0 < G.degree v) (v : V) (g : V → ℝ) :
    avg (fun r : NeighborRound G => g (r v)) = avg (fun u : G.neighborSet v => g u) := by
  have := nonempty_neighborSet G hd
  exact avg_pi_eval (β := fun w => G.neighborSet w) v fun u => g u

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

/-- The darts of `G` are the adjacent ordered pairs. -/
def dartEquiv (G : SimpleGraph V) : G.Dart ≃ {p : V × V // G.Adj p.1 p.2} where
  toFun d := ⟨d.toProd, d.adj⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Differences along a walk telescope. -/
theorem walk_sum_darts {G : SimpleGraph V} (ψ : V → ℝ) {u v : V} (p : G.Walk u v) :
    (p.darts.map fun d => ψ d.fst - ψ d.snd).sum = ψ u - ψ v := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    ring

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A sum over the darts of `G` is a sum over the adjacent ordered pairs. -/
theorem sum_dart (f : V → V → ℝ) :
    ∑ d : G.Dart, f d.fst d.snd = ∑ a, ∑ b, if G.Adj a b then f a b else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if G.Adj a b then f a b else 0),
    ← Finset.sum_filter,
    Finset.sum_subtype (p := fun p : V × V => G.Adj p.1 p.2) _ (by simp)]
  exact Fintype.sum_equiv (dartEquiv G) _ _ fun _ => rfl

/-- **Uniform orientation**: averages are invariant under reversing the activated edge. -/
theorem avg_edgeRound_symm (F : V → V → ℝ) :
    avg (fun d : EdgeRound G => F d.snd d.fst) = avg (fun d : EdgeRound G => F d.fst d.snd) := by
  exact avg_equiv (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive)
    (fun d : EdgeRound G => F d.fst d.snd)

variable [DecidableEq V]

variable {G} in
/-- Squared differences over distinct darts are bounded by the Dirichlet energy
`∑_{i ∼ j} (ψ i - ψ j)²` (each edge counted in both orientations). -/
theorem sum_darts_sq_le (ψ : V → ℝ) (S : Finset G.Dart) :
    ∑ d ∈ S, (ψ d.fst - ψ d.snd) ^ 2 ≤
      ∑ i, ∑ j, if G.Adj i j then (ψ i - ψ j) ^ 2 else 0 := by
  have hinj : Set.InjOn (fun d : G.Dart => d.toProd) S :=
    fun d₁ _ d₂ _ h => SimpleGraph.Dart.ext d₁ d₂ h
  calc ∑ d ∈ S, (ψ d.fst - ψ d.snd) ^ 2
      = ∑ q ∈ S.image (fun d : G.Dart => d.toProd), (ψ q.1 - ψ q.2) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ q ∈ univ.filter (fun q : V × V => G.Adj q.1 q.2), (ψ q.1 - ψ q.2) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨d, -, rfl⟩ := mem_image.mp hq
          simp [d.adj]
        · intros
          positivity
    _ = _ := by rw [Finset.sum_filter, Fintype.sum_prod_type]

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

/-! ### The complete graph: one uniformly random ordered pair of distinct vertices per step -/

section Complete

/-- On the complete graph, an oriented edge is an ordered pair of distinct vertices (the
"random ordered pair" scheduler of population protocols). -/
def edgeRoundTopEquiv : EdgeRound (⊤ : SimpleGraph V) ≃ {p : V × V // p.1 ≠ p.2} where
  toFun d := ⟨d.toProd, (SimpleGraph.top_adj _ _).1 d.adj⟩
  invFun p := ⟨p.1, (SimpleGraph.top_adj _ _).2 p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype V] [DecidableEq V]

/-- The complete graph on `n` vertices has `n (n - 1)` oriented edges: twice its
`n choose 2` edges. -/
theorem card_edgeRound_top :
    Fintype.card (EdgeRound (⊤ : SimpleGraph V)) = Fintype.card V * (Fintype.card V - 1) := by
  rw [SimpleGraph.dart_card_eq_twice_card_edges,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Nat.choose_two_right,
    Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]

/-- On the complete graph, a sum over the oriented edges is the sum over all ordered pairs minus
the diagonal. -/
theorem sum_edgeRound_top (F : V → V → ℝ) :
    ∑ d : EdgeRound (⊤ : SimpleGraph V), F d.fst d.snd = ∑ u, ∑ v, F u v - ∑ v, F v v := by
  rw [sum_dart, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
  simp only [SimpleGraph.top_adj, ne_eq, not_true_eq_false, if_false, zero_add]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun v hv => if_pos (Ne.symm (Finset.ne_of_mem_erase hv))

end Complete

end Dynamics
