import Mathlib
import Dynamics.Uniform

/-! # Averaging whenever you meet: the opportunistic protocol

Becchetti, Clementi, Manurangsi, Natale, Pasquale, Raghavendra, Trevisan, *Average whenever you
meet: opportunistic protocols for community detection*, ESA 2018, arXiv:1703.05045 (numbering of
arXiv v3). In every round one edge of a finite graph is activated, chosen uniformly and
independently at random. A node activated for the first time draws a uniform value `±1`, and the
two endpoints of the active edge replace their values by their average (Algorithm 1,
`Averaging(δ)` with `δ = 1/2`).

A uniformly random edge is drawn as a uniformly random dart (oriented edge): every edge carries
exactly two darts (`avg_dart_edge`). The rounds are i.i.d. uniform darts, so expectations over `T`
rounds are `Dynamics.expList G.Dart T`. As in the paper (principle of deferred decisions,
Section 3), the first-activation coins are drawn in advance as a uniform vector `σ : V → ℤˣ`,
independent of the edges; `oppRun_getD` shows that the protocol then runs the averaging process
`avgRun` started at `x⁽⁰⁾ = σ`.
-/

namespace Averaging.Opportunistic
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The real vector `x⁽⁰⁾ ∈ {-1, 1}ⁿ` of the initial signs `σ`. -/
def signVec (σ : V → ℤˣ) : V → ℝ := fun v => ((σ v : ℤ) : ℝ)

/-- One round of `Averaging(1/2)` (Algorithm 1) on the active edge `{d.fst, d.snd}`: both
endpoints take the average of their two values; the other values are unchanged. -/
noncomputable def edgeAvg (x : V → ℝ) (d : G.Dart) : V → ℝ :=
  fun w => if w = d.fst ∨ w = d.snd then (x d.fst + x d.snd) / 2 else x w

/-- The state `x⁽ᵗ⁾ = W_t ⋯ W_1 x⁽⁰⁾` after the rounds `l`, the first round first. -/
noncomputable def avgRun (x : V → ℝ) (l : List G.Dart) : V → ℝ :=
  l.foldl (edgeAvg G) x

/-- One round of the opportunistic protocol. A node holds `none` until its first activation; an
endpoint that still holds `none` uses its coin `σ`, then both endpoints average. -/
noncomputable def oppStep (σ : V → ℤˣ) (s : V → Option ℝ) (d : G.Dart) : V → Option ℝ :=
  fun w => if w = d.fst ∨ w = d.snd then
      some (((s d.fst).getD (signVec σ d.fst) + (s d.snd).getD (signVec σ d.snd)) / 2)
    else s w

/-- The opportunistic protocol after the rounds `l`, starting with no node activated. -/
noncomputable def oppRun (σ : V → ℤˣ) (l : List G.Dart) : V → Option ℝ :=
  l.foldl (oppStep G σ) fun _ => none

/-- A uniformly random dart is a uniformly random edge: every edge carries two darts. -/
theorem avg_dart_edge (f : Sym2 V → ℝ) :
    avg (fun d : G.Dart => f d.edge) = avg (fun e : G.edgeSet => f e) := by
  have h1 : ∑ d : G.Dart, f d.edge = 2 * ∑ e ∈ G.edgeFinset, f e := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := G.edgeFinset)
      (g := SimpleGraph.Dart.edge) (fun d _ => by simp), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f e) (fun d hd => by rw [(Finset.mem_filter.mp hd).2]),
      Finset.sum_const, nsmul_eq_mul]
    have := G.dart_edge_fiber_card e (by simpa using he)
    rw [show (univ.filter fun d : G.Dart => d.edge = e) =
      ({d : G.Dart | d.edge = e} : Finset _) from rfl, this]
    norm_num
  have h2 : ∑ e : G.edgeSet, f e = ∑ e ∈ G.edgeFinset, f e := by
    rw [← Finset.sum_coe_sort G.edgeFinset]
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun e => by simp) _ _ fun _ => rfl
  unfold avg
  rw [h1, h2, G.dart_card_eq_twice_card_edges, ← G.edgeFinset_card]
  push_cast
  rcases eq_or_ne (#G.edgeFinset : ℝ) 0 with h | h
  · simp [h]
  · field_simp

omit [Fintype V] [DecidableRel G.Adj] in
lemma oppStep_isSome (σ : V → ℤˣ) (s : V → Option ℝ) (d : G.Dart) (v : V) :
    (oppStep G σ s d v).isSome ↔ (v = d.fst ∨ v = d.snd) ∨ (s v).isSome := by
  unfold oppStep
  split_ifs with h <;> simp [h]

omit [Fintype V] [DecidableRel G.Adj] in
lemma foldl_oppStep_isSome (σ : V → ℤˣ) (l : List G.Dart) (s : V → Option ℝ) (v : V) :
    (l.foldl (oppStep G σ) s v).isSome ↔ (s v).isSome ∨ ∃ d ∈ l, v = d.fst ∨ v = d.snd := by
  induction l generalizing s with
  | nil => simp
  | cons d l ih =>
    rw [List.foldl_cons, ih, oppStep_isSome]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

omit [Fintype V] [DecidableRel G.Adj] in
lemma foldl_oppStep_getD (σ : V → ℤˣ) (l : List G.Dart) (s : V → Option ℝ) (x : V → ℝ)
    (h : ∀ w, (s w).getD (signVec σ w) = x w) (v : V) :
    (l.foldl (oppStep G σ) s v).getD (signVec σ v) = l.foldl (edgeAvg G) x v := by
  induction l generalizing s x with
  | nil => exact h v
  | cons d l ih =>
    apply ih
    intro w
    simp only [oppStep, edgeAvg]
    split_ifs <;> simp [h]

omit [DecidableRel G.Adj] in
/-- One round preserves the sum of the values. -/
lemma sum_edgeAvg (x : V → ℝ) (d : G.Dart) : ∑ v, edgeAvg G x d v = ∑ v, x v := by
  have hne : d.fst ≠ d.snd := d.adj.ne
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add d.fst d.snd hne fun w hw => by simp [edgeAvg, hw.1, hw.2]]
  simp only [edgeAvg, true_or, or_true, if_true]
  ring

section Protocol
omit [Fintype V] [DecidableRel G.Adj]

/-- A node holds a value exactly when it has been an endpoint of an active edge. -/
theorem oppRun_isSome_iff (σ : V → ℤˣ) (l : List G.Dart) (v : V) :
    (oppRun G σ l v).isSome ↔ ∃ d ∈ l, v = d.fst ∨ v = d.snd := by
  simp [oppRun, foldl_oppStep_isSome]

/-- Deferred decisions (Section 3): the opportunistic protocol runs the averaging process from the
initial vector `x⁽⁰⁾ = σ`, a node not activated yet holding its future coin `σ v`. -/
theorem oppRun_getD (σ : V → ℤˣ) (l : List G.Dart) (v : V) :
    (oppRun G σ l v).getD (signVec σ v) = avgRun G (signVec σ) l v :=
  foldl_oppStep_getD G σ l _ _ (fun _ => rfl) v

end Protocol

section Sum
omit [DecidableRel G.Adj]

/-- Every round preserves the sum of the values (`𝟙ᵀ W_t = 𝟙ᵀ`). -/
theorem sum_avgRun (x : V → ℝ) (l : List G.Dart) : ∑ v, avgRun G x l v = ∑ v, x v := by
  induction l generalizing x with
  | nil => rfl
  | cons d l ih =>
    rw [avgRun, List.foldl_cons, ← avgRun, ih, sum_edgeAvg]

end Sum

end Averaging.Opportunistic
