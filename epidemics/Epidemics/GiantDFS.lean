import Epidemics.GiantCoins

/-! # The depth-first search of Krivelevich and Sudakov (EPI-3)

Krivelevich and Sudakov (*The phase transition in random graphs: a simple proof*, Random
Structures & Algorithms 43 (2013), arXiv:1201.6529, Section 2) explore a graph by depth-first
search, maintaining three sets: `S` (exploration complete), `U` (a stack) and `T` (unvisited).
While `U` is non-empty, the algorithm queries the pairs between the last vertex `v` of `U` and the
vertices of `T`; a positive answer for `{v, u}` moves `u` from `T` to `U`, and if no pair is left,
`v` moves to `S`. If `U` is empty, a vertex of `T` is pushed into `U`, starting a new *epoch*
(one per connected component). Once `U = T = ∅`, the remaining pairs are queried (the paper's
completion phase), so that every pair is queried exactly once.

The search is *fed with answers*: `ofAnswers V l` is the state reached with the answers `l` (in
order), stopped just before the next query `pending`. On the edge coins `ω`, the answers are
`queryAnswers (nextQuery e₀) ω t`; the search then explores `perc ⊤ ω`
(`mem_found_iff_of_queryAnswers`), and by the principle of deferred decisions the answers are i.i.d.
Bernoulli(`p`) (`fresh_nextQuery` with `prob_queryAnswers`).

The paper scans `T` along a fixed order `σ`; any deterministic choice works, and we use `pick`.

Structure of the proofs: `State.Inv` is an invariant preserved by every move (`Inv.move`) and
answer (`Inv.answer`); `settle` reaches a state where a query is due (`move_settle`), because the
potential `2 |S| + |U| ≤ 2 |V|` increases with every effective move; a `settle` starts at most one
epoch (`epochs_settle_le`). The extra field `pushes` counts the vertices pushed by positive answers.

The properties of the search used in the paper:
* each query is a new pair (`fresh_nextQuery`, `card_queried_ofAnswers`);
* all pairs between `S` and `T` have been queried and answered negatively
  (`queried_of_mem_done_of_mem_unvisited`);
* `U` spans a path (`stack_chain_ofAnswers`);
* `|U| ≤ 1 + ∑ Xᵢ` and, while `T ≠ ∅`, `|S ∪ U| ≥ ∑ Xᵢ` (`length_stack_le`,
  `count_true_le_card`);
* the vertices found during one epoch lie in one connected component (`reachable_of_mem_comp`).
-/

namespace Epidemics
namespace DFS
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An element of a nonempty finite set: the deterministic choice that replaces the paper's
order `σ`. -/
noncomputable def pick {α : Type*} {s : Finset α} (h : s.Nonempty) : α := Classical.choose h

lemma pick_mem {α : Type*} {s : Finset α} (h : s.Nonempty) : pick h ∈ s := Classical.choose_spec h

/-- A state of the depth-first search (Krivelevich–Sudakov, Section 2). -/
structure State (V : Type*) where
  /-- `S`: the vertices whose exploration is complete. -/
  done : Finset V
  /-- `U`: the stack, last added vertex first. -/
  stack : List V
  /-- The pairs queried so far. -/
  queried : Finset (Sym2 V)
  /-- The pairs whose query was answered positively. -/
  found : Finset (Sym2 V)
  /-- The number of epochs started so far. -/
  epochs : ℕ
  /-- The vertices discovered in the current epoch. -/
  comp : Finset V
  /-- The number of vertices pushed by a positive answer. -/
  pushes : ℕ

namespace State

variable (s : State V)

/-- The initial state: `S = U = ∅`, `T = V`. -/
def init : State V := ⟨∅, [], ∅, ∅, 0, ∅, 0⟩

/-- `T`: the unvisited vertices. -/
def unvisited : Finset V := univ \ (s.done ∪ s.stack.toFinset)

/-- The unvisited vertices `u` such that the pair `{v, u}` has not been queried yet. -/
def candidates (v : V) : Finset V := s.unvisited.filter fun u => s(v, u) ∉ s.queried

/-- The pairs of distinct vertices not queried yet. -/
def unqueried : Finset (Sym2 V) := univ.filter fun e => ¬e.IsDiag ∧ e ∉ s.queried

/-- The exploration is over: `U = T = ∅` (only the completion phase is left). -/
def Finished : Prop := s.stack = [] ∧ s.unvisited = ∅

/-- The pair queried next, if any: `{v, u}` for the last vertex `v` of `U` and a candidate `u`;
once `U = T = ∅`, an unqueried pair (completion phase). `none` if a move without query is due
or every pair has been queried. -/
noncomputable def pending : Option (Sym2 V) :=
  match s.stack with
  | v :: _ => if h : (s.candidates v).Nonempty then some s(v, pick h) else none
  | [] =>
    if s.unvisited.Nonempty then none
    else if h : s.unqueried.Nonempty then some (pick h) else none

/-- A move without query: the last vertex of `U` moves to `S` if it has no candidate left; if `U`
is empty, a vertex of `T` is pushed, starting a new epoch. Otherwise the state is unchanged. -/
noncomputable def move : State V :=
  match s.stack with
  | v :: rest =>
    if (s.candidates v).Nonempty then s else { s with done := insert v s.done, stack := rest }
  | [] =>
    if h : s.unvisited.Nonempty then
      { s with stack := [pick h], epochs := s.epochs + 1, comp := {pick h} }
    else s

/-- Record the answer `b` to the pending query; a positive answer for `{v, u}` (with `v` the last
vertex of `U`) pushes `u`. -/
noncomputable def answer (b : Bool) : State V :=
  match s.stack with
  | v :: _ =>
    if h : (s.candidates v).Nonempty then
      { s with
        queried := insert s(v, pick h) s.queried
        found := if b then insert s(v, pick h) s.found else s.found
        stack := if b then pick h :: s.stack else s.stack
        comp := if b then insert (pick h) s.comp else s.comp
        pushes := if b then s.pushes + 1 else s.pushes }
    else s
  | [] =>
    if s.unvisited.Nonempty then s
    else if h : s.unqueried.Nonempty then
      { s with
        queried := insert (pick h) s.queried
        found := if b then insert (pick h) s.found else s.found }
    else s

/-- Perform the moves without query until a query is due (`2 |V|` moves always suffice, as
`2 |S| + |U| ≤ 2 |V|` increases with each effective move). -/
noncomputable def settle : State V := move^[2 * Fintype.card V] s

/-- The potential `2 |S| + |U|`, increased by every effective move. -/
def potential : ℕ := 2 * s.done.card + s.stack.length

variable {s}

@[simp] lemma mem_unvisited {x : V} : x ∈ s.unvisited ↔ x ∉ s.done ∧ x ∉ s.stack := by
  simp [unvisited]

lemma mem_candidates {v u : V} : u ∈ s.candidates v ↔ u ∈ s.unvisited ∧ s(v, u) ∉ s.queried := by
  simp [candidates]

lemma mem_unqueried {e : Sym2 V} : e ∈ s.unqueried ↔ ¬e.IsDiag ∧ e ∉ s.queried := by
  simp [unqueried]

/-! #### The cases of `move`, `answer` and `pending` -/

lemma move_cons_pos {v : V} {rest : List V} (hs : s.stack = v :: rest)
    (h : (s.candidates v).Nonempty) : s.move = s := by
  simp [move, hs, h]

lemma move_cons_neg {v : V} {rest : List V} (hs : s.stack = v :: rest)
    (h : ¬(s.candidates v).Nonempty) :
    s.move = { s with done := insert v s.done, stack := rest } := by
  simp [move, hs, h]

lemma move_nil_pos (hs : s.stack = []) (h : s.unvisited.Nonempty) :
    s.move = { s with stack := [pick h], epochs := s.epochs + 1, comp := {pick h} } := by
  simp [move, hs, h]

lemma move_nil_neg (hs : s.stack = []) (h : ¬s.unvisited.Nonempty) : s.move = s := by
  simp [move, hs, h]

lemma answer_cons_pos {v : V} {rest : List V} (hs : s.stack = v :: rest)
    (h : (s.candidates v).Nonempty) (b : Bool) :
    s.answer b = { s with
      queried := insert s(v, pick h) s.queried
      found := if b then insert s(v, pick h) s.found else s.found
      stack := if b then pick h :: s.stack else s.stack
      comp := if b then insert (pick h) s.comp else s.comp
      pushes := if b then s.pushes + 1 else s.pushes } := by
  simp [answer, hs, h]

lemma answer_cons_neg {v : V} {rest : List V} (hs : s.stack = v :: rest)
    (h : ¬(s.candidates v).Nonempty) (b : Bool) : s.answer b = s := by
  simp [answer, hs, h]

lemma answer_nil_pos (hs : s.stack = []) (h : s.unvisited.Nonempty) (b : Bool) :
    s.answer b = s := by
  simp [answer, hs, h]

lemma answer_nil_pad (hs : s.stack = []) (hT : ¬s.unvisited.Nonempty)
    (h : s.unqueried.Nonempty) (b : Bool) :
    s.answer b = { s with
      queried := insert (pick h) s.queried
      found := if b then insert (pick h) s.found else s.found } := by
  simp [answer, hs, hT, h]

lemma answer_nil_none (hs : s.stack = []) (hT : ¬s.unvisited.Nonempty)
    (h : ¬s.unqueried.Nonempty) (b : Bool) : s.answer b = s := by
  simp [answer, hs, hT, h]

lemma pending_cons_pos {v : V} {rest : List V} (hs : s.stack = v :: rest)
    (h : (s.candidates v).Nonempty) : s.pending = some s(v, pick h) := by
  simp [pending, hs, h]

lemma pending_cons_neg {v : V} {rest : List V} (hs : s.stack = v :: rest)
    (h : ¬(s.candidates v).Nonempty) : s.pending = none := by
  simp [pending, hs, h]

lemma pending_nil_pos (hs : s.stack = []) (h : s.unvisited.Nonempty) : s.pending = none := by
  simp [pending, hs, h]

lemma pending_nil_pad (hs : s.stack = []) (hT : ¬s.unvisited.Nonempty)
    (h : s.unqueried.Nonempty) : s.pending = some (pick h) := by
  simp [pending, hs, hT, h]

lemma pending_nil_none (hs : s.stack = []) (hT : ¬s.unvisited.Nonempty)
    (h : ¬s.unqueried.Nonempty) : s.pending = none := by
  simp [pending, hs, hT, h]

/-! #### The invariant -/

/-- The invariant of the search (Krivelevich–Sudakov, Section 2, and the bookkeeping of epochs). -/
structure Inv (s : State V) : Prop where
  disj : Disjoint s.done s.stack.toFinset
  nodup : s.stack.Nodup
  chain : s.stack.IsChain fun u v => s(u, v) ∈ s.found
  done_unvisited : ∀ a ∈ s.done, ∀ b ∈ s.unvisited, s(a, b) ∈ s.queried
  found_unvisited : ∀ e ∈ s.found, ∀ x ∈ e, x ∉ s.unvisited
  found_queried : s.found ⊆ s.queried
  not_diag : ∀ e ∈ s.queried, ¬e.IsDiag
  queried_unvisited : ∀ e ∈ s.queried, ∃ x ∈ e, x ∉ s.unvisited
  comp_sub : s.comp ⊆ s.done ∪ s.stack.toFinset
  stack_comp : ∀ v ∈ s.stack, v ∈ s.comp
  comp_conn : ∀ u ∈ s.comp, ∀ v ∈ s.comp,
    (SimpleGraph.fromEdgeSet (s.found : Set (Sym2 V))).Reachable u v
  base : ∀ a ∈ (s.done ∪ s.stack.toFinset) \ s.comp,
    ∀ c ∉ (s.done ∪ s.stack.toFinset) \ s.comp, s(a, c) ∈ s.queried
  card_eq : (s.done ∪ s.stack.toFinset).card = s.pushes + s.epochs
  card_comp : s.comp.card ≤ s.pushes + 1
  pushes_le : s.pushes ≤ s.found.card
  pushes_eq : ¬s.Finished → s.found.card = s.pushes

lemma inv_init : (init : State V).Inv where
  disj := by simp [init]
  nodup := by simp [init]
  chain := by simp [init]
  done_unvisited := by simp [init]
  found_unvisited := by simp [init]
  found_queried := by simp [init]
  not_diag := by simp [init]
  queried_unvisited := by simp [init]
  comp_sub := by simp [init]
  stack_comp := by simp [init]
  comp_conn := by simp [init]
  base := by simp [init]
  card_eq := by simp [init]
  card_comp := by simp [init]
  pushes_le := by simp [init]
  pushes_eq := by simp [init]

omit [Fintype V] [DecidableEq V] in
lemma reachable_mono {F F' : Finset (Sym2 V)} (h : F ⊆ F') {u v : V}
    (huv : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v) :
    (SimpleGraph.fromEdgeSet (F' : Set (Sym2 V))).Reachable u v :=
  huv.mono (SimpleGraph.fromEdgeSet_mono (by simpa using h))

/-- Root push. -/
lemma Inv.move_nil_pos (hs : s.Inv) (hst : s.stack = []) (hT : s.unvisited.Nonempty) :
    ({ s with stack := [pick hT], epochs := s.epochs + 1, comp := {pick hT} } : State V).Inv := by
  have hr := pick_mem hT
  set r := pick hT
  have hrd : r ∉ s.done := by simpa [hst] using hr
  have hunv (x : V) :
      x ∈ ({ s with stack := [r], epochs := s.epochs + 1, comp := {r} } : State V).unvisited ↔
        x ∈ s.unvisited ∧ x ≠ r := by
    simp [hst]
  have hnotfin : ¬s.Finished := fun h => by simp [h.2] at hT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hrd
  · simp
  · simp
  · intro a ha b hb
    exact hs.done_unvisited a ha b ((hunv b).mp hb).1
  · intro e he x hx hxu
    exact hs.found_unvisited e he x hx ((hunv x).mp hxu).1
  · exact hs.found_queried
  · exact hs.not_diag
  · intro e he
    obtain ⟨x, hx, hxu⟩ := hs.queried_unvisited e he
    exact ⟨x, hx, fun h => hxu ((hunv x).mp h).1⟩
  · simp
  · simp
  · intro u hu v hv
    simp only [mem_singleton] at hu hv
    subst hu hv
    rfl
  · intro a ha c hc
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty, mem_sdiff, mem_union,
      mem_singleton] at ha hc
    have had : a ∈ s.done := ha.1.resolve_right ha.2
    have hcd : c ∉ s.done := by
      intro h
      have hcr : c = r := by
        by_contra hne
        exact hc ⟨Or.inl h, hne⟩
      exact hrd (hcr ▸ h)
    exact hs.done_unvisited a had c (by simp [hst, hcd])
  · have h0 := hs.card_eq
    rw [hst] at h0
    simp only [List.toFinset_nil, union_empty] at h0
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty]
    rw [union_comm, ← insert_eq, card_insert_of_notMem hrd, h0]
    ring
  · simp
  · exact hs.pushes_le
  · intro _
    exact hs.pushes_eq hnotfin

lemma not_finished_of_cons {v : V} {rest : List V} (hst : s.stack = v :: rest) : ¬s.Finished :=
  fun h => List.cons_ne_nil v rest (hst ▸ h.1)

/-- Pop: the last vertex of `U` moves to `S`. -/
lemma Inv.move_cons_neg (hs : s.Inv) {v : V} {rest : List V} (hst : s.stack = v :: rest)
    (hc : ¬(s.candidates v).Nonempty) :
    ({ s with done := insert v s.done, stack := rest } : State V).Inv := by
  have hnd := hs.nodup
  have hdj := hs.disj
  rw [hst] at hnd hdj
  rw [List.toFinset_cons, disjoint_insert_right] at hdj
  rw [List.nodup_cons] at hnd
  have hvr : v ∉ rest.toFinset := by simpa using hnd.1
  have hset : insert v s.done ∪ rest.toFinset = s.done ∪ s.stack.toFinset := by
    rw [hst]; ext x; simp
  have hunv (x : V) :
      x ∈ ({ s with done := insert v s.done, stack := rest } : State V).unvisited ↔
        x ∈ s.unvisited := by
    simp [hst]
    tauto
  have hcand : ∀ b ∈ s.unvisited, s(v, b) ∈ s.queried := by
    intro b hb
    by_contra hq
    exact hc ⟨b, mem_candidates.mpr ⟨hb, hq⟩⟩
  refine ⟨?_, hnd.2, ?_, ?_, ?_, hs.found_queried, hs.not_diag, ?_, ?_, ?_, hs.comp_conn,
    ?_, ?_, hs.card_comp, hs.pushes_le, fun _ => hs.pushes_eq (not_finished_of_cons hst)⟩
  · exact disjoint_insert_left.mpr ⟨hvr, hdj.2⟩
  · have := hs.chain
    rw [hst] at this
    exact this.tail
  · intro a ha b hb
    rcases mem_insert.mp ha with rfl | ha
    · exact hcand b ((hunv b).mp hb)
    · exact hs.done_unvisited a ha b ((hunv b).mp hb)
  · intro e he x hx hxu
    exact hs.found_unvisited e he x hx ((hunv x).mp hxu)
  · intro e he
    obtain ⟨x, hx, hxu⟩ := hs.queried_unvisited e he
    exact ⟨x, hx, fun h => hxu ((hunv x).mp h)⟩
  · show s.comp ⊆ insert v s.done ∪ rest.toFinset
    rw [hset]; exact hs.comp_sub
  · intro w hw
    exact hs.stack_comp w (by rw [hst]; exact List.mem_cons_of_mem v hw)
  · show ∀ a ∈ (insert v s.done ∪ rest.toFinset) \ s.comp,
      ∀ c ∉ (insert v s.done ∪ rest.toFinset) \ s.comp, s(a, c) ∈ s.queried
    rw [hset]; exact hs.base
  · show (insert v s.done ∪ rest.toFinset).card = s.pushes + s.epochs
    rw [hset]; exact hs.card_eq

/-- A negative answer to a query of the search. -/
lemma Inv.answer_cons_false (hs : s.Inv) {v : V} {rest : List V} (hst : s.stack = v :: rest)
    (hc : (s.candidates v).Nonempty) :
    ({ s with queried := insert s(v, pick hc) s.queried } : State V).Inv := by
  have hu := mem_candidates.mp (pick_mem hc)
  set u := pick hc
  have hvs : v ∈ s.stack := by rw [hst]; exact List.mem_cons_self
  have hvu : v ≠ u := fun h => (mem_unvisited.mp hu.1).2 (h ▸ hvs)
  have hvT : v ∉ s.unvisited := fun h => (mem_unvisited.mp h).2 hvs
  refine ⟨hs.disj, hs.nodup, hs.chain, ?_, hs.found_unvisited, ?_, ?_, ?_, hs.comp_sub,
    hs.stack_comp, hs.comp_conn, ?_, hs.card_eq, hs.card_comp, hs.pushes_le,
    fun _ => hs.pushes_eq (not_finished_of_cons hst)⟩
  · intro a ha b hb
    exact mem_insert_of_mem (hs.done_unvisited a ha b hb)
  · exact hs.found_queried.trans (subset_insert _ _)
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · simpa [Sym2.mk_isDiag_iff] using hvu
    · exact hs.not_diag e he
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact ⟨v, Sym2.mem_mk_left v u, hvT⟩
    · exact hs.queried_unvisited e he
  · intro a ha c hc'
    exact mem_insert_of_mem (hs.base a ha c hc')

/-- A positive answer to a query of the search: `u` is pushed. -/
lemma Inv.answer_cons_true (hs : s.Inv) {v : V} {rest : List V} (hst : s.stack = v :: rest)
    (hc : (s.candidates v).Nonempty) :
    ({ s with
      queried := insert s(v, pick hc) s.queried
      found := insert s(v, pick hc) s.found
      stack := pick hc :: s.stack
      comp := insert (pick hc) s.comp
      pushes := s.pushes + 1 } : State V).Inv := by
  have hu := mem_candidates.mp (pick_mem hc)
  set u := pick hc
  have hvs : v ∈ s.stack := by rw [hst]; exact List.mem_cons_self
  have huT := mem_unvisited.mp hu.1
  have hvu : v ≠ u := fun h => huT.2 (h ▸ hvs)
  have hvT : v ∉ s.unvisited := fun h => (mem_unvisited.mp h).2 hvs
  have hus : u ∉ s.done ∪ s.stack.toFinset := by simpa using huT
  have hef : s(v, u) ∉ s.found := fun h => hu.2 (hs.found_queried h)
  have hunv (x : V) :
      x ∈ ({ s with
        queried := insert s(v, u) s.queried
        found := insert s(v, u) s.found
        stack := u :: s.stack
        comp := insert u s.comp
        pushes := s.pushes + 1 } : State V).unvisited ↔ x ∈ s.unvisited ∧ x ≠ u := by
    simp
    tauto
  have hsub : ∀ x, x ∈ ({ s with
        queried := insert s(v, u) s.queried
        found := insert s(v, u) s.found
        stack := u :: s.stack
        comp := insert u s.comp
        pushes := s.pushes + 1 } : State V).unvisited → x ∈ s.unvisited :=
    fun x hx => ((hunv x).mp hx).1
  have hset : s.done ∪ (u :: s.stack).toFinset = insert u (s.done ∪ s.stack.toFinset) := by
    ext x; simp
  have hD : (s.done ∪ (u :: s.stack).toFinset) \ insert u s.comp =
      (s.done ∪ s.stack.toFinset) \ s.comp := by
    rw [hset]; ext x; simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 (fun h => h2 (Or.inl h))
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_⟩
      rintro (rfl | h)
      · exact hus h1
      · exact h2 h
  have hadj : (SimpleGraph.fromEdgeSet ((insert s(v, u) s.found : Finset (Sym2 V)) :
      Set (Sym2 V))).Adj v u := by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by simp, hvu⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Disjoint s.done (u :: s.stack).toFinset
    rw [List.toFinset_cons, disjoint_insert_right]
    exact ⟨huT.1, hs.disj⟩
  · exact List.nodup_cons.mpr ⟨huT.2, hs.nodup⟩
  · show (u :: s.stack).IsChain fun a b => s(a, b) ∈ insert s(v, u) s.found
    have hch := hs.chain.imp (S := fun a b => s(a, b) ∈ insert s(v, u) s.found)
      fun a b h => mem_insert_of_mem h
    rw [hst] at hch ⊢
    exact List.IsChain.cons_cons (by rw [Sym2.eq_swap]; exact mem_insert_self _ _) hch
  · intro a ha b hb
    exact mem_insert_of_mem (hs.done_unvisited a ha b (hsub b hb))
  · intro e he x hx hxu
    rcases mem_insert.mp he with rfl | he
    · rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hvT (hsub _ hxu)
      · exact ((hunv _).mp hxu).2 rfl
    · exact hs.found_unvisited e he x hx (hsub x hxu)
  · exact insert_subset_insert _ hs.found_queried
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · simpa [Sym2.mk_isDiag_iff] using hvu
    · exact hs.not_diag e he
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact ⟨v, Sym2.mem_mk_left v u, fun h => hvT (hsub v h)⟩
    · obtain ⟨x, hx, hxu⟩ := hs.queried_unvisited e he
      exact ⟨x, hx, fun h => hxu (hsub x h)⟩
  · show insert u s.comp ⊆ s.done ∪ (u :: s.stack).toFinset
    rw [hset]
    exact insert_subset_insert _ hs.comp_sub
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (hs.stack_comp w hw)
  · have hvc : v ∈ s.comp := hs.stack_comp v hvs
    have hreach (w : V) (hw : w ∈ s.comp) : (SimpleGraph.fromEdgeSet
        ((insert s(v, u) s.found : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u w :=
      hadj.symm.reachable.trans (reachable_mono (subset_insert _ _) (hs.comp_conn v hvc w hw))
    intro a ha c hc'
    rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hc' with rfl | hc'
    · rfl
    · exact hreach c hc'
    · exact (hreach a ha).symm
    · exact reachable_mono (subset_insert _ _) (hs.comp_conn a ha c hc')
  · show ∀ a ∈ (s.done ∪ (u :: s.stack).toFinset) \ insert u s.comp,
      ∀ c ∉ (s.done ∪ (u :: s.stack).toFinset) \ insert u s.comp, s(a, c) ∈ insert s(v, u) s.queried
    rw [hD]
    intro a ha c hc'
    exact mem_insert_of_mem (hs.base a ha c hc')
  · show (s.done ∪ (u :: s.stack).toFinset).card = s.pushes + 1 + s.epochs
    rw [hset, card_insert_of_notMem hus, hs.card_eq]
    ring
  · show (insert u s.comp).card ≤ s.pushes + 1 + 1
    exact (card_insert_le _ _).trans (by have := hs.card_comp; omega)
  · show s.pushes + 1 ≤ (insert s(v, u) s.found).card
    rw [card_insert_of_notMem hef]
    exact Nat.succ_le_succ hs.pushes_le
  · intro _
    show (insert s(v, u) s.found).card = s.pushes + 1
    rw [card_insert_of_notMem hef, hs.pushes_eq (not_finished_of_cons hst)]

/-- A query of the completion phase. -/
lemma Inv.answer_pad (hs : s.Inv) (hst : s.stack = []) (hT : ¬s.unvisited.Nonempty)
    (hq : s.unqueried.Nonempty) (b : Bool) :
    ({ s with
      queried := insert (pick hq) s.queried
      found := if b then insert (pick hq) s.found else s.found } : State V).Inv := by
  have he := mem_unqueried.mp (pick_mem hq)
  have hT' : s.unvisited = ∅ := not_nonempty_iff_eq_empty.mp hT
  have hfin (t : State V) (ht : t.unvisited = s.unvisited) (x : V) : x ∉ t.unvisited := by
    rw [ht, hT']; exact notMem_empty x
  have hunv : ({ s with
      queried := insert (pick hq) s.queried
      found := if b then insert (pick hq) s.found else s.found } : State V).unvisited =
        s.unvisited := rfl
  have hff : s.found ⊆ (if b then insert (pick hq) s.found else s.found) := by
    split_ifs
    · exact subset_insert _ _
    · exact Subset.refl _
  refine ⟨hs.disj, hs.nodup, ?_, ?_, ?_, ?_, ?_, ?_, hs.comp_sub, hs.stack_comp, ?_, ?_,
    hs.card_eq, hs.card_comp, ?_, ?_⟩
  · simp [hst]
  · intro a _ b hb; exact absurd hb (hfin _ hunv b)
  · intro e _ x _ hx; exact hfin _ hunv x hx
  · split_ifs
    · exact insert_subset_insert _ hs.found_queried
    · exact hs.found_queried.trans (subset_insert _ _)
  · intro e he'
    rcases mem_insert.mp he' with rfl | he'
    · exact he.1
    · exact hs.not_diag e he'
  · intro e _
    induction e using Sym2.ind with
    | h x y => exact ⟨x, Sym2.mem_mk_left x y, hfin _ hunv x⟩
  · intro u hu w hw
    exact reachable_mono hff (hs.comp_conn u hu w hw)
  · intro a ha c hc
    exact mem_insert_of_mem (hs.base a ha c hc)
  · exact hs.pushes_le.trans (card_le_card hff)
  · intro hnf
    exact absurd ⟨hst, hT'⟩ hnf

theorem Inv.move (hs : s.Inv) : s.move.Inv := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [State.move_nil_pos hst hT]; exact hs.move_nil_pos hst hT
    · rw [State.move_nil_neg hst hT]; exact hs
  · by_cases hc : (s.candidates v).Nonempty
    · rw [State.move_cons_pos hst hc]; exact hs
    · rw [State.move_cons_neg hst hc]; exact hs.move_cons_neg hst hc

theorem Inv.answer (hs : s.Inv) (b : Bool) : (s.answer b).Inv := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [answer_nil_pos hst hT]; exact hs
    · by_cases hq : s.unqueried.Nonempty
      · rw [answer_nil_pad hst hT hq]; exact hs.answer_pad hst hT hq b
      · rw [answer_nil_none hst hT hq]; exact hs
  · by_cases hc : (s.candidates v).Nonempty
    · rw [answer_cons_pos hst hc]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hs.answer_cons_false hst hc
      · simp only [↓reduceIte]
        exact hs.answer_cons_true hst hc
    · rw [answer_cons_neg hst hc]; exact hs

theorem Inv.iterate_move (hs : s.Inv) (k : ℕ) : (State.move^[k] s).Inv := by
  induction k with
  | zero => exact hs
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.move

theorem Inv.settle (hs : s.Inv) : s.settle.Inv := hs.iterate_move _

/-! #### Frame lemmas -/

lemma move_frame : s.move.queried = s.queried ∧ s.move.found = s.found ∧
    s.move.pushes = s.pushes := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [move_nil_pos hst hT]; exact ⟨rfl, rfl, rfl⟩
    · rw [move_nil_neg hst hT]; exact ⟨rfl, rfl, rfl⟩
  · by_cases hc : (s.candidates v).Nonempty
    · rw [move_cons_pos hst hc]; exact ⟨rfl, rfl, rfl⟩
    · rw [move_cons_neg hst hc]; exact ⟨rfl, rfl, rfl⟩

lemma iterate_move_frame (k : ℕ) : (move^[k] s).queried = s.queried ∧
    (move^[k] s).found = s.found ∧ (move^[k] s).pushes = s.pushes := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, h3⟩ := (move^[k] s).move_frame
    exact ⟨h1.trans ih.1, h2.trans ih.2.1, h3.trans ih.2.2⟩

lemma settle_queried : s.settle.queried = s.queried := (iterate_move_frame _).1
lemma settle_found : s.settle.found = s.found := (iterate_move_frame _).2.1
lemma settle_pushes : s.settle.pushes = s.pushes := (iterate_move_frame _).2.2

/-- A move either keeps the epoch (and its vertices) or starts a new one with a single vertex. -/
lemma move_epochs_comp : (s.move.epochs = s.epochs ∧ s.move.comp = s.comp) ∨
    (s.move.epochs = s.epochs + 1 ∧ ∃ x, s.move.comp = {x}) := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [move_nil_pos hst hT]; exact Or.inr ⟨rfl, _, rfl⟩
    · rw [move_nil_neg hst hT]; exact Or.inl ⟨rfl, rfl⟩
  · by_cases hc : (s.candidates v).Nonempty
    · rw [move_cons_pos hst hc]; exact Or.inl ⟨rfl, rfl⟩
    · rw [move_cons_neg hst hc]; exact Or.inl ⟨rfl, rfl⟩

lemma answer_epochs (b : Bool) : (s.answer b).epochs = s.epochs := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [answer_nil_pos hst hT]
    · by_cases hq : s.unqueried.Nonempty
      · rw [answer_nil_pad hst hT hq]
      · rw [answer_nil_none hst hT hq]
  · by_cases hc : (s.candidates v).Nonempty
    · rw [answer_cons_pos hst hc]
    · rw [answer_cons_neg hst hc]

/-- The answer to the pending query, if any, adds that pair to the queried ones (and to the found
ones if positive); without pending query, the answer changes nothing. -/
lemma pending_answer (b : Bool) : (s.pending = none ∧ s.answer b = s) ∨
    ∃ e, s.pending = some e ∧ e ∉ s.queried ∧ (s.answer b).queried = insert e s.queried ∧
      (s.answer b).found = (if b then insert e s.found else s.found) := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · exact Or.inl ⟨pending_nil_pos hst hT, answer_nil_pos hst hT b⟩
    · by_cases hq : s.unqueried.Nonempty
      · rw [answer_nil_pad hst hT hq]
        exact Or.inr ⟨_, pending_nil_pad hst hT hq, (mem_unqueried.mp (pick_mem hq)).2, rfl, rfl⟩
      · exact Or.inl ⟨pending_nil_none hst hT hq, answer_nil_none hst hT hq b⟩
  · by_cases hc : (s.candidates v).Nonempty
    · rw [answer_cons_pos hst hc]
      exact Or.inr ⟨_, pending_cons_pos hst hc, (mem_candidates.mp (pick_mem hc)).2, rfl, rfl⟩
    · exact Or.inl ⟨pending_cons_neg hst hc, answer_cons_neg hst hc b⟩

/-! #### Monotonicity -/

/-- `t` extends `s`: more pairs queried and found, `S` and `S ∪ U` larger (so `T` smaller), more
epochs and pushes. -/
structure Le (s t : State V) : Prop where
  queried : s.queried ⊆ t.queried
  found : s.found ⊆ t.found
  done : s.done ⊆ t.done
  unvisited : t.unvisited ⊆ s.unvisited
  epochs : s.epochs ≤ t.epochs
  pushes : s.pushes ≤ t.pushes

lemma Le.refl (s : State V) : s.Le s :=
  ⟨Subset.refl _, Subset.refl _, Subset.refl _, Subset.refl _, le_rfl, le_rfl⟩

lemma Le.trans {s t u : State V} (h₁ : s.Le t) (h₂ : t.Le u) : s.Le u :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2, h₁.3.trans h₂.3, h₂.4.trans h₁.4, h₁.5.trans h₂.5,
    h₁.6.trans h₂.6⟩

lemma le_move (s : State V) : s.Le s.move := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [move_nil_pos hst hT]
      refine ⟨Subset.refl _, Subset.refl _, Subset.refl _, fun x hx => ?_, Nat.le_succ _,
        le_rfl⟩
      simp only [mem_unvisited] at hx ⊢
      exact ⟨hx.1, by simp [hst]⟩
    · rw [move_nil_neg hst hT]; exact Le.refl s
  · by_cases hc : (s.candidates v).Nonempty
    · rw [move_cons_pos hst hc]; exact Le.refl s
    · rw [move_cons_neg hst hc]
      refine ⟨Subset.refl _, Subset.refl _, subset_insert _ _, fun x hx => ?_, le_rfl, le_rfl⟩
      simp only [mem_unvisited, mem_insert, not_or, hst, List.mem_cons] at hx ⊢
      tauto

lemma le_answer (s : State V) (b : Bool) : s.Le (s.answer b) := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [answer_nil_pos hst hT]; exact Le.refl s
    · by_cases hq : s.unqueried.Nonempty
      · rw [answer_nil_pad hst hT hq]
        refine ⟨subset_insert _ _, ?_, Subset.refl _, Subset.refl _, le_rfl, le_rfl⟩
        split_ifs
        · exact subset_insert _ _
        · exact Subset.refl _
      · rw [answer_nil_none hst hT hq]; exact Le.refl s
  · by_cases hc : (s.candidates v).Nonempty
    · rw [answer_cons_pos hst hc]
      cases b
      · exact ⟨subset_insert _ _, Subset.refl _, Subset.refl _, Subset.refl _, le_rfl, le_rfl⟩
      · refine ⟨subset_insert _ _, subset_insert _ _, Subset.refl _, fun x hx => ?_, le_rfl,
          Nat.le_succ _⟩
        simp only [mem_unvisited, if_true, List.mem_cons, not_or] at hx ⊢
        exact ⟨hx.1, hx.2.2⟩
    · rw [answer_cons_neg hst hc]; exact Le.refl s

lemma le_iterate_move (s : State V) (k : ℕ) : s.Le (move^[k] s) := by
  induction k with
  | zero => exact Le.refl s
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (le_move _)

lemma le_settle (s : State V) : s.Le s.settle := le_iterate_move s _

/-! #### Termination of `settle` -/

lemma potential_move (hs : s.Inv) : s.move = s ∨ s.move.potential = s.potential + 1 := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [move_nil_pos hst hT]
      right
      simp [potential, hst]
    · rw [move_nil_neg hst hT]; exact Or.inl rfl
  · by_cases hc : (s.candidates v).Nonempty
    · rw [move_cons_pos hst hc]; exact Or.inl rfl
    · rw [move_cons_neg hst hc]
      right
      have hvd : v ∉ s.done := by
        have := hs.disj
        rw [hst, List.toFinset_cons, disjoint_insert_right] at this
        exact this.1
      simp only [potential, hst, List.length_cons, card_insert_of_notMem hvd]
      ring

lemma potential_le (hs : s.Inv) : s.potential ≤ 2 * Fintype.card V := by
  have h1 : s.stack.length = s.stack.toFinset.card := (List.toFinset_card_of_nodup hs.nodup).symm
  have h2 := card_union_of_disjoint hs.disj
  have h3 := card_le_univ (s.done ∪ s.stack.toFinset)
  simp only [potential]
  omega

/-- After `settle`, no move without query is due. -/
theorem move_settle (hs : s.Inv) : s.settle.move = s.settle := by
  have key : ∀ k, (move^[k] s).move ≠ move^[k] s → s.potential + k ≤ (move^[k] s).potential := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hne
      rw [Function.iterate_succ_apply'] at hne ⊢
      have hne' : (move^[k] s).move ≠ move^[k] s := fun h => hne (by rw [h, h])
      have := ih hne'
      rcases potential_move (hs.iterate_move k) with h | h
      · exact absurd h hne'
      · rw [h]; omega
  by_contra hne
  have h1 := key _ hne
  have h2 := potential_le hs.settle.move
  rcases potential_move hs.settle with h | h
  · exact hne h
  · have : s.settle.potential = (move^[2 * Fintype.card V] s).potential := rfl
    omega

/-- A state where no move is due is either at a query of the search or finished. -/
lemma exists_cons_of_move_eq (hfix : s.move = s) (hnf : ¬s.Finished) :
    ∃ v rest, s.stack = v :: rest ∧ (s.candidates v).Nonempty := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [move_nil_pos hst hT] at hfix
      have := congrArg State.stack hfix
      simp [hst] at this
    · exact absurd ⟨hst, not_nonempty_iff_eq_empty.mp hT⟩ hnf
  · by_cases hc : (s.candidates v).Nonempty
    · exact ⟨v, rest, rfl, hc⟩
    · rw [move_cons_neg hst hc] at hfix
      have := congrArg State.stack hfix
      simp [hst] at this

lemma move_of_finished (h : s.Finished) : s.move = s :=
  move_nil_neg h.1 (not_nonempty_iff_eq_empty.mpr h.2)

lemma settle_of_finished (h : s.Finished) : s.settle = s := by
  have : ∀ k, move^[k] s = s := fun k => Function.iterate_fixed (move_of_finished h) k
  exact this _

lemma answer_finished (h : s.Finished) (b : Bool) : (s.answer b).Finished := by
  have hT : ¬s.unvisited.Nonempty := by rw [h.2]; simp
  by_cases hq : s.unqueried.Nonempty
  · rw [answer_nil_pad h.1 hT hq]; exact h
  · rw [answer_nil_none h.1 hT hq]; exact h

/-! #### Epochs within one `settle` -/

lemma move_of_not_root (h : ¬(s.stack = [] ∧ s.unvisited.Nonempty)) :
    s.move.epochs = s.epochs ∧ s.move.comp = s.comp := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · exact absurd ⟨hst, hT⟩ h
    · rw [move_nil_neg hst hT]; exact ⟨rfl, rfl⟩
  · by_cases hc : (s.candidates v).Nonempty
    · rw [move_cons_pos hst hc]; exact ⟨rfl, rfl⟩
    · rw [move_cons_neg hst hc]; exact ⟨rfl, rfl⟩

/-- After a new epoch starts, `settle` starts no other one: either the new root has a candidate
(pairs inside `T` are never queried), or it was the last unvisited vertex. -/
lemma epochs_iterate_after_root (hs : s.Inv) (hst : s.stack = []) (hT : s.unvisited.Nonempty)
    (m : ℕ) : (move^[m] s.move).epochs = s.move.epochs := by
  have hr := pick_mem hT
  set r := pick hT
  have hrd : r ∉ s.done := by simpa [hst] using hr
  set t := s.move with ht
  rw [move_nil_pos hst hT] at ht
  have htst : t.stack = [r] := by rw [ht]
  by_cases hT' : (s.unvisited.erase r).Nonempty
  · obtain ⟨u, hu⟩ := hT'
    have huT := mem_erase.mp hu
    have hc : (t.candidates r).Nonempty := by
      refine ⟨u, mem_candidates.mpr ⟨?_, ?_⟩⟩
      · rw [ht]
        simp only [mem_unvisited, List.mem_singleton]
        exact ⟨(mem_unvisited.mp huT.2).1, huT.1⟩
      · rw [ht]
        intro hq
        obtain ⟨x, hx, hxu⟩ := hs.queried_unvisited _ hq
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hxu hr
        · exact hxu huT.2
    rw [Function.iterate_fixed (move_cons_pos htst hc)]
  · have hc : ¬(t.candidates r).Nonempty := by
      rintro ⟨u, hu⟩
      have hu' := (mem_candidates.mp hu).1
      rw [ht] at hu'
      simp only [mem_unvisited, List.mem_singleton] at hu'
      exact hT' ⟨u, mem_erase.mpr ⟨hu'.2, by simp [hst, hu'.1]⟩⟩
    have hmove : t.move = { t with done := insert r t.done, stack := [] } := move_cons_neg htst hc
    have hfin : t.move.Finished := by
      rw [hmove]
      refine ⟨rfl, eq_empty_of_forall_notMem fun x hx => ?_⟩
      simp only [mem_unvisited, mem_insert, not_or, List.not_mem_nil, not_false_eq_true,
        and_true] at hx
      have hxd : x ∉ s.done := by rw [ht] at hx; exact hx.2
      have hxr : x ≠ r := hx.1
      exact hT' ⟨x, mem_erase.mpr ⟨hxr, by simp [hst, hxd]⟩⟩
    cases m with
    | zero => rfl
    | succ m =>
      rw [Function.iterate_succ_apply, Function.iterate_fixed (move_of_finished hfin), hmove]

/-- `settle` starts at most one epoch. -/
lemma epochs_settle_le (hs : s.Inv) : s.settle.epochs ≤ s.epochs + 1 := by
  have key : ∀ k, (move^[k] s).epochs = s.epochs ∨ ((move^[k] s).epochs = s.epochs + 1 ∧
      ∀ m, (move^[m] (move^[k] s)).epochs = (move^[k] s).epochs) := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have ht : (move^[k] s).Inv := hs.iterate_move k
      rcases ih with h | ⟨h, hroot⟩
      · by_cases hr : (move^[k] s).stack = [] ∧ (move^[k] s).unvisited.Nonempty
        · refine Or.inr ⟨?_, epochs_iterate_after_root ht hr.1 hr.2⟩
          rw [move_nil_pos hr.1 hr.2, ← h]
        · exact Or.inl ((move_of_not_root hr).1.trans h)
      · have h1 : (move^[k] s).move.epochs = (move^[k] s).epochs := hroot 1
        refine Or.inr ⟨h1.trans h, fun m => ?_⟩
        rw [← Function.iterate_succ_apply, hroot (m + 1), h1]
  rcases key (2 * Fintype.card V) with h | h
  · exact h.le.trans (Nat.le_succ _)
  · exact h.1.le

/-- If `settle` starts no epoch, the current epoch keeps its vertices. -/
lemma comp_settle_of_epochs_eq (h : s.settle.epochs = s.epochs) : s.settle.comp = s.comp := by
  have key : ∀ k, (move^[k] s).epochs = s.epochs → (move^[k] s).comp = s.comp := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply'] at hk ⊢
      have h1 := (le_iterate_move s k).epochs
      have h2 := (le_move (move^[k] s)).epochs
      rcases (move^[k] s).move_epochs_comp with h' | h'
      · rw [h'.2]; exact ih (by omega)
      · omega
  exact key _ h

/-- If `settle` starts an epoch, the current epoch has a single vertex. -/
lemma comp_settle_of_lt (h : s.epochs < s.settle.epochs) : ∃ x, s.settle.comp = {x} := by
  have key : ∀ k, s.epochs < (move^[k] s).epochs → ∃ x, (move^[k] s).comp = {x} := by
    intro k
    induction k with
    | zero => intro hk; exact absurd hk (lt_irrefl _)
    | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply'] at hk ⊢
      rcases (move^[k] s).move_epochs_comp with h' | h'
      · rw [h'.2]; exact ih (by omega)
      · exact h'.2
  exact key _ h

lemma answer_pushes_le (b : Bool) : (s.answer b).pushes ≤ s.pushes + 1 := by
  rcases hst : s.stack with _ | ⟨v, rest⟩
  · by_cases hT : s.unvisited.Nonempty
    · rw [answer_nil_pos hst hT]; omega
    · by_cases hq : s.unqueried.Nonempty
      · rw [answer_nil_pad hst hT hq]; exact Nat.le_succ _
      · rw [answer_nil_none hst hT hq]; omega
  · by_cases hc : (s.candidates v).Nonempty
    · rw [answer_cons_pos hst hc]; dsimp only; split_ifs <;> omega
    · rw [answer_cons_neg hst hc]; omega

/-- A query of the search proper (not of the completion phase): a positive answer pushes a new
vertex, which joins the current epoch. -/
lemma answer_of_not_finished (hs : s.Inv) (hfix : s.move = s) (hnf : ¬s.Finished) (b : Bool) :
    (s.answer b).pushes = s.pushes + (if b then 1 else 0) ∧
      (s.answer b).comp.card = s.comp.card + (if b then 1 else 0) ∧ ¬(s.answer b).Finished := by
  obtain ⟨v, rest, hst, hc⟩ := exists_cons_of_move_eq hfix hnf
  have hu := mem_candidates.mp (pick_mem hc)
  have huc : pick hc ∉ s.comp := fun h => by
    have := hs.comp_sub h
    simp only [mem_union, List.mem_toFinset] at this
    exact (mem_unvisited.mp hu.1).elim (fun h1 h2 => this.elim h1 h2)
  rw [answer_cons_pos hst hc]
  refine ⟨by cases b <;> rfl, ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact card_insert_of_notMem huc
    · rfl
  · rintro ⟨h1, -⟩
    dsimp only at h1
    cases b <;> simp [hst] at h1

/-- Where a query is due, the pending pair exists as long as some pair is unqueried. -/
lemma exists_pending (hs : s.Inv) (hfix : s.move = s)
    (hq : s.queried.card < (Fintype.card V).choose 2) : ∃ e, s.pending = some e := by
  by_cases hnf : s.Finished
  · have hT : ¬s.unvisited.Nonempty := by rw [hnf.2]; simp
    have hND : (univ.filter fun e : Sym2 V => ¬e.IsDiag).card = (Fintype.card V).choose 2 := by
      rw [← Sym2.card_subtype_not_diag, Fintype.card_subtype]
    have hsub : s.queried ⊆ univ.filter fun e : Sym2 V => ¬e.IsDiag :=
      fun e he => mem_filter.mpr ⟨mem_univ _, hs.not_diag e he⟩
    obtain ⟨e, he, heq⟩ := exists_mem_notMem_of_card_lt_card (hq.trans_eq hND.symm)
    have hun : s.unqueried.Nonempty := ⟨e, mem_unqueried.mpr ⟨(mem_filter.mp he).2, heq⟩⟩
    exact ⟨_, pending_nil_pad hnf.1 hT hun⟩
  · obtain ⟨v, rest, hst, hc⟩ := exists_cons_of_move_eq hfix hnf
    exact ⟨_, pending_cons_pos hst hc⟩

end State

open State

/-- The search fed with the answers `l`, in order, stopped just before its next query. -/
noncomputable def ofAnswers (V : Type*) [Fintype V] [DecidableEq V] (l : List Bool) :
    State V :=
  l.foldl (fun s b => (s.answer b).settle) (init : State V).settle

/-- The search as an adaptive strategy on the edge coins: after the answers `l`, query the pending
pair of `ofAnswers V l` (or `e₀` once every pair has been queried). -/
noncomputable def nextQuery (e₀ : Sym2 V) (l : List Bool) : Sym2 V :=
  (ofAnswers V l).pending.getD e₀

lemma ofAnswers_nil : ofAnswers V [] = (init : State V).settle := rfl

lemma ofAnswers_append_singleton (l : List Bool) (b : Bool) :
    ofAnswers V (l ++ [b]) = ((ofAnswers V l).answer b).settle := by
  simp [ofAnswers, List.foldl_append]

theorem inv_ofAnswers (l : List Bool) : (ofAnswers V l).Inv := by
  induction l using List.reverseRecOn with
  | nil => exact inv_init.settle
  | append_singleton l b ih => rw [ofAnswers_append_singleton]; exact (ih.answer b).settle

/-- The search is always stopped at a query (or finished). -/
theorem move_ofAnswers (l : List Bool) : (ofAnswers V l).move = ofAnswers V l := by
  induction l using List.reverseRecOn with
  | nil => exact move_settle inv_init
  | append_singleton l b _ =>
    rw [ofAnswers_append_singleton]; exact move_settle ((inv_ofAnswers l).answer b)

theorem le_ofAnswers_append (l l' : List Bool) :
    (ofAnswers V l).Le (ofAnswers V (l ++ l')) := by
  induction l' using List.reverseRecOn with
  | nil => simpa using Le.refl _
  | append_singleton l' b ih =>
    rw [← List.append_assoc, ofAnswers_append_singleton]
    exact ih.trans ((le_answer _ b).trans (le_settle _))

theorem le_ofAnswers_take (l : List Bool) (j : ℕ) :
    (ofAnswers V (l.take j)).Le (ofAnswers V l) := by
  simpa using le_ofAnswers_append (V := V) (l.take j) (l.drop j)

theorem finished_ofAnswers_append (l l' : List Bool) (h : (ofAnswers V l).Finished) :
    (ofAnswers V (l ++ l')).Finished := by
  induction l' using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton l' b ih =>
    rw [← List.append_assoc, ofAnswers_append_singleton, settle_of_finished (answer_finished ih b)]
    exact answer_finished ih b

/-- One query: the pending pair is queried, and found iff the answer is positive. -/
lemma card_step (l : List Bool) (b : Bool) {e : Sym2 V} (hp : (ofAnswers V l).pending = some e) :
    (ofAnswers V (l ++ [b])).queried.card = (ofAnswers V l).queried.card + 1 ∧
      (ofAnswers V (l ++ [b])).found.card =
        (ofAnswers V l).found.card + (if b then 1 else 0) := by
  have hs := inv_ofAnswers (V := V) l
  rw [ofAnswers_append_singleton, settle_queried, settle_found]
  rcases pending_answer (s := ofAnswers V l) b with ⟨hp', _⟩ | ⟨e', hp', he, hq', hf'⟩
  · rw [hp] at hp'; exact absurd hp' (by simp)
  · have hef : e' ∉ (ofAnswers V l).found := fun h => he (hs.found_queried h)
    rw [hq', hf', card_insert_of_notMem he]
    refine ⟨rfl, ?_⟩
    cases b
    · simp
    · simp [card_insert_of_notMem hef]

theorem card_queried_found_of_not_finished (l : List Bool) (h : ¬(ofAnswers V l).Finished) :
    (ofAnswers V l).queried.card = l.length ∧ (ofAnswers V l).found.card = l.count true := by
  induction l using List.reverseRecOn with
  | nil => simp [ofAnswers_nil, settle_queried, settle_found, init]
  | append_singleton l b ih =>
    have hnf : ¬(ofAnswers V l).Finished := fun hf => h (finished_ofAnswers_append l [b] hf)
    obtain ⟨v, rest, hst, hc⟩ := exists_cons_of_move_eq (move_ofAnswers l) hnf
    obtain ⟨h1, h2⟩ := card_step l b (pending_cons_pos hst hc)
    obtain ⟨hq, hf⟩ := ih hnf
    rw [h1, h2, hq, hf]
    cases b <;> simp

/-- Each answer is the answer to a new query: after `t ≤ n (n - 1) / 2` answers, exactly `t`
pairs have been queried, and the found pairs are the positive answers. -/
theorem card_queried_found (l : List Bool) (hl : l.length ≤ (Fintype.card V).choose 2) :
    (ofAnswers V l).queried.card = l.length ∧ (ofAnswers V l).found.card = l.count true := by
  induction l using List.reverseRecOn with
  | nil => simp [ofAnswers_nil, settle_queried, settle_found, init]
  | append_singleton l b ih =>
    have hl' : l.length < (Fintype.card V).choose 2 := by simp at hl; omega
    obtain ⟨hq, hf⟩ := ih hl'.le
    obtain ⟨e, hp⟩ := exists_pending (inv_ofAnswers l) (move_ofAnswers l) (hq ▸ hl')
    obtain ⟨h1, h2⟩ := card_step l b hp
    rw [h1, h2, hq, hf]
    cases b <;> simp

theorem card_found_le (l : List Bool) : (ofAnswers V l).found.card ≤ l.count true := by
  induction l using List.reverseRecOn with
  | nil => simp [ofAnswers_nil, settle_found, init]
  | append_singleton l b ih =>
    rcases hp : (ofAnswers V l).pending with _ | e
    · rcases pending_answer (s := ofAnswers V l) b with ⟨_, ha⟩ | ⟨e', hp', -⟩
      · rw [ofAnswers_append_singleton, settle_found, ha]
        simp only [List.count_append]
        omega
      · rw [hp] at hp'; exact absurd hp' (by simp)
    · rw [(card_step l b hp).2, List.count_append]
      cases b <;> simp <;> omega

/-! ### Queries -/

/-- Every pair is queried at most once: the search is a fresh strategy for all the
`n (n - 1) / 2` pairs of distinct vertices. -/
theorem fresh_nextQuery (e₀ : Sym2 V) :
    FreshUpTo (nextQuery e₀) ((Fintype.card V).choose 2) := by
  intro l hl j hj
  have hlt : (l.take j).length < (Fintype.card V).choose 2 := by
    simp only [List.length_take]; omega
  obtain ⟨ej, hpj⟩ := exists_pending (inv_ofAnswers (l.take j)) (move_ofAnswers _)
    ((card_queried_found _ hlt.le).1 ▸ hlt)
  obtain ⟨e, hp⟩ := exists_pending (inv_ofAnswers l) (move_ofAnswers _)
    ((card_queried_found _ hl.le).1 ▸ hl)
  simp only [nextQuery, hpj, hp, Option.getD_some]
  -- `ej` has been queried by the time of the `l.length`-th query, `e` has not
  have hej : ej ∈ (ofAnswers V (l.take j ++ [l[j]])).queried := by
    rw [ofAnswers_append_singleton, settle_queried]
    rcases pending_answer (s := ofAnswers V (l.take j)) l[j] with ⟨hp', _⟩ | ⟨e', hp', -, hq', -⟩
    · rw [hpj] at hp'; exact absurd hp' (by simp)
    · rw [hpj] at hp'
      rw [hq', Option.some.inj hp']
      exact mem_insert_self _ _
  have hle : (ofAnswers V (l.take j ++ [l[j]])).Le (ofAnswers V l) := by
    rw [← List.take_succ_eq_append_getElem hj]
    exact le_ofAnswers_take l (j + 1)
  rcases pending_answer (s := ofAnswers V l) true with ⟨hp', _⟩ | ⟨e', hp', he, -⟩
  · rw [hp] at hp'; exact absurd hp' (by simp)
  · rw [hp] at hp'
    rw [← Option.some.inj hp'] at he
    exact fun h => he (h ▸ hle.queried hej)

/-- Each answer is the answer to a new query: after `t ≤ n (n - 1) / 2` answers, exactly `t`
pairs have been queried. -/
theorem card_queried_ofAnswers {l : List Bool} (hl : l.length ≤ (Fintype.card V).choose 2) :
    (ofAnswers V l).queried.card = l.length :=
  (card_queried_found l hl).1

/-- Only pairs of distinct vertices are queried. -/
theorem not_isDiag_of_mem_queried (l : List Bool) {e : Sym2 V}
    (he : e ∈ (ofAnswers V l).queried) : ¬e.IsDiag :=
  (inv_ofAnswers l).not_diag e he

/-- On the coins `ω`, the search learns `ω` on the queried pairs: a queried pair has been found
iff its coin is `true`. -/
theorem mem_found_iff_of_queryAnswers (e₀ : Sym2 V) (ω : Sym2 V → Bool) (t : ℕ) {e : Sym2 V}
    (he : e ∈ (ofAnswers V (queryAnswers (nextQuery e₀) ω t)).queried) :
    e ∈ (ofAnswers V (queryAnswers (nextQuery e₀) ω t)).found ↔ ω e = true := by
  induction t generalizing e with
  | zero =>
    simp [queryAnswers, ofAnswers_nil, settle_queried, init] at he
  | succ t ih =>
    set A := queryAnswers (nextQuery e₀) ω t
    have hs := inv_ofAnswers (V := V) A
    simp only [queryAnswers] at he ⊢
    rw [ofAnswers_append_singleton, settle_queried] at he
    rw [ofAnswers_append_singleton, settle_found]
    rcases pending_answer (s := ofAnswers V A) (ω (nextQuery e₀ A)) with
      ⟨_, ha⟩ | ⟨e', hp, he', hq, hf⟩
    · rw [ha] at he ⊢; exact ih he
    · have hn : nextQuery e₀ A = e' := by simp [nextQuery, hp]
      rw [hq] at he
      rw [hf, hn]
      rcases mem_insert.mp he with rfl | he
      · have hef : e ∉ (ofAnswers V A).found := fun h => he' (hs.found_queried h)
        cases hω : ω e
        · simp [hef]
        · simp
      · have hne : e ≠ e' := fun h => he' (h ▸ he)
        rw [← ih he]
        split_ifs <;> simp [hne]

/-- The found pairs have been queried. -/
theorem found_subset_queried (l : List Bool) :
    (ofAnswers V l).found ⊆ (ofAnswers V l).queried :=
  (inv_ofAnswers l).found_queried

/-! ### The sets `S`, `U`, `T` -/

/-- `S` and `U` are disjoint and `U` has no repetition. -/
theorem disjoint_done_stack (l : List Bool) :
    Disjoint (ofAnswers V l).done (ofAnswers V l).stack.toFinset ∧
      (ofAnswers V l).stack.Nodup :=
  ⟨(inv_ofAnswers l).disj, (inv_ofAnswers l).nodup⟩

/-- `U` spans a path of found pairs: consecutive vertices of the stack form found pairs. -/
theorem stack_chain_ofAnswers (l : List Bool) :
    (ofAnswers V l).stack.IsChain fun u v => s(u, v) ∈ (ofAnswers V l).found :=
  (inv_ofAnswers l).chain

/-- All pairs between `S` and `T` have been queried and answered negatively. -/
theorem queried_of_mem_done_of_mem_unvisited (l : List Bool) {a b : V}
    (ha : a ∈ (ofAnswers V l).done) (hb : b ∈ (ofAnswers V l).unvisited) :
    s(a, b) ∈ (ofAnswers V l).queried ∧ s(a, b) ∉ (ofAnswers V l).found :=
  ⟨(inv_ofAnswers l).done_unvisited a ha b hb,
    fun h => (inv_ofAnswers l).found_unvisited _ h b (Sym2.mem_mk_right a b) hb⟩

/-- `|U| ≤ 1 + ∑ Xᵢ`: every vertex of the stack but the first one of its epoch was pushed by a
positive answer. -/
theorem length_stack_le (l : List Bool) :
    (ofAnswers V l).stack.length ≤ 1 + l.count true := by
  have hs := inv_ofAnswers (V := V) l
  rw [← List.toFinset_card_of_nodup hs.nodup]
  have h1 : (ofAnswers V l).stack.toFinset.card ≤ (ofAnswers V l).comp.card :=
    card_le_card fun x hx => hs.stack_comp x (List.mem_toFinset.mp hx)
  have := hs.card_comp
  have := hs.pushes_le
  have := card_found_le (V := V) l
  omega

lemma not_finished_of_unvisited {s : State V} (hT : s.unvisited.Nonempty) : ¬s.Finished :=
  fun h => by rw [h.2] at hT; simp at hT

/-- While `T ≠ ∅`, every positive answer has moved a new vertex from `T` to `U`: `|S ∪ U|` is the
number of positive answers plus the number of epochs. -/
theorem count_true_add_epochs (l : List Bool) (hT : (ofAnswers V l).unvisited.Nonempty) :
    l.count true + (ofAnswers V l).epochs =
      ((ofAnswers V l).done ∪ (ofAnswers V l).stack.toFinset).card := by
  have hs := inv_ofAnswers (V := V) l
  have hnf := not_finished_of_unvisited hT
  rw [hs.card_eq, ← hs.pushes_eq hnf, (card_queried_found_of_not_finished l hnf).2]

/-- While `T ≠ ∅`: `∑ Xᵢ ≤ |S ∪ U|`. -/
theorem count_true_le_card (l : List Bool) (hT : (ofAnswers V l).unvisited.Nonempty) :
    l.count true ≤ ((ofAnswers V l).done ∪ (ofAnswers V l).stack.toFinset).card := by
  rw [← count_true_add_epochs l hT]; omega

/-- Between two consecutive queries, `|S ∪ U|` grows by at most `2` (one push by a positive answer,
one new epoch). -/
theorem card_union_append_le (l : List Bool) (b : Bool) :
    ((ofAnswers V (l ++ [b])).done ∪ (ofAnswers V (l ++ [b])).stack.toFinset).card ≤
      ((ofAnswers V l).done ∪ (ofAnswers V l).stack.toFinset).card + 2 := by
  rw [(inv_ofAnswers (V := V) (l ++ [b])).card_eq, (inv_ofAnswers (V := V) l).card_eq,
    ofAnswers_append_singleton, settle_pushes]
  have h1 := answer_pushes_le (s := ofAnswers V l) b
  have h2 := epochs_settle_le ((inv_ofAnswers (V := V) l).answer b)
  rw [answer_epochs] at h2
  omega

/-- At the start, `|S ∪ U| ≤ 1`. -/
theorem card_union_nil_le :
    ((ofAnswers V []).done ∪ (ofAnswers V []).stack.toFinset).card ≤ 1 := by
  rw [(inv_ofAnswers (V := V) []).card_eq, ofAnswers_nil, settle_pushes]
  have := epochs_settle_le (inv_init (V := V))
  simp only [init] at this ⊢
  omega

/-! ### Epochs -/

/-- The vertices discovered in the current epoch are connected by found pairs. -/
theorem reachable_of_mem_comp (l : List Bool) {u v : V} (hu : u ∈ (ofAnswers V l).comp)
    (hv : v ∈ (ofAnswers V l).comp) :
    (SimpleGraph.fromEdgeSet ((ofAnswers V l).found : Set (Sym2 V))).Reachable u v :=
  (inv_ofAnswers l).comp_conn u hu v hv

/-- One query in the same epoch, while `T ≠ ∅`: a positive answer adds a vertex to the epoch. -/
lemma card_comp_append (l : List Bool) (b : Bool)
    (hep : (ofAnswers V (l ++ [b])).epochs = (ofAnswers V l).epochs)
    (hnf : ¬(ofAnswers V l).Finished) :
    (ofAnswers V (l ++ [b])).comp.card = (ofAnswers V l).comp.card + (if b then 1 else 0) := by
  have hs := inv_ofAnswers (V := V) l
  obtain ⟨-, hc, -⟩ := answer_of_not_finished hs (move_ofAnswers l) hnf b
  rw [ofAnswers_append_singleton] at hep ⊢
  rw [comp_settle_of_epochs_eq (by rw [hep, answer_epochs]), hc]

/-- Within one epoch, while `T ≠ ∅`, each positive answer adds a vertex to the current epoch. -/
theorem count_drop_le_card_comp (l : List Bool) {j : ℕ} (hj : j ≤ l.length)
    (hep : (ofAnswers V (l.take j)).epochs = (ofAnswers V l).epochs)
    (hT : (ofAnswers V l).unvisited.Nonempty) :
    (l.drop j).count true + (ofAnswers V (l.take j)).comp.card ≤ (ofAnswers V l).comp.card := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rcases Nat.lt_or_ge l.length j with hlj | hlj
    · obtain rfl : j = l.length + 1 := by simp at hj; omega
      simp only [List.drop_eq_nil_of_le (by simp : (l ++ [b]).length ≤ l.length + 1),
        List.count_nil, zero_add]
      rw [List.take_of_length_le (by simp)]
    · have hle := le_ofAnswers_append (V := V) l [b]
      have hle' := le_ofAnswers_take (V := V) l j
      rw [List.take_append_of_le_length hlj] at hep ⊢
      rw [List.drop_append_of_le_length hlj, List.count_append]
      have hep' : (ofAnswers V (l.take j)).epochs = (ofAnswers V l).epochs := by
        have := hle.epochs; have := hle'.epochs; omega
      have hT' : (ofAnswers V l).unvisited.Nonempty := hT.mono hle.unvisited
      have := ih hlj hep' hT'
      rw [card_comp_append l b (by omega) (not_finished_of_unvisited hT')]
      cases b <;> simp <;> omega

/-- When a new epoch starts, `U` has just been emptied: the previously explored set `D` has all its
pairs with `V ∖ D` queried; it contains a vertex for each positive answer, and it is contained
in the current `S`. -/
theorem exists_of_epochs_lt (l : List Bool) (b : Bool)
    (hep : (ofAnswers V l).epochs < (ofAnswers V (l ++ [b])).epochs) :
    ∃ D : Finset V, D ⊆ (ofAnswers V (l ++ [b])).done ∧ (l ++ [b]).count true ≤ D.card ∧
      ∀ a ∈ D, ∀ c ∉ D, s(a, c) ∈ (ofAnswers V (l ++ [b])).queried := by
  have hs := inv_ofAnswers (V := V) l
  have hs' := inv_ofAnswers (V := V) (l ++ [b])
  set s := ofAnswers V l
  set s' := ofAnswers V (l ++ [b]) with hs'def
  have hnf : ¬s.Finished := by
    intro hf
    rw [hs'def, ofAnswers_append_singleton, settle_of_finished (answer_finished hf b)] at hep
    rw [answer_epochs] at hep
    exact lt_irrefl _ hep
  obtain ⟨hp, -, -⟩ := answer_of_not_finished hs (move_ofAnswers l) hnf b
  have hcount : (l ++ [b]).count true = s'.pushes := by
    rw [hs'def, ofAnswers_append_singleton, settle_pushes, hp, ← hs.pushes_eq hnf,
      (card_queried_found_of_not_finished l hnf).2, List.count_append]
    cases b <;> simp
  have hlt : (s.answer b).epochs < (s.answer b).settle.epochs := by
    rw [answer_epochs]
    rw [hs'def, ofAnswers_append_singleton] at hep
    exact hep
  obtain ⟨x, hx⟩ := comp_settle_of_lt hlt
  rw [← ofAnswers_append_singleton] at hx
  refine ⟨(s'.done ∪ s'.stack.toFinset) \ s'.comp, ?_, ?_, hs'.base⟩
  · intro y hy
    simp only [mem_sdiff, mem_union, List.mem_toFinset] at hy
    rcases hy.1 with h | h
    · exact h
    · exact absurd (hs'.stack_comp y h) hy.2
  · rw [card_sdiff_of_subset hs'.comp_sub, hs'.card_eq, hcount, hx, card_singleton]
    omega


end DFS
end Epidemics
