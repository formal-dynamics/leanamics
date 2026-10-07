import Epidemics.SubcriticalChernoff
import Epidemics.SubcriticalCluster

/-! # Exploring a percolation cluster: deferred decisions (EPI-2)

The crux of the proof of Theorem E.1 of Becchetti, Clementi, Denni, Pasquale, Trevisan, Ziccardi,
*Percolation and epidemic processes in one-dimensional small-world networks* (arXiv:2103.16398):
the cluster of a vertex in bond percolation on a graph of maximum degree `d` is explored one edge
at a time, each coin being looked at only when its edge is examined, so the cluster size is
dominated by a binomial tail.

Instead of running an explicit BFS, we prove a statement about every *state* of an exploration:
a set `D` of discovered vertices and a set `X` of examined pairs, whose coins are forced closed
(`closeOff X ω`; an examined open edge has both endpoints in `D`, so closing it is harmless). The
`frontier` counts the unexamined edges of `G` leaving `D`. Theorem `prob_reachSet_le_binTail`:
if `frontier G D X + (k - 1)(d - 1) ≤ m`, then `D` reaches at least `k` new vertices with
probability at most `binTail p m k`. The induction on `m` conditions on the coin of one frontier
edge `{w, x}` (`coins_prob_split`):
* closed: the state becomes `(D, X ∪ {wx})` and the frontier loses one edge;
* open: the state becomes `(D ∪ {x}, X ∪ {wx})`, one vertex is found, and the frontier gains at
  most `d - 1` edges at `x` while losing `wx`;
which matches the recursion `binTail_succ_succ`. Starting from `({s}, ∅)`, whose frontier is at
most `d`, gives the bound `binTail p (t (d - 1) + 1) t` for `t < |C(s)|`.
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Closing examined coins -/

/-- The coins with every pair of `X` forced closed. -/
def closeOff (X : Finset (Sym2 V)) (ω : Sym2 V → Bool) : Sym2 V → Bool :=
  fun e => ω e && decide (e ∉ X)

omit [Fintype V] in
lemma closeOff_empty (ω : Sym2 V → Bool) : closeOff ∅ ω = ω := by
  funext e
  simp [closeOff]

omit [Fintype V] in
lemma perc_closeOff_adj {G : SimpleGraph V} {X : Finset (Sym2 V)} {ω : Sym2 V → Bool}
    {u v : V} :
    (perc G (closeOff X ω)).Adj u v ↔ G.Adj u v ∧ ω s(u, v) = true ∧ s(u, v) ∉ X := by
  simp [perc, closeOff]

omit [Fintype V] in
/-- A closed examined coin is the same as a forced-closed one. -/
lemma closeOff_update_false (X : Finset (Sym2 V)) (ω : Sym2 V → Bool) (e : Sym2 V) :
    closeOff X (Function.update ω e false) = closeOff (insert e X) ω := by
  funext e'
  by_cases h : e' = e
  · subst h
    simp [closeOff]
  · simp [closeOff, h]

/-! ### The frontier of an exploration state -/

section Frontier
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The unexamined edges of `G` leaving `D`, counted from their endpoint in `D`. -/
def frontier (D : Finset V) (X : Finset (Sym2 V)) : ℕ :=
  ∑ u ∈ D, (univ.filter fun v => v ∉ D ∧ G.Adj u v ∧ s(u, v) ∉ X).card

variable {G}

lemma mem_of_frontier_eq_zero {D : Finset V} {X : Finset (Sym2 V)} (h : frontier G D X = 0)
    {u v : V} (hu : u ∈ D) (hv : v ∉ D) (hadj : G.Adj u v) : s(u, v) ∈ X := by
  by_contra hX
  have h0 := (sum_eq_zero_iff.mp h) u hu
  rw [card_eq_zero, filter_eq_empty_iff] at h0
  exact h0 (mem_univ v) ⟨hv, hadj, hX⟩

lemma exists_of_frontier_ne_zero {D : Finset V} {X : Finset (Sym2 V)} (h : frontier G D X ≠ 0) :
    ∃ w ∈ D, ∃ x, x ∉ D ∧ G.Adj w x ∧ s(w, x) ∉ X := by
  by_contra hne
  push Not at hne
  apply h
  refine sum_eq_zero fun u hu => ?_
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro v - ⟨hv, hadj, hX⟩
  exact hX (hne u hu v hv hadj)

/-- Examining the frontier edge `{w, x}` removes it from the count of `w`, whether or not `x` is
added to the discovered set. -/
lemma sum_card_lt_frontier {D D' : Finset V} {X : Finset (Sym2 V)} (hD : D ⊆ D') {w x : V}
    (hw : w ∈ D) (hx : x ∉ D) (hadj : G.Adj w x) (hX : s(w, x) ∉ X) :
    ∑ u ∈ D, (univ.filter fun v => v ∉ D' ∧ G.Adj u v ∧ s(u, v) ∉ insert s(w, x) X).card <
      frontier G D X := by
  have hsub (u : V) : (univ.filter fun v => v ∉ D' ∧ G.Adj u v ∧ s(u, v) ∉ insert s(w, x) X) ⊆
      univ.filter fun v => v ∉ D ∧ G.Adj u v ∧ s(u, v) ∉ X := by
    intro v
    simp only [mem_filter, mem_univ, true_and, mem_insert, not_or]
    rintro ⟨hv, hadj', -, hX'⟩
    exact ⟨fun h => hv (hD h), hadj', hX'⟩
  refine sum_lt_sum (fun u _ => card_le_card (hsub u)) ⟨w, hw, card_lt_card ?_⟩
  rw [ssubset_iff_of_subset (hsub w)]
  exact ⟨x, by simp [hx, hadj, hX], by simp⟩

/-- **Closed branch**: the frontier loses the examined edge. -/
lemma frontier_insert_edge_lt {D : Finset V} {X : Finset (Sym2 V)} {w x : V} (hw : w ∈ D)
    (hx : x ∉ D) (hadj : G.Adj w x) (hX : s(w, x) ∉ X) :
    frontier G D (insert s(w, x) X) < frontier G D X :=
  sum_card_lt_frontier (subset_refl D) hw hx hadj hX

/-- **Open branch**: the new vertex `x` brings at most `d - 1` new frontier edges, and the
examined edge leaves the frontier. -/
lemma frontier_insert_vertex_le {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) {D : Finset V}
    {X : Finset (Sym2 V)} {w x : V} (hw : w ∈ D) (hx : x ∉ D) (hadj : G.Adj w x)
    (hX : s(w, x) ∉ X) :
    frontier G (insert x D) (insert s(w, x) X) + 1 ≤ frontier G D X + (d - 1) := by
  have hlt := sum_card_lt_frontier (subset_insert x D) hw hx hadj hX
  have hxterm : (univ.filter fun v =>
      v ∉ insert x D ∧ G.Adj x v ∧ s(x, v) ∉ insert s(w, x) X).card ≤ d - 1 := by
    calc _ ≤ ((G.neighborFinset x).erase w).card := by
          apply card_le_card
          intro v
          simp only [mem_filter, mem_univ, true_and, mem_insert, not_or, mem_erase,
            mem_neighborFinset]
          rintro ⟨⟨-, hvD⟩, hxv, -⟩
          exact ⟨fun h => hvD (h ▸ hw), hxv⟩
      _ = G.degree x - 1 := by
          rw [card_erase_of_mem (by simpa using hadj.symm), card_neighborFinset_eq_degree]
      _ ≤ d - 1 := Nat.sub_le_sub_right (hdeg x) 1
  unfold frontier at hlt ⊢
  rw [sum_insert hx]
  omega

/-- The initial frontier `({s}, ∅)` has at most `d` edges. -/
lemma frontier_singleton_le {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (s : V) :
    frontier G {s} ∅ ≤ d := by
  unfold frontier
  rw [sum_singleton]
  calc _ ≤ (G.neighborFinset s).card := by
        apply card_le_card
        intro v
        simp only [mem_filter, mem_univ, true_and, mem_neighborFinset]
        exact fun h => h.2.1
    _ = G.degree s := card_neighborFinset_eq_degree G s
    _ ≤ d := hdeg s

/-- With an empty frontier, the discovered set is the whole cluster. -/
lemma reachSet_closeOff_eq_self {D : Finset V} {X : Finset (Sym2 V)} (h : frontier G D X = 0)
    (ω : Sym2 V → Bool) : reachSet (perc G (closeOff X ω)) D = D :=
  reachSet_eq_self fun u hu v hadj => by
    by_contra hv
    rw [perc_closeOff_adj] at hadj
    exact hadj.2.2 (mem_of_frontier_eq_zero h hu hv hadj.1)

omit [DecidableRel G.Adj] in
/-- **Open branch, pathwise**: if the frontier edge `{w, x}` is open, the cluster of `D` is the
cluster of `D ∪ {x}` with that edge examined. -/
lemma reachSet_update_true {D : Finset V} {X : Finset (Sym2 V)} {w x : V} (hw : w ∈ D)
    (hadj : G.Adj w x) (hX : s(w, x) ∉ X) (ω : Sym2 V → Bool) :
    reachSet (perc G (closeOff X (Function.update ω s(w, x) true))) D =
      reachSet (perc G (closeOff (insert s(w, x) X) ω)) (insert x D) := by
  have hHwx : (perc G (closeOff X (Function.update ω s(w, x) true))).Adj w x := by
    rw [perc_closeOff_adj]
    simp [hadj, hX]
  rw [← reachSet_insert hw hHwx]
  symm
  apply reachSet_eq_of_le
  · intro u v huv
    rw [perc_closeOff_adj] at huv ⊢
    obtain ⟨hG, hω, hXi⟩ := huv
    rw [mem_insert, not_or] at hXi
    refine ⟨hG, ?_, hXi.2⟩
    rw [Function.update_of_ne hXi.1]
    exact hω
  · intro u v huv hnot
    rw [perc_closeOff_adj] at huv hnot
    obtain ⟨hG, hω, hXi⟩ := huv
    by_cases he : s(u, v) = s(w, x)
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem hw
    · exfalso
      apply hnot
      rw [Function.update_of_ne he] at hω
      exact ⟨hG, hω, by rw [mem_insert, not_or]; exact ⟨he, hXi⟩⟩

end Frontier

/-! ### Deferred decisions -/

section Deferred
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)

/-- Conditioning the percolation coins on the coin of one pair. -/
lemma coins_prob_update (e : Sym2 V) (s : (Sym2 V → Bool) → Prop) :
    (coins p h0 h1).prob s =
      p * (coins p h0 h1).prob (fun ω => s (Function.update ω e true)) +
        (1 - p) * (coins p h0 h1).prob (fun ω => s (Function.update ω e false)) :=
  coins_prob_split p h0 h1 e s

/-- With an empty frontier, no new vertex is ever found. -/
lemma prob_reachSet_eq_zero {D : Finset V} {X : Finset (Sym2 V)} (hF : frontier G D X = 0)
    (k : ℕ) :
    (coins p h0 h1).prob
      (fun ω => D.card + (k + 1) ≤ (reachSet (perc G (closeOff X ω)) D).card) = 0 :=
  prob_eq_zero _ fun ω hω => by
    rw [reachSet_closeOff_eq_self hF] at hω
    omega

/-- **Deferred decisions, for every exploration state**: if
`frontier G D X + (k - 1)(d - 1) ≤ m`, then the cluster of `D` with the pairs of `X` closed has at
least `|D| + k` vertices with probability at most `binTail p m k`. -/
theorem prob_reachSet_le_binTail (hdeg : ∀ v, G.degree v ≤ d) (m : ℕ) :
    ∀ (D : Finset V) (X : Finset (Sym2 V)) (k : ℕ), frontier G D X + (k - 1) * (d - 1) ≤ m →
      (coins p h0 h1).prob
          (fun ω => D.card + k ≤ (reachSet (perc G (closeOff X ω)) D).card) ≤
        binTail p h0 h1 m k := by
  induction m with
  | zero =>
    intro D X k hm
    rcases k with _ | k
    · rw [binTail_zero_right]
      exact Distribution.prob_le_one _ _
    · rw [prob_reachSet_eq_zero h0 h1 (by omega)]
      exact binTail_nonneg h0 h1 _ _
  | succ m ih =>
    intro D X k hm
    rcases k with _ | k
    · rw [binTail_zero_right]
      exact Distribution.prob_le_one _ _
    by_cases hF : frontier G D X = 0
    · rw [prob_reachSet_eq_zero h0 h1 hF]
      exact binTail_nonneg h0 h1 _ _
    obtain ⟨w, hw, x, hx, hadj, hX⟩ := exists_of_frontier_ne_zero hF
    simp only [add_tsub_cancel_right] at hm
    -- the coin of `{w, x}` is closed
    have hclosed : (coins p h0 h1).prob (fun ω => D.card + (k + 1) ≤
          (reachSet (perc G (closeOff X (Function.update ω s(w, x) false))) D).card) ≤
        binTail p h0 h1 m (k + 1) := by
      simp only [closeOff_update_false]
      refine ih D _ (k + 1) ?_
      have := frontier_insert_edge_lt hw hx hadj hX
      simp only [add_tsub_cancel_right]
      omega
    -- the coin of `{w, x}` is open
    have hopen : (coins p h0 h1).prob (fun ω => D.card + (k + 1) ≤
          (reachSet (perc G (closeOff X (Function.update ω s(w, x) true))) D).card) ≤
        binTail p h0 h1 m k := by
      have hev (ω : Sym2 V → Bool) : D.card + (k + 1) ≤
            (reachSet (perc G (closeOff X (Function.update ω s(w, x) true))) D).card ↔
          (insert x D).card + k ≤
            (reachSet (perc G (closeOff (insert s(w, x) X) ω)) (insert x D)).card := by
        rw [reachSet_update_true hw hadj hX, card_insert_of_notMem hx]
        constructor <;> intro h <;> omega
      rw [prob_congr _ hev]
      rcases k with _ | k
      · rw [binTail_zero_right]
        exact Distribution.prob_le_one _ _
      · refine ih (insert x D) _ (k + 1) ?_
        have := frontier_insert_vertex_le hdeg hw hx hadj hX
        simp only [add_tsub_cancel_right]
        rw [add_mul, one_mul] at hm
        omega
    rw [coins_prob_update h0 h1 s(w, x), binTail_succ_succ]
    exact add_le_add (mul_le_mul_of_nonneg_left hopen h0)
      (mul_le_mul_of_nonneg_left hclosed (by linarith))

/-- **Deferred decisions** (the proof of [BCDPTZ22, Theorem E.1]): the cluster of `s` has more
than `t` vertices with probability at most `binTail p (t (d - 1) + 1) t`. -/
theorem prob_cluster_gt_le_binTail (hdeg : ∀ v, G.degree v ≤ d) (s : V) (t : ℕ) :
    (coins p h0 h1).prob (fun ω => t < ((perc G ω).connectedComponentMk s).supp.ncard) ≤
      binTail p h0 h1 (t * (d - 1) + 1) t := by
  rcases t with _ | t
  · rw [binTail_zero_right]
    exact Distribution.prob_le_one _ _
  have hev (ω : Sym2 V → Bool) : t + 1 < ((perc G ω).connectedComponentMk s).supp.ncard ↔
      ({s} : Finset V).card + (t + 1) ≤ (reachSet (perc G (closeOff ∅ ω)) {s}).card := by
    rw [ncard_supp_eq_card_reachSet, closeOff_empty, card_singleton]
    constructor <;> intro h <;> omega
  rw [prob_congr _ hev]
  refine prob_reachSet_le_binTail h0 h1 hdeg _ {s} ∅ (t + 1) ?_
  have := frontier_singleton_le hdeg s
  simp only [add_tsub_cancel_right]
  rw [add_mul, one_mul]
  omega

end Deferred

end Epidemics
