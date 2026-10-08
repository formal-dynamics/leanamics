import Epidemics.SmallWorldMart

/-! # Subcritical exploration of a percolation cluster (EPI-6)

The upper bound on cluster sizes of [BCDPTZ22] for `SWG(n, c/n)` (Lemma C.1) explores the
cluster of a node `s` in the percolation graph `perc G ω` breadth-first, with deferred decisions on
the edge coins. Here the coins are independent Bernoulli(`r e`) with possibly different
probabilities, and the search processes one node per step: it reads at once the block of all
pairs from the current node to its undiscovered `G`-neighbours, and appends the open ones to the
queue.

Every discovered node `y ≠ s` carries the weight `h e` of the pair `e` through which it was
discovered (the root carries `w₀`). If the expected weight discovered from a node of weight `w`
is at most `λ w` (hypothesis `hstep`, with `κ λ ≤ 1`, the subcritical condition), the potential
`exp θ (discovered weight − κ λ · processed weight)` is a supermartingale
(`expect_prod_hist_le_one_of_fresh`); a cluster with more than `t` nodes forces `t` processed
nodes and a large potential, whence, by Markov's inequality (`prob_cluster_gt_le`),
`P(|C(s)| ≥ t + 1) ≤ exp (-θ ((1 - κ λ) t w_min - w_max))`.

For `SWG(n, c/n)` the weights distinguish nodes reached through a cycle edge from nodes reached
through a bridge, the two types behind the paper's Galton–Watson comparison (Appendix C).
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

namespace Explore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- State of the breadth-first search: discovered nodes in discovery (= processing) order, the
number of processed nodes, and the weights of the discovered nodes. -/
structure State (V : Type*) where
  order : List V
  proc : ℕ
  wt : V → ℝ

variable (G : SimpleGraph V) [DecidableRel G.Adj] (h : Sym2 V → ℝ)

/-- The undiscovered `G`-neighbours of `v`. -/
def fresh (σ : State V) (v : V) : Finset V :=
  univ.filter fun y => y ∉ σ.order ∧ G.Adj v y

/-- The block of pairs read when processing the current node `σ.order[σ.proc]` (empty when the
search is over). -/
def block (σ : State V) : Finset (Sym2 V) :=
  if hp : σ.proc < σ.order.length then
    (fresh G σ σ.order[σ.proc]).image fun y => s(σ.order[σ.proc], y)
  else ∅

/-- The nodes discovered from `v` when the open pairs are `A`. -/
def newV (σ : State V) (v : V) (A : Finset (Sym2 V)) : Finset V :=
  (fresh G σ v).filter fun y => s(v, y) ∈ A

/-- One step of the search, given the set `A` of open pairs of the block. -/
noncomputable def update (σ : State V) (A : Finset (Sym2 V)) : State V :=
  if hp : σ.proc < σ.order.length then
    ⟨σ.order ++ (newV G σ σ.order[σ.proc] A).toList, σ.proc + 1,
      fun y => if y ∈ newV G σ σ.order[σ.proc] A then h s(σ.order[σ.proc], y) else σ.wt y⟩
  else σ

/-- The state after the observations `l`, starting from the root `s` of weight `w₀`. -/
noncomputable def state (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) : State V :=
  l.foldl (update G h) ⟨[s], 0, fun _ => w₀⟩

variable {G h}

lemma state_nil (s : V) (w₀ : ℝ) : state G h s w₀ [] = ⟨[s], 0, fun _ => w₀⟩ := rfl

lemma state_append (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) (A : Finset (Sym2 V)) :
    state G h s w₀ (l ++ [A]) = update G h (state G h s w₀ l) A := by
  simp [state, List.foldl_append]

lemma update_of_lt {σ : State V} (hp : σ.proc < σ.order.length) (A : Finset (Sym2 V)) :
    update G h σ A = ⟨σ.order ++ (newV G σ σ.order[σ.proc] A).toList, σ.proc + 1,
      fun y => if y ∈ newV G σ σ.order[σ.proc] A then h s(σ.order[σ.proc], y) else σ.wt y⟩ := by
  rw [update, dif_pos hp]

lemma update_of_ge {σ : State V} (hp : ¬σ.proc < σ.order.length) (A : Finset (Sym2 V)) :
    update G h σ A = σ := by
  rw [update, dif_neg hp]

lemma block_of_lt {σ : State V} (hp : σ.proc < σ.order.length) :
    block G σ = (fresh G σ σ.order[σ.proc]).image fun y => s(σ.order[σ.proc], y) := by
  rw [block, dif_pos hp]

lemma block_of_ge {σ : State V} (hp : ¬σ.proc < σ.order.length) : block G σ = ∅ := by
  rw [block, dif_neg hp]

lemma mem_fresh {σ : State V} {v y : V} : y ∈ fresh G σ v ↔ y ∉ σ.order ∧ G.Adj v y := by
  simp [fresh]

lemma mem_newV {σ : State V} {v y : V} {A : Finset (Sym2 V)} :
    y ∈ newV G σ v A ↔ (y ∉ σ.order ∧ G.Adj v y) ∧ s(v, y) ∈ A := by
  simp [newV, fresh]

/-! ### Invariants -/

/-- The invariants of the search. -/
structure Inv (s : V) (w₀ : ℝ) (σ : State V) : Prop where
  nodup : σ.order.Nodup
  head : σ.order[0]? = some s
  proc_le : σ.proc ≤ σ.order.length
  root_wt : σ.wt s = w₀
  parent : ∀ v ∈ σ.order, v ≠ s → ∃ u ∈ σ.order, G.Adj u v ∧ σ.wt v = h s(u, v)

lemma inv_update {s : V} {w₀ : ℝ} {σ : State V} (hσ : Inv (G := G) (h := h) s w₀ σ)
    (A : Finset (Sym2 V)) : Inv (G := G) (h := h) s w₀ (update G h σ A) := by
  by_cases hp : σ.proc < σ.order.length
  · rw [update_of_lt hp]
    set v := σ.order[σ.proc]
    have hvo : v ∈ σ.order := List.getElem_mem hp
    have hns : s ∉ newV G σ v A := fun hs => (mem_newV.mp hs).1.1
      (List.mem_of_getElem? hσ.head)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine List.Nodup.append hσ.nodup (Finset.nodup_toList _) ?_
      intro a ha hb
      rw [Finset.mem_toList] at hb
      exact (mem_newV.mp hb).1.1 ha
    · rw [List.getElem?_append_left (List.length_pos_of_mem (List.mem_of_getElem? hσ.head))]
      exact hσ.head
    · simp only [List.length_append, Finset.length_toList]
      omega
    · dsimp only
      rw [if_neg hns]
      exact hσ.root_wt
    · intro y hy hys
      rw [List.mem_append, Finset.mem_toList] at hy
      by_cases hyn : y ∈ newV G σ v A
      · refine ⟨v, List.mem_append_left _ hvo, (mem_newV.mp hyn).1.2, ?_⟩
        simp only [if_pos hyn]
      · rcases hy with hy | hy
        · obtain ⟨u, hu, hadj, hw⟩ := hσ.parent y hy hys
          refine ⟨u, List.mem_append_left _ hu, hadj, ?_⟩
          simp only [if_neg hyn]
          exact hw
        · exact absurd hy hyn
  · rw [update_of_ge hp]
    exact hσ

lemma inv_state (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) :
    Inv (G := G) (h := h) s w₀ (state G h s w₀ l) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨List.nodup_singleton s, rfl, Nat.zero_le _, rfl, ?_⟩
    intro v hv hvs
    exact absurd (List.mem_singleton.mp hv) hvs
  | append_singleton l A ih =>
    rw [state_append]
    exact inv_update ih A

/-- The order only grows, and `proc` only grows. -/
lemma update_mono (σ : State V) (A : Finset (Sym2 V)) :
    σ.order <+: (update G h σ A).order ∧ σ.proc ≤ (update G h σ A).proc ∧
      ∀ y ∈ σ.order, (update G h σ A).wt y = σ.wt y := by
  by_cases hp : σ.proc < σ.order.length
  · rw [update_of_lt hp]
    refine ⟨List.prefix_append _ _, by simp, fun y hy => ?_⟩
    have : y ∉ newV G σ σ.order[σ.proc] A := fun hn => (mem_newV.mp hn).1.1 hy
    simp only [if_neg this]
  · rw [update_of_ge hp]
    exact ⟨List.prefix_refl _, le_refl _, fun _ _ => rfl⟩

lemma state_mono (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) {j : ℕ} (hj : j ≤ l.length) :
    (state G h s w₀ (l.take j)).order <+: (state G h s w₀ l).order ∧
      (state G h s w₀ (l.take j)).proc ≤ (state G h s w₀ l).proc ∧
      ∀ y ∈ (state G h s w₀ (l.take j)).order,
        (state G h s w₀ l).wt y = (state G h s w₀ (l.take j)).wt y := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l A ih =>
    rcases Nat.lt_or_ge j (l.length + 1) with hjl | hjl
    · have hj' : j ≤ l.length := by omega
      rw [List.take_append_of_le_length hj']
      obtain ⟨h1, h2, h3⟩ := ih hj'
      obtain ⟨u1, u2, u3⟩ := update_mono (G := G) (h := h) (state G h s w₀ l) A
      rw [state_append]
      refine ⟨h1.trans u1, h2.trans u2, fun y hy => ?_⟩
      rw [u3 y (h1.subset hy), h3 y hy]
    · rw [List.take_of_length_le (by simp; omega)]
      exact ⟨List.prefix_refl _, le_refl _, fun _ _ => rfl⟩

/-- `proc` counts the steps until the search is over. -/
lemma proc_state (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) :
    (state G h s w₀ l).proc = l.length ∨
      ((state G h s w₀ l).proc < l.length ∧
        (state G h s w₀ l).proc = (state G h s w₀ l).order.length) := by
  induction l using List.reverseRecOn with
  | nil => left; rfl
  | append_singleton l A ih =>
    rw [state_append, List.length_append, List.length_singleton]
    by_cases hp : (state G h s w₀ l).proc < (state G h s w₀ l).order.length
    · rw [update_of_lt hp]
      rcases ih with ih | ih
      · left; simp [ih]
      · omega
    · rw [update_of_ge hp]
      right
      have := (inv_state (G := G) (h := h) s w₀ l).proc_le
      rcases ih with ih | ih <;> omega

/-! ### Freshness of the blocks -/

/-- Every pair read along the history `l` has a processed endpoint. -/
lemma readSet_sub (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) :
    ∀ e ∈ readSet (fun l => block G (state G h s w₀ l)) l,
      ∃ u ∈ (state G h s w₀ l).order.take (state G h s w₀ l).proc, ∃ y, e = s(u, y) := by
  intro e he
  simp only [readSet, mem_biUnion, mem_range] at he
  obtain ⟨j, hj, he⟩ := he
  set σ := state G h s w₀ (l.take j)
  have hp : σ.proc < σ.order.length := by
    by_contra hp
    rw [block_of_ge hp] at he
    exact absurd he (Finset.notMem_empty e)
  rw [block_of_lt hp, Finset.mem_image] at he
  obtain ⟨y, -, rfl⟩ := he
  refine ⟨σ.order[σ.proc], ?_, y, rfl⟩
  -- the node processed at step `j` is processed after step `j + 1`
  have hj1 : j + 1 ≤ l.length := hj
  obtain ⟨h1, h2, -⟩ := state_mono (G := G) (h := h) s w₀ l hj1
  have hstep : state G h s w₀ (l.take (j + 1)) = update G h σ (l[j]'hj) := by
    rw [List.take_succ_eq_append_getElem hj, state_append]
  rw [hstep, update_of_lt hp] at h1 h2
  simp only at h1 h2
  have hlen : σ.proc < (σ.order ++ (newV G σ σ.order[σ.proc] (l[j]'hj)).toList).length := by
    simp; omega
  have hpre := h1.getElem hlen
  rw [List.getElem_append_left hp] at hpre
  rw [hpre, List.mem_take_iff_getElem]
  exact ⟨σ.proc, by have := h1.length_le; simp at this; omega, rfl⟩

lemma block_fresh (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) :
    Disjoint (block G (state G h s w₀ l)) (readSet (fun l => block G (state G h s w₀ l)) l) := by
  have key := readSet_sub (G := G) (h := h) s w₀ l
  have hnd := (inv_state (G := G) (h := h) s w₀ l).nodup
  set σ := state G h s w₀ l
  by_cases hp : σ.proc < σ.order.length
  · rw [Finset.disjoint_left]
    intro e he he'
    rw [block_of_lt hp, Finset.mem_image] at he
    obtain ⟨y, hy, rfl⟩ := he
    obtain ⟨u, hu, y', he'⟩ := key _ he'
    have hy' := (mem_fresh.mp hy).1
    rcases Sym2.eq_iff.mp he' with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · -- the current node is not yet processed
      obtain ⟨i, hi, hiu⟩ := List.mem_take_iff_getElem.mp hu
      have := hnd.getElem_inj_iff.mp hiu
      omega
    · exact hy' (List.take_subset _ _ hu)
  · rw [block_of_ge hp]
    exact Finset.disjoint_empty_left _

/-! ### The search on the actual coins -/

/-- The observation process of the search on the coins `ω`: the open pairs of each block. -/
noncomputable def obs (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V))) (ω : Sym2 V → Bool) :
    Finset (Sym2 V) :=
  (block G (state G h s w₀ l)).filter fun e => ω e = true

/-- After processing a node, all its open neighbours are discovered. -/
lemma closed_state (s : V) (w₀ : ℝ) (ω : Sym2 V → Bool) (k : ℕ) :
    ∀ v ∈ (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k)).order.take
        (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k)).proc,
      ∀ y, (perc G ω).Adj v y → y ∈ (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k)).order := by
  induction k with
  | zero => intro v hv; simp [hist, state_nil] at hv
  | succ k ih =>
    have hστ : state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω (k + 1)) =
        update G h (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k))
          ((block G (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k))).filter
            fun e => ω e = true) := by
      simp only [hist, state_append, obs]
    rw [hστ]
    set τ := state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k) with hτ
    intro v hv y hadj
    by_cases hp : τ.proc < τ.order.length
    · rw [update_of_lt hp] at hv ⊢
      simp only at hv ⊢
      rw [List.take_append_of_le_length (by omega), List.take_add_one, List.mem_append] at hv
      rcases hv with hv | hv
      · exact List.mem_append_left _ (ih v hv y hadj)
      · rw [List.getElem?_eq_getElem hp, Option.toList_some, List.mem_singleton] at hv
        subst hv
        by_cases hyo : y ∈ τ.order
        · exact List.mem_append_left _ hyo
        · refine List.mem_append_right _ (Finset.mem_toList.mpr (mem_newV.mpr
            ⟨⟨hyo, hadj.1⟩, ?_⟩))
          rw [Finset.mem_filter, block_of_lt hp]
          exact ⟨Finset.mem_image.mpr ⟨y, mem_fresh.mpr ⟨hyo, hadj.1⟩, rfl⟩, hadj.2⟩
    · rw [update_of_ge hp] at hv ⊢
      exact ih v hv y hadj

/-! ### The potential and the supermartingale -/

/-- The potential of the search: discovered weight (root excluded) minus `c` times the weight of
the processed nodes. -/
noncomputable def pot (c : ℝ) (σ : State V) : ℝ :=
  (σ.order.tail.map σ.wt).sum - c * ((σ.order.take σ.proc).map σ.wt).sum

/-- The factor of the supermartingale after the history `l`, when the open pairs of the block
are `A`. -/
noncomputable def fac (θ c : ℝ) (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V)))
    (A : Finset (Sym2 V)) : ℝ :=
  if hp : (state G h s w₀ l).proc < (state G h s w₀ l).order.length then
    Real.exp (θ * (∑ e ∈ A, h e - c * (state G h s w₀ l).wt
      ((state G h s w₀ l).order[(state G h s w₀ l).proc])))
  else 1

lemma fac_nonneg (θ c : ℝ) (s : V) (w₀ : ℝ) (l : List (Finset (Sym2 V)))
    (A : Finset (Sym2 V)) : 0 ≤ fac (G := G) (h := h) θ c s w₀ l A := by
  unfold fac
  split_ifs
  · exact (Real.exp_pos _).le
  · exact zero_le_one

/-- The open pairs of the block are the pairs to the newly discovered nodes. -/
lemma image_newV {σ : State V} (hp : σ.proc < σ.order.length) {A : Finset (Sym2 V)}
    (hA : A ⊆ block G σ) :
    (newV G σ σ.order[σ.proc] A).image (fun y => s(σ.order[σ.proc], y)) = A := by
  ext e
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_newV.mp hy).2
  · intro he
    have he' := hA he
    rw [block_of_lt hp, Finset.mem_image] at he'
    obtain ⟨y, hy, rfl⟩ := he'
    exact ⟨y, mem_newV.mpr ⟨mem_fresh.mp hy, he⟩, rfl⟩

lemma pot_update {s : V} {w₀ c : ℝ} {σ : State V} (hσ : Inv (G := G) (h := h) s w₀ σ)
    (hp : σ.proc < σ.order.length) {A : Finset (Sym2 V)} (hA : A ⊆ block G σ) :
    pot c (update G h σ A) = pot c σ + (∑ e ∈ A, h e - c * σ.wt σ.order[σ.proc]) := by
  rw [update_of_lt hp]
  set v := σ.order[σ.proc]
  set N := newV G σ v A
  have hne : σ.order ≠ [] := List.ne_nil_of_mem (List.mem_of_getElem? hσ.head)
  have hwt : ∀ y ∈ σ.order, (if y ∈ N then h s(v, y) else σ.wt y) = σ.wt y := by
    intro y hy
    rw [if_neg fun hn => (mem_newV.mp hn).1.1 hy]
  have hvo : v ∈ σ.order := List.getElem_mem hp
  unfold pot
  simp only
  rw [List.tail_append_of_ne_nil hne, List.map_append, List.sum_append,
    List.map_congr_left fun y hy => hwt y (List.mem_of_mem_tail hy),
    List.take_append_of_le_length (by omega), List.take_add_one, List.map_append,
    List.sum_append, List.map_congr_left fun y hy => hwt y (List.mem_of_mem_take hy),
    List.getElem?_eq_getElem hp, Option.toList_some, List.map_singleton, List.sum_singleton,
    hwt v hvo, Finset.sum_map_toList]
  have hN : ∑ y ∈ N, (if y ∈ N then h s(v, y) else σ.wt y) = ∑ e ∈ A, h e := by
    rw [Finset.sum_congr rfl fun y hy => if_pos hy, ← image_newV hp hA,
      Finset.sum_image fun y _ y' _ hyy => Sym2.congr_right.mp hyy]
  rw [hN]
  ring

lemma pot_nil (c : ℝ) (s : V) (w₀ : ℝ) : pot c (state G h s w₀ []) = 0 := by
  simp [pot, state_nil]

/-- Along the search on the coins `ω`, the product of the factors is `exp (θ · potential)`. -/
lemma histProd_eq (θ c : ℝ) (s : V) (w₀ : ℝ) (ω : Sym2 V → Bool) (k : ℕ) :
    histProd (obs (G := G) (h := h) s w₀) (fac (G := G) (h := h) θ c s w₀) ω 0 k =
      Real.exp (θ * pot c (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k))) := by
  induction k with
  | zero => simp [histProd, hist, pot_nil]
  | succ k ih =>
    rw [histProd_zero_succ, ih]
    set l := hist (obs (G := G) (h := h) s w₀) ω k
    have hl : hist (obs (G := G) (h := h) s w₀) ω (k + 1) =
        l ++ [obs (G := G) (h := h) s w₀ l ω] := rfl
    rw [hl, state_append]
    by_cases hp : (state G h s w₀ l).proc < (state G h s w₀ l).order.length
    · have hA : obs (G := G) (h := h) s w₀ l ω ⊆ block G (state G h s w₀ l) :=
        Finset.filter_subset _ _
      rw [pot_update (inv_state s w₀ l) hp hA]
      unfold fac
      rw [dif_pos hp, ← Real.exp_add]
      congr 1
      simp only [obs]
      ring
    · rw [update_of_ge hp]
      unfold fac
      rw [dif_neg hp, mul_one]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The weights of the discovered nodes lie in `[wmin, wmax]`. -/
lemma wt_bounds {s : V} {w₀ wmin wmax : ℝ} {σ : State V} (hσ : Inv (G := G) (h := h) s w₀ σ)
    (hh : ∀ e, wmin ≤ h e ∧ h e ≤ wmax) (hw₀ : wmin ≤ w₀ ∧ w₀ ≤ wmax) :
    ∀ y ∈ σ.order, wmin ≤ σ.wt y ∧ σ.wt y ≤ wmax := by
  intro y hy
  by_cases hys : y = s
  · subst hys
    rw [hσ.root_wt]
    exact hw₀
  · obtain ⟨u, -, -, hw⟩ := hσ.parent y hy hys
    rw [hw]
    exact hh _

omit [Fintype V] [DecidableEq V] in
lemma length_mul_le_sum_map (l : List V) (wt : V → ℝ) {a : ℝ} (ha : ∀ y ∈ l, a ≤ wt y) :
    l.length * a ≤ (l.map wt).sum := by
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    have h1 := ha y (List.mem_cons_self ..)
    have h2 := ih fun z hz => ha z (List.mem_cons_of_mem _ hz)
    linarith

omit [Fintype V] [DecidableRel G.Adj] in
/-- Lower bound on the potential when `t` nodes are processed and `t + 1` discovered. -/
lemma pot_ge {s : V} {w₀ wmin wmax c : ℝ} {σ : State V} (hσ : Inv (G := G) (h := h) s w₀ σ)
    (hh : ∀ e, wmin ≤ h e ∧ h e ≤ wmax) (hw₀ : wmin ≤ w₀ ∧ w₀ ≤ wmax) (hwmin : 0 ≤ wmin)
    (hc1 : c ≤ 1) {t : ℕ} (hproc : σ.proc = t) (hlen : t + 1 ≤ σ.order.length) :
    (1 - c) * t * wmin - wmax ≤ pot c σ := by
  have hb := wt_bounds hσ hh hw₀
  have hnn : ∀ a ∈ σ.order.tail.map σ.wt, 0 ≤ a := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    exact hwmin.trans (hb y (List.mem_of_mem_tail hy)).1
  -- the discovered weight dominates the weight of the first `t + 1` nodes, root excluded
  have hpre : ((σ.order.take (t + 1)).tail.map σ.wt).sum ≤ (σ.order.tail.map σ.wt).sum := by
    refine List.Sublist.sum_le_sum ?_ hnn
    have htt : (σ.order.take (t + 1)).tail = σ.order.tail.take t := by
      cases σ.order <;> simp
    rw [htt]
    exact (List.take_sublist _ _).map _
  obtain ⟨y0, rest, hor⟩ : ∃ y0 rest, σ.order = y0 :: rest := by
    cases h' : σ.order with
    | nil => rw [h'] at hlen; simp at hlen
    | cons y0 rest => exact ⟨y0, rest, rfl⟩
  have hy0 : y0 ∈ σ.order := by rw [hor]; exact List.mem_cons_self ..
  have htake : σ.order.take (t + 1) = σ.order.take t ++ [σ.order[t]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
    rfl
  have hsplit : ((σ.order.take (t + 1)).map σ.wt).sum =
      ((σ.order.take (t + 1)).tail.map σ.wt).sum + σ.wt y0 := by
    rw [hor, List.take_succ_cons, List.tail_cons, List.map_cons, List.sum_cons]
    ring
  have hsplit' : ((σ.order.take (t + 1)).map σ.wt).sum =
      ((σ.order.take t).map σ.wt).sum + σ.wt σ.order[t] := by
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  have hS : t * wmin ≤ ((σ.order.take t).map σ.wt).sum := by
    have := length_mul_le_sum_map (σ.order.take t) σ.wt
      (a := wmin) fun y hy => (hb y (List.mem_of_mem_take hy)).1
    rwa [List.length_take, min_eq_left (by omega)] at this
  have hwt : wmin ≤ σ.wt σ.order[t] := (hb _ (List.getElem_mem _)).1
  have hw0 := (hb y0 hy0).2
  have hprod := mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr hc1)
  have hsum := hsplit.symm.trans hsplit'
  unfold pot
  rw [hproc]
  linarith

/-! ### The tail bound -/

/-- When the search is over (every discovered node processed), the discovered nodes contain the
cluster of the root. -/
lemma ncard_le_of_finished (s : V) (w₀ : ℝ) (ω : Sym2 V → Bool) (k : ℕ)
    (hfin : (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k)).proc =
      (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k)).order.length) :
    ((perc G ω).connectedComponentMk s).supp.ncard ≤
      (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k)).order.length := by
  set σ := state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω k) with hσ
  have hinv := inv_state (G := G) (h := h) s w₀ (hist (obs (G := G) (h := h) s w₀) ω k)
  have hcl := closed_state (G := G) (h := h) s w₀ ω k
  rw [← hσ, hfin, List.take_length] at hcl
  have hclosed : ∀ u ∈ σ.order.toFinset, ∀ v, (perc G ω).Adj u v → v ∈ σ.order.toFinset :=
    fun u hu v hadj => List.mem_toFinset.mpr (hcl u (List.mem_toFinset.mp hu) v hadj)
  have hs : s ∈ σ.order.toFinset := List.mem_toFinset.mpr (List.mem_of_getElem? hinv.head)
  have hsub : ((perc G ω).connectedComponentMk s).supp ⊆ (σ.order.toFinset : Set V) := by
    intro v hv
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hv
    obtain ⟨p⟩ := hv.symm
    exact mem_of_walk hclosed p hs
  calc _ ≤ (σ.order.toFinset : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = σ.order.toFinset.card := Set.ncard_coe_finset _
    _ ≤ σ.order.length := List.toFinset_card_le _

/-- A cluster with more than `t` nodes forces `t` processed and `t + 1` discovered nodes after
`t` steps. -/
lemma proc_eq_of_lt_ncard (s : V) (w₀ : ℝ) (ω : Sym2 V → Bool) (t : ℕ)
    (ht : t < ((perc G ω).connectedComponentMk s).supp.ncard) :
    (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω t)).proc = t ∧
      t + 1 ≤ (state G h s w₀ (hist (obs (G := G) (h := h) s w₀) ω t)).order.length := by
  have hle := (inv_state (G := G) (h := h) s w₀ (hist (obs (G := G) (h := h) s w₀) ω t)).proc_le
  have hfin := ncard_le_of_finished (G := G) (h := h) s w₀ ω t
  rcases proc_state (G := G) (h := h) s w₀ (hist (obs (G := G) (h := h) s w₀) ω t) with
    hp | ⟨hp, hpl⟩
  · rw [length_hist] at hp
    refine ⟨hp, ?_⟩
    by_contra hlt
    have := hfin (by omega)
    omega
  · rw [length_hist] at hp
    have := hfin hpl
    omega

/-- One step of the supermartingale: the factor has expectation at most `1`. -/
lemma expect_fac_le_one (r : Sym2 V → ℝ) (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    {wmax lam θ κ : ℝ} (hh0 : ∀ e, 0 ≤ h e) (hhmax : ∀ e, h e ≤ wmax) (hθ : 0 ≤ θ)
    (hθκ : θ * wmax ≤ κ - 1) (hκ2 : κ ≤ 2) (s : V) (w₀ : ℝ)
    (hstep : ∀ σ : State V, Inv (G := G) (h := h) s w₀ σ → ∀ hp : σ.proc < σ.order.length,
      ∑ y ∈ fresh G σ σ.order[σ.proc], r s(σ.order[σ.proc], y) * h s(σ.order[σ.proc], y) ≤
        lam * σ.wt σ.order[σ.proc])
    (l : List (Finset (Sym2 V))) :
    (Distribution.independent fun e => Distribution.bernoulli (r e) (hr0 e) (hr1 e)).expect
      (fun ω => fac (G := G) (h := h) θ (κ * lam) s w₀ l (obs (G := G) (h := h) s w₀ l ω)) ≤
      1 := by
  set σ := state G h s w₀ l with hσ
  by_cases hp : σ.proc < σ.order.length
  · set v := σ.order[σ.proc]
    have hκ1 : 1 ≤ κ := by nlinarith [hh0 s(v, v), hhmax s(v, v)]
    have hfac (ω : Sym2 V → Bool) : fac (G := G) (h := h) θ (κ * lam) s w₀ l
        (obs (G := G) (h := h) s w₀ l ω) = Real.exp (-(θ * (κ * lam) * σ.wt v)) *
          Real.exp (∑ e ∈ (block G σ).filter (fun e => ω e = true), θ * h e) := by
      unfold fac
      rw [dif_pos hp, ← Real.exp_add, ← Finset.mul_sum]
      congr 1
      simp only [obs]
      ring
    simp_rw [hfac, Distribution.expect_mul]
    rw [expect_exp_sum_open r hr0 hr1 (block G σ) fun e => θ * h e]
    have hprod : ∏ e ∈ block G σ, (1 - r e + r e * Real.exp (θ * h e)) ≤
        Real.exp (κ * θ * ∑ y ∈ fresh G σ v, r s(v, y) * h s(v, y)) := by
      calc ∏ e ∈ block G σ, (1 - r e + r e * Real.exp (θ * h e))
          ≤ ∏ e ∈ block G σ, Real.exp (κ * r e * (θ * h e)) := by
            refine Finset.prod_le_prod (fun e _ => ?_) fun e _ => ?_
            · nlinarith [hr0 e, hr1 e, Real.add_one_le_exp (θ * h e),
                mul_nonneg hθ (hh0 e)]
            · exact one_sub_add_mul_exp_le (hr0 e) (mul_nonneg hθ (hh0 e))
                ((mul_le_mul_of_nonneg_left (hhmax e) hθ).trans hθκ) hκ2
        _ = Real.exp (∑ e ∈ block G σ, κ * r e * (θ * h e)) := (Real.exp_sum _ _).symm
        _ = Real.exp (κ * θ * ∑ y ∈ fresh G σ v, r s(v, y) * h s(v, y)) := by
            rw [block_of_lt hp, Finset.sum_image fun y _ y' _ hyy => Sym2.congr_right.mp hyy,
              Finset.mul_sum]
            exact congrArg Real.exp (Finset.sum_congr rfl fun y _ => by ring)
    have hst := hstep σ (inv_state s w₀ l) hp
    calc Real.exp (-(θ * (κ * lam) * σ.wt v)) *
          ∏ e ∈ block G σ, (1 - r e + r e * Real.exp (θ * h e))
        ≤ Real.exp (-(θ * (κ * lam) * σ.wt v)) *
          Real.exp (κ * θ * ∑ y ∈ fresh G σ v, r s(v, y) * h s(v, y)) :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp (κ * θ * (∑ y ∈ fresh G σ v, r s(v, y) * h s(v, y) - lam * σ.wt v)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := by
          refine Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (by linarith) hθ) (by linarith))
      _ = 1 := Real.exp_zero
  · have hfac (ω : Sym2 V → Bool) : fac (G := G) (h := h) θ (κ * lam) s w₀ l
        (obs (G := G) (h := h) s w₀ l ω) = 1 := by
      unfold fac
      rw [dif_neg hp]
    simp_rw [hfac, Distribution.expect_const]
    rfl

/-- **Tail of the cluster size** (subcritical exploration with weights): with independent
Bernoulli(`r e`) coins, weights `h e ∈ [wmin, wmax]`, root weight `w₀ ∈ [wmin, wmax]`, and
expected weight discovered from every node of weight `w` at most `λ w` (`hstep`), the cluster of
`s` has more than `t` nodes with probability at most
`exp (-θ ((1 - κ λ) t wmin - wmax))`, for every `θ ≥ 0` and `κ ≤ 2` with `θ wmax ≤ κ - 1`. -/
theorem prob_cluster_gt_le (r : Sym2 V → ℝ) (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    {w₀ wmin wmax lam θ κ : ℝ} (hh : ∀ e, wmin ≤ h e ∧ h e ≤ wmax)
    (hw₀ : wmin ≤ w₀ ∧ w₀ ≤ wmax) (hwmin : 0 ≤ wmin) (hθ : 0 ≤ θ) (hθκ : θ * wmax ≤ κ - 1)
    (hκ2 : κ ≤ 2) (hc1 : κ * lam ≤ 1) (s : V)
    (hstep : ∀ σ : State V, Inv (G := G) (h := h) s w₀ σ → ∀ hp : σ.proc < σ.order.length,
      ∑ y ∈ fresh G σ σ.order[σ.proc], r s(σ.order[σ.proc], y) * h s(σ.order[σ.proc], y) ≤
        lam * σ.wt σ.order[σ.proc])
    (t : ℕ) :
    (Distribution.independent fun e => Distribution.bernoulli (r e) (hr0 e) (hr1 e)).prob
        (fun ω => t < ((perc G ω).connectedComponentMk s).supp.ncard) ≤
      Real.exp (-(θ * ((1 - κ * lam) * t * wmin - wmax))) := by
  set P := Distribution.independent fun e => Distribution.bernoulli (r e) (hr0 e) (hr1 e)
  set a := Real.exp (θ * ((1 - κ * lam) * t * wmin - wmax))
  have hh0 : ∀ e, 0 ≤ h e := fun e => hwmin.trans (hh e).1
  have hM : P.expect (fun ω => histProd (obs (G := G) (h := h) s w₀)
      (fac (G := G) (h := h) θ (κ * lam) s w₀) ω 0 t) ≤ 1 := by
    refine expect_prod_hist_le_one_of_fresh _ (obs (G := G) (h := h) s w₀)
      (fun l => block G (state G h s w₀ l)) (fun l ω ω' hag => ?_)
      (fun l => block_fresh s w₀ l) _ (fac_nonneg θ (κ * lam) s w₀)
      (fun l => expect_fac_le_one r hr0 hr1 hh0 (fun e => (hh e).2) hθ hθκ hκ2 s w₀ hstep l) t
    simp only [obs]
    exact Finset.filter_congr fun e he => by rw [hag e he]
  calc P.prob (fun ω => t < ((perc G ω).connectedComponentMk s).supp.ncard)
      ≤ P.prob (fun ω => a ≤ histProd (obs (G := G) (h := h) s w₀)
          (fac (G := G) (h := h) θ (κ * lam) s w₀) ω 0 t) := by
        refine Distribution.prob_mono _ fun ω hω => ?_
        obtain ⟨hproc, hlen⟩ := proc_eq_of_lt_ncard (G := G) (h := h) s w₀ ω t hω
        rw [histProd_eq]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (pot_ge (inv_state s w₀ _) hh hw₀ hwmin hc1 hproc hlen) hθ)
    _ ≤ P.expect (fun ω => histProd (obs (G := G) (h := h) s w₀)
          (fac (G := G) (h := h) θ (κ * lam) s w₀) ω 0 t) / a :=
        prob_le_expect_div P _ (fun ω => histProd_nonneg _ (fac_nonneg θ (κ * lam) s w₀) ω 0 t)
          (Real.exp_pos _)
    _ ≤ 1 / a := div_le_div_of_nonneg_right hM (Real.exp_pos _).le
    _ = _ := by rw [one_div, ← Real.exp_neg]

end Explore

end Epidemics
