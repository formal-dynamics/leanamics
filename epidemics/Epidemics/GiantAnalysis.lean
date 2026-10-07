import Epidemics.GiantDFS

/-! # Deterministic analysis of the depth-first search (EPI-3)

The deterministic half of the proofs of Krivelevich–Sudakov, Theorem 1, part 2, and Theorem 2
(*The phase transition in random graphs: a simple proof*, Random Structures & Algorithms 43
(2013), arXiv:1201.6529): consequences of the properties of the search (`Epidemics.GiantDFS`) for
an arbitrary sequence of answers `l`, with `X = l.count true` positive answers.

* `card_mul_card_le`: if all pairs between disjoint sets `A` and `B` have been queried, then
  `|A| |B|` is at most the number of queries.
* `three_mul_explored_lt`: "`|S| < n/3` at time `N₀`" (proof of Theorem 1): if `|S ∪ U|` reached
  `n / 3`, then at the first such time `|S| |T|` would exceed the number of queries.
* `le_length_stack`: "`|U| ≥ ε² n / 5`" (proof of Theorem 1): otherwise `|S| |T|` would exceed
  the number of queries.
* `exists_epoch_start`: the current epoch started at a time `τ` when `U` was empty, so the
  explored set `D` had all its pairs with `V ∖ D` queried (proof of Theorem 2).
* `exists_path_of_stack`, `card_comp_le_ncard`: on the edge coins `ω`, the stack is a path of
  `perc ⊤ ω` and the current epoch lies in one connected component.
-/

namespace Epidemics
namespace DFS
open Finset State

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `|S ∪ U|` after the answers `l`: the explored vertices. -/
noncomputable def explored (V : Type*) [Fintype V] [DecidableEq V] (l : List Bool) : ℕ :=
  ((ofAnswers V l).done ∪ (ofAnswers V l).stack.toFinset).card

omit [Fintype V] [DecidableEq V] in
/-- If all pairs between the disjoint sets `A` and `B` lie in `Q`, then `|A| |B| ≤ |Q|`. -/
lemma card_mul_card_le {A B : Finset V} (hAB : Disjoint A B) {Q : Finset (Sym2 V)}
    (h : ∀ a ∈ A, ∀ b ∈ B, s(a, b) ∈ Q) : A.card * B.card ≤ Q.card := by
  rw [← card_product]
  refine card_le_card_of_injOn (fun x => s(x.1, x.2)) (fun x hx => ?_) ?_
  · obtain ⟨ha, hb⟩ := mem_product.mp hx
    exact h _ ha _ hb
  · rintro ⟨a, b⟩ hx ⟨a', b'⟩ hx' heq
    simp only [coe_product, Set.mem_prod, mem_coe] at hx hx'
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hx'.2 (disjoint_left.mp hAB hx.1)

lemma card_unvisited (s : State V) :
    s.unvisited.card = Fintype.card V - (s.done ∪ s.stack.toFinset).card := by
  rw [unvisited, card_univ_sdiff]

lemma explored_le (l : List Bool) : explored V l ≤ Fintype.card V := card_le_univ _

lemma card_done_add_length (l : List Bool) :
    (ofAnswers V l).done.card + (ofAnswers V l).stack.length = explored V l := by
  have hs := inv_ofAnswers (V := V) l
  rw [explored, card_union_of_disjoint hs.disj, List.toFinset_card_of_nodup hs.nodup]

/-- `explored` grows along prefixes. -/
lemma explored_take_le (l : List Bool) (j : ℕ) : explored V (l.take j) ≤ explored V l := by
  have h := card_le_card (le_ofAnswers_take (V := V) l j).unvisited
  rw [card_unvisited, card_unvisited] at h
  have h1 := explored_le (V := V) l
  have h2 := explored_le (V := V) (l.take j)
  simp only [explored] at *
  omega

/-- `|S| |T|` is at most the number of queries. -/
lemma card_done_mul_card_unvisited_le (l : List Bool) (hl : l.length ≤ (Fintype.card V).choose 2) :
    (ofAnswers V l).done.card * (ofAnswers V l).unvisited.card ≤ l.length := by
  rw [← card_queried_ofAnswers hl]
  refine card_mul_card_le (disjoint_left.mpr fun a ha hb => (mem_unvisited.mp hb).1 ha) ?_
  exact fun a ha b hb => (queried_of_mem_done_of_mem_unvisited l ha hb).1

lemma count_take_le (l : List Bool) (j : ℕ) : (l.take j).count true ≤ l.count true :=
  (List.take_sublist j l).count_le true

/-- **`|S ∪ U| < n/3` at time `|l|`** (Krivelevich–Sudakov, proof of Theorem 1): at the first time
when `3 |S ∪ U| ≥ n`, we have `|S ∪ U| ≤ (n + 5)/3` (it grows by at most `2` per query), so
`|S| ≥ n/3 - 1 - X` and `|T| ≥ (2n - 5)/3`, and all the pairs between `S` and `T` have been
queried. -/
theorem three_mul_explored_lt (l : List Bool) (hl : l.length ≤ (Fintype.card V).choose 2)
    (hn : 4 ≤ Fintype.card V)
    (h : (l.length : ℝ) <
      ((Fintype.card V : ℝ) / 3 - 1 - l.count true) * ((2 * Fintype.card V - 5) / 3)) :
    3 * explored V l < Fintype.card V := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∃ t, t ≤ l.length ∧ Fintype.card V ≤ 3 * explored V (l.take t) :=
    ⟨l.length, le_rfl, by rwa [List.take_length]⟩
  obtain ⟨ht₀l, ht₀⟩ := Nat.find_spec hex
  have hmin := fun t (ht : t < Nat.find hex) => Nat.find_min hex ht
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, List.take_zero] at ht₀
    have := card_union_nil_le (V := V)
    simp only [explored] at ht₀
    omega
  obtain ⟨t, ht⟩ : ∃ t, Nat.find hex = t + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ht] at ht₀l ht₀
  have hprev : 3 * explored V (l.take t) < Fintype.card V := by
    have := hmin t (by omega)
    push Not at this
    exact this (by omega)
  have hstep : explored V (l.take (t + 1)) ≤ explored V (l.take t) + 2 := by
    rw [List.take_succ_eq_append_getElem (by omega)]
    exact card_union_append_le _ _
  have hlen : (l.take (t + 1)).length = t + 1 := by simp; omega
  have hST := card_done_mul_card_unvisited_le (V := V) (l.take (t + 1)) (by omega)
  rw [hlen, card_unvisited] at hST
  have hSU := card_done_add_length (V := V) (l.take (t + 1))
  have hU := length_stack_le (V := V) (l.take (t + 1))
  have hX := count_take_le l (t + 1)
  have hexle := explored_le (V := V) (l.take (t + 1))
  simp only [explored] at hSU hexle ht₀ hstep hprev
  set a := ((ofAnswers V (l.take (t + 1))).done ∪
    (ofAnswers V (l.take (t + 1))).stack.toFinset).card
  set S := (ofAnswers V (l.take (t + 1))).done.card
  set n := Fintype.card V
  -- real arithmetic
  have hSr : (n : ℝ) / 3 - 1 - l.count true ≤ S := by
    have h1 : (S : ℝ) + (ofAnswers V (l.take (t + 1))).stack.length = a := by exact_mod_cast hSU
    have h2 : ((ofAnswers V (l.take (t + 1))).stack.length : ℝ) ≤
        1 + (l.take (t + 1)).count true := by exact_mod_cast hU
    have h3 : ((l.take (t + 1)).count true : ℝ) ≤ l.count true := by exact_mod_cast hX
    have h4 : (n : ℝ) ≤ 3 * a := by exact_mod_cast ht₀
    linarith
  have hTr : (2 * (n : ℝ) - 5) / 3 ≤ ((n - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub hexle]
    have : (3 * a : ℝ) ≤ n + 5 := by exact_mod_cast (by omega : 3 * a ≤ n + 5)
    linarith
  have hprod : (S : ℝ) * ((n - a : ℕ) : ℝ) ≤ l.length := by
    have : S * (n - a) ≤ l.length := by omega
    exact_mod_cast this
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt ((n : ℝ) / 3 - 1 - l.count true) 0 with hneg | hpos'
  · have : ((n : ℝ) / 3 - 1 - l.count true) * ((2 * n - 5) / 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (by linarith)
    have : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    linarith
  · have := mul_le_mul hSr hTr (by linarith) (Nat.cast_nonneg _)
    linarith

/-- **A long stack** (Krivelevich–Sudakov, proof of Theorem 1): if `3 |S ∪ U| < n`, the number of
positive answers is at least `Xlo ≥ L`, and both `(Xlo - L)(n - Xlo)` and `(n/3 - L)(2n/3)`
exceed the number of queries, then `|U| ≥ L`. (Otherwise `|S| ≥ |S ∪ U| - L` with
`Xlo ≤ |S ∪ U| < n/3`, and by concavity `|S| |T|` would exceed the number of queries.) -/
theorem le_length_stack (l : List Bool) (hl : l.length ≤ (Fintype.card V).choose 2)
    (h3 : 3 * explored V l < Fintype.card V) {Xlo L : ℝ} (hX : Xlo ≤ l.count true)
    (hL : L ≤ Xlo)
    (h1 : (l.length : ℝ) < (Xlo - L) * (Fintype.card V - Xlo))
    (h2 : (l.length : ℝ) < (Fintype.card V / 3 - L) * (2 * Fintype.card V / 3)) :
    L ≤ (ofAnswers V l).stack.length := by
  have h1' := h1
  have h2' := h2
  by_contra hU
  push Not at hU
  have hST := card_done_mul_card_unvisited_le (V := V) l hl
  rw [card_unvisited] at hST
  have hSU := card_done_add_length (V := V) l
  have hexle := explored_le (V := V) l
  have hT : (ofAnswers V l).unvisited.Nonempty := by
    rw [← card_pos, card_unvisited]
    simp only [explored] at h3
    omega
  have hXa := count_true_le_card (V := V) l hT
  simp only [explored] at hSU hexle h3
  set a := ((ofAnswers V l).done ∪ (ofAnswers V l).stack.toFinset).card
  set S := (ofAnswers V l).done.card
  set n := Fintype.card V
  have hSU' : (S : ℝ) + (ofAnswers V l).stack.length = a := by exact_mod_cast hSU
  have ha : (3 * a : ℝ) < n := by exact_mod_cast h3
  have hXa' : ((l.count true : ℕ) : ℝ) ≤ a := by exact_mod_cast hXa
  have hprod : (S : ℝ) * (n - a) ≤ l.length := by
    have : S * (n - a) ≤ l.length := hST
    have h' : ((S * (n - a) : ℕ) : ℝ) ≤ l.length := by exact_mod_cast this
    rwa [Nat.cast_mul, Nat.cast_sub hexle] at h'
  have haX : Xlo ≤ a := hX.trans hXa'
  have hS : (a : ℝ) - L ≤ S := by linarith
  have hgS : ((a : ℝ) - L) * (n - a) ≤ S * (n - a) :=
    mul_le_mul_of_nonneg_right hS (by linarith)
  -- concavity of `x ↦ (x - L)(n - x)` on `[Xlo, n/3]`
  have hg : (l.length : ℝ) < ((a : ℝ) - L) * (n - a) := by
    rcases le_or_gt ((a : ℝ) + Xlo) (n + L) with hc | hc
    · have : ((a : ℝ) - L) * (n - a) - (Xlo - L) * (n - Xlo) = (a - Xlo) * (n + L - a - Xlo) := by
        ring
      have : 0 ≤ ((a : ℝ) - Xlo) * (n + L - a - Xlo) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    · have : ((a : ℝ) - L) * (n - a) - (n / 3 - L) * (2 * n / 3) =
          (a - n / 3) * (n + L - a - n / 3) := by ring
      have : 0 ≤ ((a : ℝ) - n / 3) * (n + L - a - n / 3) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      linarith [h2']
  linarith

/-- **The start of the current epoch** (Krivelevich–Sudakov, proof of Theorem 2): there is a time
`τ ≤ |l|` such that the positive answers after `τ` all lie in the current epoch and, unless
`τ = 0`, at time `τ` an explored set `D` with `|D| ≥ ∑_{i<τ} Xᵢ`, `|D| ≤ |S ∪ U|` had all its pairs
with `V ∖ D` queried, so that `|D| (n - |D|) ≤ τ`. -/
theorem exists_epoch_start (l : List Bool) (hl : l.length ≤ (Fintype.card V).choose 2)
    (hT : (ofAnswers V l).unvisited.Nonempty) :
    ∃ τ ≤ l.length, (l.drop τ).count true ≤ (ofAnswers V l).comp.card ∧
      (τ = 0 ∨ ∃ d : ℕ, (l.take τ).count true ≤ d ∧ d ≤ explored V l ∧
        d * (Fintype.card V - d) ≤ τ) := by
  classical
  have hex : ∃ j, j ≤ l.length ∧ (ofAnswers V (l.take j)).epochs = (ofAnswers V l).epochs :=
    ⟨l.length, le_rfl, by rw [List.take_length]⟩
  obtain ⟨hτl, hτ⟩ := Nat.find_spec hex
  set τ := Nat.find hex with hτdef
  refine ⟨τ, hτl, ?_, ?_⟩
  · have := count_drop_le_card_comp l hτl hτ hT
    omega
  · rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · exact Or.inl h0
    · right
      obtain ⟨t, ht⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
      have hmin := Nat.find_min hex (show t < τ by omega)
      have htl : t < l.length := by omega
      have hlt : (ofAnswers V (l.take t)).epochs < (ofAnswers V (l.take t ++ [l[t]])).epochs := by
        rw [← List.take_succ_eq_append_getElem htl, ← ht, hτ]
        have := (le_ofAnswers_take (V := V) l t).epochs
        push Not at hmin
        exact lt_of_le_of_ne this (hmin (by omega))
      obtain ⟨D, hDS, hDX, hDQ⟩ := exists_of_epochs_lt _ _ hlt
      rw [← List.take_succ_eq_append_getElem htl, ← ht] at hDS hDX hDQ
      refine ⟨D.card, hDX, ?_, ?_⟩
      · calc D.card ≤ (ofAnswers V (l.take τ)).done.card := card_le_card hDS
          _ ≤ explored V (l.take τ) := card_le_card subset_union_left
          _ ≤ explored V l := explored_take_le l τ
      · have hlen : (l.take τ).length = τ := by simp; omega
        rw [← card_univ_sdiff, ← hlen, ← card_queried_ofAnswers (V := V) (by simp; omega)]
        exact card_mul_card_le disjoint_sdiff
          fun a ha c hc => hDQ a ha c (mem_sdiff.mp hc).2

/-- **A large epoch** (Krivelevich–Sudakov, proof of Theorem 2): suppose `3 |S ∪ U| < n`, at
least `(1 - δ) t p` of the first `t` answers are positive for every `t₁ ≤ t ≤ |l|`, and
`(1 - δ) p (n - |l| p) > 1`. Then the current epoch started by time `t₁` (an earlier start at time
`τ > t₁` would give an explored set `D` with `(1 - δ) τ p ≤ |D| < n/3` and
`|D| (n - |D|) ≤ τ < (1 - δ) τ p (n - |l| p)`), so it contains all the positive answers after
`t₁`. -/
theorem le_card_comp (l : List Bool) (hl : l.length ≤ (Fintype.card V).choose 2)
    (h3 : 3 * explored V l < Fintype.card V) {t₁ : ℕ} {p δ : ℝ} (hp : 0 ≤ p) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1)
    (hlow : ∀ t, t₁ ≤ t → t ≤ l.length → (1 - δ) * (t * p) ≤ ((l.take t).count true : ℝ))
    (hcontr : 1 < (1 - δ) * p * (Fintype.card V - l.length * p)) :
    (l.count true : ℝ) - (l.take t₁).count true ≤ (ofAnswers V l).comp.card := by
  have hexle := explored_le (V := V) l
  have hT : (ofAnswers V l).unvisited.Nonempty := by
    rw [← card_pos, card_unvisited]
    simp only [explored] at h3
    omega
  obtain ⟨τ, hτl, hdrop, hτ⟩ := exists_epoch_start l hl hT
  have hτt₁ : τ ≤ t₁ := by
    by_contra hlt
    push Not at hlt
    rcases hτ with h0 | ⟨d, hXd, hdex, hdτ⟩
    · omega
    · have hXτ := hlow τ hlt.le hτl
      set n := Fintype.card V
      have hdn : d ≤ n := hdex.trans hexle
      have hd3 : (3 * d : ℝ) < n := by exact_mod_cast (by omega : 3 * d < n)
      have hdτ' : (d : ℝ) * (n - d) ≤ τ := by
        have h' : ((d * (n - d) : ℕ) : ℝ) ≤ τ := by exact_mod_cast hdτ
        rwa [Nat.cast_mul, Nat.cast_sub hdn] at h'
      have hXd' : ((l.take τ).count true : ℝ) ≤ d := by exact_mod_cast hXd
      set d₀ := (1 - δ) * (τ * p) with hd₀def
      have hd₀ : d₀ ≤ d := hXτ.trans hXd'
      have hd₀nn : 0 ≤ d₀ := mul_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg _) hp)
      have hd₀L : d₀ ≤ l.length * p := by
        have hτp : (τ : ℝ) * p ≤ l.length * p :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hτl) hp
        have : d₀ ≤ τ * p := by
          rw [hd₀def]
          nlinarith [mul_nonneg (Nat.cast_nonneg τ) hp]
        linarith
      have hτpos : (0 : ℝ) < τ := by exact_mod_cast (by omega : 0 < τ)
      have hA : d₀ * (n - d₀) ≤ d * (n - d) := by
        have : 0 ≤ (d - d₀) * (n - d - d₀) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hB : d₀ * (n - l.length * p) ≤ d₀ * (n - d₀) :=
        mul_le_mul_of_nonneg_left (by linarith) hd₀nn
      have hC : (τ : ℝ) < d₀ * (n - l.length * p) := by
        have : d₀ * (n - l.length * p) = τ * ((1 - δ) * p * (n - l.length * p)) := by
          rw [hd₀def]; ring
        rw [this]
        nlinarith
      linarith
  have hsplit : l.count true = (l.take τ).count true + (l.drop τ).count true := by
    rw [← List.count_append, List.take_append_drop]
  have hmono : (l.take τ).count true ≤ (l.take t₁).count true := by
    have : l.take τ = (l.take t₁).take τ := by rw [List.take_take, min_eq_left hτt₁]
    rw [this]
    exact count_take_le _ _
  have h1 : ((l.drop τ).count true : ℝ) ≤ (ofAnswers V l).comp.card := by exact_mod_cast hdrop
  have h2 : (l.count true : ℝ) = (l.take τ).count true + (l.drop τ).count true := by
    exact_mod_cast hsplit
  have h3' : ((l.take τ).count true : ℝ) ≤ (l.take t₁).count true := by exact_mod_cast hmono
  linarith

/-! ### On the edge coins -/

section Coins

variable (e₀ : Sym2 V) (ω : Sym2 V → Bool) (t : ℕ)

/-- The found pairs are open edges of `perc ⊤ ω`. -/
lemma adj_of_mem_found {u v : V}
    (h : s(u, v) ∈ (ofAnswers V (queryAnswers (nextQuery e₀) ω t)).found) :
    (perc ⊤ ω).Adj u v := by
  have hq := found_subset_queried _ h
  refine ⟨?_, (mem_found_iff_of_queryAnswers e₀ ω t hq).mp h⟩
  rw [SimpleGraph.top_adj]
  rintro rfl
  exact not_isDiag_of_mem_queried _ hq (Sym2.mk_isDiag_iff.mpr rfl)

lemma fromEdgeSet_found_le :
    SimpleGraph.fromEdgeSet ((ofAnswers V (queryAnswers (nextQuery e₀) ω t)).found :
      Set (Sym2 V)) ≤ perc ⊤ ω := by
  intro u v huv
  rw [SimpleGraph.fromEdgeSet_adj] at huv
  exact adj_of_mem_found e₀ ω t huv.1

omit [Fintype V] [DecidableEq V] in
/-- A chain of adjacent vertices is the support of a walk. -/
lemma exists_walk_of_isChain {G : SimpleGraph V} :
    ∀ (a : V) (L : List V), (a :: L).IsChain G.Adj →
      ∃ (b : V) (q : G.Walk a b), q.support = a :: L
  | a, [], _ => ⟨a, SimpleGraph.Walk.nil, rfl⟩
  | a, c :: L, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨b, q, hq⟩ := exists_walk_of_isChain c L h.2
    exact ⟨b, SimpleGraph.Walk.cons h.1 q, by simp [hq]⟩

/-- **The stack is a path** of `perc ⊤ ω` with `|U| - 1` edges. -/
theorem exists_path_of_stack (hne : (ofAnswers V (queryAnswers (nextQuery e₀) ω t)).stack ≠ []) :
    ∃ (u v : V) (q : (perc ⊤ ω).Walk u v), q.IsPath ∧
      q.length + 1 = (ofAnswers V (queryAnswers (nextQuery e₀) ω t)).stack.length := by
  obtain ⟨a, L, hL⟩ := List.exists_cons_of_ne_nil hne
  have hch := stack_chain_ofAnswers (V := V) (queryAnswers (nextQuery e₀) ω t)
  have hnd := (disjoint_done_stack (V := V) (queryAnswers (nextQuery e₀) ω t)).2
  rw [hL] at hch hnd
  have hch' : (a :: L).IsChain (perc ⊤ ω).Adj :=
    hch.imp fun u v h => adj_of_mem_found e₀ ω t h
  obtain ⟨b, q, hq⟩ := exists_walk_of_isChain a L hch'
  refine ⟨a, b, q, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, hq]; exact hnd
  · rw [hL, ← hq, SimpleGraph.Walk.length_support]

/-- **The current epoch lies in one connected component** of `perc ⊤ ω`. -/
theorem card_comp_le_ncard {u : V} (hu : u ∈ (ofAnswers V (queryAnswers (nextQuery e₀) ω t)).comp) :
    (ofAnswers V (queryAnswers (nextQuery e₀) ω t)).comp.card ≤
      ((perc ⊤ ω).connectedComponentMk u).supp.ncard := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun w hw => ?_) (Set.toFinite _)
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
  exact ((reachable_of_mem_comp _ hu hw).mono (fromEdgeSet_found_le e₀ ω t)).symm

end Coins

end DFS
end Epidemics
