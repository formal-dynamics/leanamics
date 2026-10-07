import Epidemics.ReedFrost
import Dynamics.Chernoff
import Dynamics.DriftHittingAux

/-! # Independent edge coins: deferred decisions and symmetry (EPI-3)

Facts about finite distributions and the i.i.d. Bernoulli(`p`) coins `coins p` of
`Epidemics.ReedFrost`, used in the proof of the supercritical giant component (Krivelevich–Sudakov,
*The phase transition in random graphs: a simple proof*, Random Structures & Algorithms 43 (2013),
arXiv:1201.6529).

* **Elementary bounds** on `Distribution.prob`: monotonicity, complement, union bounds.
* **Cylinders**: the probability that the independent coordinates `c 0, …, c (m-1)` (distinct)
  take prescribed values is the product of their weights (`prob_forall_eval_eq`).
* **Principle of deferred decisions.** Krivelevich and Sudakov run the depth-first search "fed with
  a sequence of i.i.d. Bernoulli(`p`) random variables `X̄`" and observe that "the so obtained graph
  is clearly distributed according to `G(n, p)`" (Section 2). Here the coins come first: an adaptive
  strategy queries the coordinates of `ω : ι → Bool` one at a time, the next coordinate being a
  function of the answers so far. As long as no coordinate is queried twice, the answers are
  i.i.d. Bernoulli(`p`) (`expect_queryAnswers`, `prob_queryAnswers`). The proof: the answers equal
  a given list `L` iff the coordinates queried along `L`, which are determined by `L`, take the
  values of `L`, a cylinder event.
* **Symmetry**: relabelling the vertices does not change the law of the coins (`coins_prob_perm`).

`coins` is built from `Epidemics.bernoulli`, which coincides with the coin
`Dynamics.Distribution.bernoulli` of the Chernoff bounds (FND-3): `coins_eq_independent`.
-/

namespace Epidemics
open Finset Dynamics

/-- The edge coins are the independent Bernoulli coins of the Chernoff bounds (FND-3). -/
lemma coins_eq_independent {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) (h0 : 0 ≤ p)
    (h1 : p ≤ 1) :
    coins (V := V) p h0 h1 = Distribution.independent fun _ => Distribution.bernoulli p h0 h1 :=
  rfl

/-! ### Elementary bounds on probabilities

Monotonicity and the expectation form of `prob` are the core's `Distribution.prob_mono` and
`Distribution.prob_eq_expect`. The bounds below are not in `dynamics/` yet (their move there is
tracked in issue #42). -/

section Prob

variable {α : Type*} [Fintype α]

lemma prob_congr (P : Distribution α) {A B : α → Prop} (h : ∀ a, A a ↔ B a) :
    P.prob A = P.prob B :=
  le_antisymm (P.prob_mono fun a => (h a).1) (P.prob_mono fun a => (h a).2)

lemma prob_not (P : Distribution α) (A : α → Prop) :
    P.prob (fun a => ¬A a) = 1 - P.prob A := by
  classical
  rw [P.prob_eq_expect, P.prob_eq_expect, ← P.expect_const 1, ← Distribution.expect_sub]
  congr 1
  funext a
  by_cases hA : A a <;> simp [hA]

lemma prob_or_le (P : Distribution α) (A B : α → Prop) :
    P.prob (fun a => A a ∨ B a) ≤ P.prob A + P.prob B := by
  classical
  rw [P.prob_eq_expect, P.prob_eq_expect, P.prob_eq_expect, ← Distribution.expect_add]
  refine P.expect_mono fun a => ?_
  by_cases hA : A a <;> by_cases hB : B a <;> simp [hA, hB]

lemma prob_exists_le_sum {ι : Type*} (P : Distribution α) (s : Finset ι) (A : ι → α → Prop) :
    P.prob (fun a => ∃ i ∈ s, A i a) ≤ ∑ i ∈ s, P.prob (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Distribution.prob]
  | insert i s hi ih =>
    rw [sum_insert hi]
    calc P.prob (fun a => ∃ j ∈ insert i s, A j a)
        = P.prob (fun a => A i a ∨ ∃ j ∈ s, A j a) := prob_congr P fun a => by simp
      _ ≤ P.prob (A i) + P.prob (fun a => ∃ j ∈ s, A j a) := prob_or_le P _ _
      _ ≤ P.prob (A i) + ∑ j ∈ s, P.prob (A j) := by linarith

/-- If `B` fails with probability at most `ε` and implies `A`, then `A` has probability at least
`1 - ε`. -/
lemma one_sub_le_prob (P : Distribution α) {A B : α → Prop} (h : ∀ a, B a → A a) {ε : ℝ}
    (hB : P.prob (fun a => ¬B a) ≤ ε) : 1 - ε ≤ P.prob A := by
  rw [prob_not] at hB
  linarith [Distribution.prob_mono P h]

end Prob

/-! ### Cylinders -/

/-- **Cylinders**: if the coordinates `c 0, …, c (m-1)` are distinct, the probability that they
take the values `x 0, …, x (m-1)` under an independent product is the product of the weights. -/
theorem prob_forall_eval_eq {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → Distribution α) {m : ℕ} {c : Fin m → ι} (hc : Function.Injective c)
    (x : Fin m → α) :
    (Distribution.independent P).prob (fun ω => ∀ k, ω (c k) = x k) =
      ∏ k, (P (c k)).weight (x k) := by
  classical
  -- the indicator of the cylinder is a product over the coordinates
  set ψ : ι → α → ℝ := fun i a => ∏ k ∈ univ.filter (fun k => c k = i),
    if a = x k then 1 else 0 with hψ
  have hind (ω : ι → α) : (if ∀ k, ω (c k) = x k then (1 : ℝ) else 0) = ∏ i, ψ i (ω i) := by
    rw [hψ]
    simp only
    rw [show (∏ i, ∏ k ∈ univ.filter (fun k => c k = i), if ω i = x k then (1 : ℝ) else 0) =
        ∏ i, ∏ k ∈ univ.filter (fun k => c k = i), if ω (c k) = x k then (1 : ℝ) else 0 from
      prod_congr rfl fun i _ => prod_congr rfl fun k hk => by
        rw [(mem_filter.mp hk).2]]
    rw [prod_fiberwise univ c (fun k => if ω (c k) = x k then (1 : ℝ) else 0), prod_boole]
    simp
  have hfib (i : ι) : (P i).expect (ψ i) = ∏ k ∈ univ.filter (fun k => c k = i),
      (P (c k)).weight (x k) := by
    rcases (univ.filter fun k => c k = i).eq_empty_or_nonempty with h | ⟨k, hk⟩
    · simp [hψ, h, (P i).expect_const]
    · have hs : univ.filter (fun k => c k = i) = {k} := by
        refine eq_singleton_iff_unique_mem.mpr ⟨hk, fun k' hk' => hc ?_⟩
        rw [(mem_filter.mp hk').2, (mem_filter.mp hk).2]
      have hki : c k = i := (mem_filter.mp hk).2
      simp only [hψ, hs, prod_singleton, Distribution.expect, mul_ite, mul_one, mul_zero,
        sum_ite_eq', mem_univ, if_true, hki]
  rw [Distribution.prob_eq_expect]
  simp_rw [hind]
  rw [Distribution.independent_expect_prod]
  simp_rw [hfib]
  exact prod_fiberwise univ c fun k => (P (c k)).weight (x k)

/-! ### Adaptive queries -/

section Deferred

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The answers to the first `t` queries of the adaptive strategy `next` on the coins `ω`, in
order: after the answers `l`, the next query is the coordinate `next l`. -/
def queryAnswers (next : List Bool → ι) (ω : ι → Bool) : ℕ → List Bool
  | 0 => []
  | t + 1 => queryAnswers next ω t ++ [ω (next (queryAnswers next ω t))]

/-- The strategy `next` never queries a coordinate twice among its first `m` queries: after any
`k < m` answers, the next coordinate differs from the `k` coordinates queried before. -/
def FreshUpTo (next : List Bool → ι) (m : ℕ) : Prop :=
  ∀ l : List Bool, l.length < m → ∀ j < l.length, next (l.take j) ≠ next l

omit [Fintype ι] [DecidableEq ι] in
lemma FreshUpTo.mono {next : List Bool → ι} {m m' : ℕ} (h : FreshUpTo next m) (hm : m' ≤ m) :
    FreshUpTo next m' :=
  fun l hl => h l (lt_of_lt_of_le hl hm)

omit [Fintype ι] [DecidableEq ι] in
lemma length_queryAnswers (next : List Bool → ι) (ω : ι → Bool) (t : ℕ) :
    (queryAnswers next ω t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [queryAnswers, ih]

omit [Fintype ι] [DecidableEq ι] in
lemma take_queryAnswers (next : List Bool → ι) (ω : ι → Bool) {s t : ℕ} (hst : s ≤ t) :
    (queryAnswers next ω t).take s = queryAnswers next ω s := by
  induction t with
  | zero => obtain rfl : s = 0 := Nat.le_zero.mp hst; rfl
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with h | h
    · rw [queryAnswers, List.take_append_of_le_length (by simp [length_queryAnswers]; omega),
        ih (by omega)]
    · obtain rfl : s = t + 1 := le_antisymm hst h
      exact List.take_of_length_le (by simp [length_queryAnswers])

omit [Fintype ι] [DecidableEq ι] in
/-- The answers are a given list `L` iff the coordinates queried along `L` take its values. -/
lemma queryAnswers_eq_iff (next : List Bool → ι) (ω : ι → Bool) (L : List Bool) :
    queryAnswers next ω L.length = L ↔
      ∀ k < L.length, some (ω (next (L.take k))) = L[k]? := by
  induction L using List.reverseRecOn with
  | nil => simp [queryAnswers]
  | append_singleton L b ih =>
    rw [List.length_append, List.length_singleton, queryAnswers]
    constructor
    · intro h
      have hL : queryAnswers next ω L.length = L :=
        (List.append_inj h (by simp [length_queryAnswers])).1
      have hb : ω (next (queryAnswers next ω L.length)) = b := by
        simpa using (List.append_inj h (by simp [length_queryAnswers])).2
      rw [hL] at hb
      intro k hk
      rcases Nat.lt_or_ge k L.length with hkL | hkL
      · rw [List.take_append_of_le_length hkL.le, List.getElem?_append_left hkL]
        exact (ih.mp hL) k hkL
      · obtain rfl : k = L.length := by omega
        simp [hb]
    · intro h
      have hL : queryAnswers next ω L.length = L := ih.mpr fun k hk => by
        have := h k (by omega)
        rwa [List.take_append_of_le_length hk.le, List.getElem?_append_left hk] at this
      have hb : ω (next L) = b := by simpa using h L.length (by simp)
      rw [hL, hb]

/-- The answers to a fresh strategy form a cylinder: they equal `L` with probability
`∏ₖ w(Lₖ)`. -/
lemma prob_queryAnswers_eq (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (next : List Bool → ι) {m : ℕ}
    (hfresh : FreshUpTo next m) (x : Fin m → Bool) :
    (Distribution.independent fun _ : ι => Distribution.bernoulli p h0 h1).prob
        (fun ω => queryAnswers next ω m = List.ofFn x) =
      ∏ k, (Distribution.bernoulli p h0 h1).weight (x k) := by
  have hinj : Function.Injective fun k : Fin m => next ((List.ofFn x).take k) := by
    intro j k hjk
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
    · refine hfresh ((List.ofFn x).take k) (by simp) j (by simpa using h) ?_
      rwa [List.take_take, min_eq_left h.le]
    · refine hfresh ((List.ofFn x).take j) (by simp) k (by simpa using h) ?_
      rw [List.take_take, min_eq_left h.le]
      exact hjk.symm
  rw [← prob_forall_eval_eq (fun _ => Distribution.bernoulli p h0 h1) hinj x]
  refine prob_congr _ fun ω => ?_
  have := queryAnswers_eq_iff next ω (List.ofFn x)
  rw [List.length_ofFn] at this
  rw [this]
  constructor
  · intro h k
    simpa using h k k.2
  · intro h k hk
    simpa [hk] using h ⟨k, hk⟩

/-- **Principle of deferred decisions** (the coupling behind Krivelevich–Sudakov, Section 2): if
the strategy `next` is fresh for `m` queries, its first `m` answers on i.i.d. Bernoulli(`p`) coins
are distributed as `m` i.i.d. Bernoulli(`p`) trials. -/
theorem expect_queryAnswers (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (next : List Bool → ι) {m : ℕ}
    (hfresh : FreshUpTo next m) (F : List Bool → ℝ) :
    (Distribution.independent fun _ : ι => Distribution.bernoulli p h0 h1).expect
        (fun ω => F (queryAnswers next ω m)) =
      (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).expect
        (fun x => F (List.ofFn x)) := by
  classical
  -- decompose along the (unique) list of answers
  have hdec (ω : ι → Bool) : F (queryAnswers next ω m) =
      ∑ x : Fin m → Bool, F (List.ofFn x) *
        (if queryAnswers next ω m = List.ofFn x then (1 : ℝ) else 0) := by
    have hlen := length_queryAnswers next ω m
    set x₀ : Fin m → Bool := fun k => (queryAnswers next ω m)[k.1]'(by rw [hlen]; exact k.2)
    have hx₀ : List.ofFn x₀ = queryAnswers next ω m := by
      apply List.ext_getElem (by simp [hlen])
      intro k h₁ h₂
      simp [x₀]
    rw [sum_eq_single x₀]
    · rw [hx₀]; simp
    · intro x _ hx
      rw [if_neg, mul_zero]
      intro h
      exact hx (List.ofFn_injective (h.symm.trans hx₀.symm))
    · simp
  simp_rw [hdec]
  rw [Distribution.expect_sum]
  simp only [Distribution.expect_mul, ← Distribution.prob_eq_expect]
  simp only [prob_queryAnswers_eq p h0 h1 next hfresh]
  rw [Distribution.expect]
  refine sum_congr rfl fun x _ => ?_
  simp only [Distribution.independent]
  ring

/-- The principle of deferred decisions for events. -/
theorem prob_queryAnswers (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (next : List Bool → ι) {m : ℕ}
    (hfresh : FreshUpTo next m) (E : List Bool → Prop) :
    (Distribution.independent fun _ : ι => Distribution.bernoulli p h0 h1).prob
        (fun ω => E (queryAnswers next ω m)) =
      (Distribution.independent fun _ : Fin m => Distribution.bernoulli p h0 h1).prob
        (fun x => E (List.ofFn x)) := by
  classical
  rw [Distribution.prob_eq_expect, Distribution.prob_eq_expect]
  exact expect_queryAnswers p h0 h1 next hfresh fun L => if E L then 1 else 0

end Deferred

/-! ### Symmetry -/

section Coins

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A permutation of the vertices permutes the pairs. -/
def permSym2 (σ : Equiv.Perm V) : Equiv.Perm (Sym2 V) where
  toFun := Sym2.map σ
  invFun := Sym2.map σ.symm
  left_inv e := by simp [Sym2.map_map]
  right_inv e := by simp [Sym2.map_map]

/-- **Symmetry**: relabelling the vertices by a permutation `σ` preserves the law of the coins. -/
theorem coins_prob_perm (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (σ : Equiv.Perm V)
    (E : (Sym2 V → Bool) → Prop) :
    (coins p h0 h1).prob (fun ω => E (fun e => ω (e.map σ))) = (coins p h0 h1).prob E := by
  classical
  rw [Distribution.prob_eq_expect, Distribution.prob_eq_expect]
  simp only [Distribution.expect, coins, Distribution.independent]
  refine Fintype.sum_equiv ((permSym2 σ).arrowCongr (Equiv.refl Bool)).symm _ _ fun ω => ?_
  congr 1
  exact (Equiv.prod_comp (permSym2 σ) fun e => (bernoulli p h0 h1).weight (ω e)).symm

end Coins

end Epidemics
