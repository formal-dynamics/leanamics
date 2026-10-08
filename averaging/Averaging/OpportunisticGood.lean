import Averaging.OpportunisticSecondMoment

/-! # Non-ephemeral good nodes: the deterministic part of Lemma 4.2

Fix a reference state `x₁` (the state at the start `t₁` of the phase) and a threshold `θ`. The
deviation of a later state `x` at `v` is `r_v = x_v - α - β₁ χ_v`, where `α` is the (conserved)
average and `β₁ χ` the cut component of `x₁`; `v` is *bad* (`badSet`) if `r_v² > θ`. A round is
*bad* (`IsBadStep`) if its dart crosses the cut or has a bad endpoint.

* `not_mem_badSet_avgRun`: a node that is not bad at `t₁` and is touched only by rounds that are
  not bad is never bad: averaging two good nodes of the same community keeps both good, since
  `α + β₁ χ` is constant on each community (proof of Lemma 4.2, Appendix C.3, sets `A_t`).
* `card_filter_touched_le`: the nodes for which this fails number at most `|B| + 2 Z`, with `B`
  the bad set at `t₁` and `Z` the number of bad rounds.

We also collect the facts on i.i.d. lists used to compute expectations of functions of prefixes.
-/

namespace Averaging.Opportunistic
open Finset Dynamics

/-! ### Functions of prefixes of i.i.d. lists -/

section Lists
variable {α : Type*} [Fintype α]

lemma expList_le_of_length {T : ℕ} {F G : List α → ℝ}
    (h : ∀ l : List α, l.length = T → F l ≤ G l) : expList α T F ≤ expList α T G := by
  induction T generalizing F G with
  | zero => exact h [] rfl
  | succ T ih =>
    rw [expList_succ, expList_succ]
    exact avg_le_avg fun a => ih fun l hl => h (a :: l) (by simp [hl])

lemma expList_congr_length {T : ℕ} {F G : List α → ℝ}
    (h : ∀ l : List α, l.length = T → F l = G l) : expList α T F = expList α T G :=
  le_antisymm (expList_le_of_length fun l hl => (h l hl).le)
    (expList_le_of_length fun l hl => (h l hl).ge)

/-- A function of the first `k` of `T ≥ k` draws only sees `k` draws. -/
lemma expList_take [Nonempty α] {k T : ℕ} (hk : k ≤ T) (F : List α → ℝ) :
    expList α T (fun l => F (l.take k)) = expList α k F := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [expList_append]
  refine expList_congr_length fun l hl => ?_
  simp_rw [List.take_left' hl]
  exact expList_const (α := α) m _

/-- A function of the first `k` draws and of the next one. -/
lemma expList_take_getElem? [Nonempty α] {k T : ℕ} (hk : k < T) (F : List α → Option α → ℝ) :
    expList α T (fun l => F (l.take k) l[k]?) = expList α k fun p => avg fun a => F p (some a) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show k + m + 1 = k + (m + 1) by ring, expList_append]
  refine expList_congr_length fun p hp => ?_
  have h1 : ∀ l : List α, (p ++ l).take k = p := fun l => List.take_left' hp
  have h2 : ∀ l : List α, (p ++ l)[k]? = l.head? := fun l => by
    rw [List.getElem?_append_right (by omega), hp, Nat.sub_self, List.head?_eq_getElem?]
  simp_rw [h1, h2, expList_succ, List.head?_cons]
  congr 1
  funext a
  exact expList_const (α := α) m _

end Lists

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {V₁ : Finset V} {d b : ℕ}

/-- A dart crossing the cut. -/
def IsCrossDart (V₁ : Finset V) (e : G.Dart) : Prop := e.snd ∈ V₁ ↔ e.fst ∉ V₁

instance (V₁ : Finset V) (e : G.Dart) : Decidable (IsCrossDart V₁ e) := by
  unfold IsCrossDart; infer_instance

/-- The deviation `r_v = x_v - α - β₁ χ_v` of `x` from the reference `x₁` (Lemma 4.2). -/
noncomputable def devVec (V₁ : Finset V) (x₁ x : V → ℝ) (v : V) : ℝ :=
  x v - avg x₁ - cutCoef V₁ x₁ * cutVec V₁ v

/-- The nodes with `r_v² > θ`. -/
noncomputable def badSet (V₁ : Finset V) (θ : ℝ) (x₁ x : V → ℝ) : Finset V :=
  {v | θ < devVec V₁ x₁ x v ^ 2}

/-- A bad round: the dart crosses the cut or has a bad endpoint. -/
def IsBadStep (V₁ : Finset V) (θ : ℝ) (x₁ x : V → ℝ) (e : G.Dart) : Prop :=
  IsCrossDart V₁ e ∨ e.fst ∈ badSet V₁ θ x₁ x ∨ e.snd ∈ badSet V₁ θ x₁ x

noncomputable instance (V₁ : Finset V) (θ : ℝ) (x₁ x : V → ℝ) (e : G.Dart) :
    Decidable (IsBadStep V₁ θ x₁ x e) := by
  unfold IsBadStep; infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
lemma cutVec_eq_of_not_cross {e : G.Dart} (h : ¬ IsCrossDart V₁ e) :
    cutVec V₁ e.fst = cutVec V₁ e.snd := by
  unfold IsCrossDart at h
  unfold cutVec
  by_cases ha : e.fst ∈ V₁ <;> by_cases hb : e.snd ∈ V₁ <;> simp_all

omit [Fintype V] [DecidableRel G.Adj] in
lemma avgRun_take_succ (x : V → ℝ) (l : List G.Dart) {k : ℕ} {e : G.Dart} (he : l[k]? = some e) :
    avgRun G x (l.take (k + 1)) = edgeAvg G (avgRun G x (l.take k)) e := by
  rw [List.take_add_one, he]
  simp [avgRun, List.foldl_append]

omit [DecidableRel G.Adj] in
/-- The deviation at an untouched node does not change, and at the two endpoints of an internal
dart it becomes the average of the two deviations. -/
lemma devVec_edgeAvg (x₁ x : V → ℝ) (e : G.Dart) (v : V) :
    devVec V₁ x₁ (edgeAvg G x e) v =
      if v = e.fst ∨ v = e.snd then
        (x e.fst + x e.snd) / 2 - avg x₁ - cutCoef V₁ x₁ * cutVec V₁ v
      else devVec V₁ x₁ x v := by
  unfold devVec edgeAvg
  split_ifs <;> rfl

omit [DecidableRel G.Adj] in
/-- **Good nodes stay good** (proof of Lemma 4.2): a node that is not bad at the start and is
touched only by rounds that are not bad is never bad. -/
lemma not_mem_badSet_avgRun (θ : ℝ) (x₁ : V → ℝ) (v : V) (l : List G.Dart)
    (h0 : v ∉ badSet V₁ θ x₁ x₁)
    (hstep : ∀ k < l.length, ∀ e : G.Dart, l[k]? = some e → (v = e.fst ∨ v = e.snd) →
      ¬ IsBadStep V₁ θ x₁ (avgRun G x₁ (l.take k)) e) :
    ∀ k ≤ l.length, v ∉ badSet V₁ θ x₁ (avgRun G x₁ (l.take k)) := by
  intro k
  induction k with
  | zero => intro _; simpa [avgRun] using h0
  | succ k ih =>
    intro hk
    have hk' : k < l.length := by omega
    obtain ⟨e, he⟩ : ∃ e, l[k]? = some e := ⟨l[k], List.getElem?_eq_getElem hk'⟩
    rw [avgRun_take_succ x₁ l he]
    have hv := ih hk'.le
    set y := avgRun G x₁ (l.take k)
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv ⊢
    rw [devVec_edgeAvg]
    split_ifs with hve
    · have hb := hstep k hk' e he hve
      simp only [IsBadStep, not_or, badSet, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hb
      obtain ⟨hc, ha, hb⟩ := hb
      have hχ := cutVec_eq_of_not_cross hc
      have hχv : cutVec V₁ v = cutVec V₁ e.fst := by
        rcases hve with rfl | rfl
        · rfl
        · exact hχ.symm
      have : (y e.fst + y e.snd) / 2 - avg x₁ - cutCoef V₁ x₁ * cutVec V₁ v =
          (devVec V₁ x₁ y e.fst + devVec V₁ x₁ y e.snd) / 2 := by
        unfold devVec; rw [hχv, hχ]; ring
      rw [this]
      nlinarith [sq_nonneg (devVec V₁ x₁ y e.fst - devVec V₁ x₁ y e.snd)]
    · exact hv

/-- The endpoints of the `k`-th dart of `l` (empty past the end). -/
def endpoints (l : List G.Dart) (k : ℕ) : Finset V :=
  match l[k]? with
  | some e => {e.fst, e.snd}
  | none => ∅

omit [Fintype V] [DecidableRel G.Adj] in
lemma card_endpoints_le (l : List G.Dart) (k : ℕ) : #(endpoints l k) ≤ 2 := by
  unfold endpoints
  split
  · exact Finset.card_le_two
  · simp

/-- The `k`-th round of `l` is bad. -/
def IsBadRound (V₁ : Finset V) (θ : ℝ) (x₁ : V → ℝ) (l : List G.Dart) (k : ℕ) : Prop :=
  ∃ e, l[k]? = some e ∧ IsBadStep V₁ θ x₁ (avgRun G x₁ (l.take k)) e

omit [DecidableRel G.Adj] in
open scoped Classical in
/-- **Counting**: the nodes that are bad at the start or touched by a bad round number at most
`|B| + 2 Z`. -/
lemma card_touched_le (θ : ℝ) (x₁ : V → ℝ) (l : List G.Dart) :
    #{v | v ∈ badSet V₁ θ x₁ x₁ ∨ ∃ k < l.length, ∃ e : G.Dart, l[k]? = some e ∧
        (v = e.fst ∨ v = e.snd) ∧ IsBadStep V₁ θ x₁ (avgRun G x₁ (l.take k)) e} ≤
      #(badSet V₁ θ x₁ x₁) + 2 * #{k ∈ range l.length | IsBadRound V₁ θ x₁ l k} := by
  set K := {k ∈ range l.length | IsBadRound V₁ θ x₁ l k}
  have hsub : (univ.filter fun v => v ∈ badSet V₁ θ x₁ x₁ ∨ ∃ k < l.length, ∃ e : G.Dart,
        l[k]? = some e ∧ (v = e.fst ∨ v = e.snd) ∧
          IsBadStep V₁ θ x₁ (avgRun G x₁ (l.take k)) e) ⊆
      badSet V₁ θ x₁ x₁ ∪ K.biUnion (endpoints l) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with hv | ⟨k, hk, e, he, hve, hbad⟩
    · exact Finset.mem_union_left _ hv
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, ?_, ?_⟩)
      · simp only [K, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk, e, he, hbad⟩
      · simp only [endpoints, he]
        rcases hve with rfl | rfl <;> simp
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  gcongr
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k ∈ K, #(endpoints l k) ≤ ∑ _k ∈ K, 2 := Finset.sum_le_sum fun k _ =>
        card_endpoints_le l k
    _ = 2 * #K := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end Averaging.Opportunistic
