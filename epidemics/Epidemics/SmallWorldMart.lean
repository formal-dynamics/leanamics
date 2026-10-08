import Epidemics.SmallWorldDefs

/-! # Adaptive observations: a finite supermartingale lemma (EPI-6, tools)

Tools for the exploration argument of [BCDPTZ22] (Appendix C), in finite probability.

* **Histories.** An adaptive process observes `obs h ω` after the history `h` of previous
  observations (`hist obs ω k` is the history after `k` steps). This generalizes EPI-3's
  `queryAnswers` (one coin per step) to arbitrary observations (blocks of coins, partners in a
  matching, …).
* **Supermartingale lemma** (`expect_prod_hist_le_one`): if every factor `f h b ≥ 0` has
  conditional expectation at most `1` given the history `h`, the product of the factors along the
  process has expectation at most `1`. With Markov's inequality this gives the tail bound of the
  exploration (`Epidemics.SmallWorldExplore`), in the role of the Galton–Watson comparison of the
  paper.
* **Coordinatewise combination of independent families** (`expect_expect_coord`): if `x` and `y`
  are independent families, `fun i => φ i (x i) (y i)` is an independent family. This gives the
  independence of disjoint sets of coordinates (`expect_mul_of_dep`) and, in
  `Epidemics.SmallWorldCollapse`, the law of the percolated `SWG(n, q)`.
* **Fresh observations of independent coordinates** (`expect_prod_hist_le_one_of_fresh`): if each
  observation reads coordinates not read before, the conditional expectation is the unconditional
  one, so it suffices that `E[f h (obs h ω)] ≤ 1` for every history `h` (principle of deferred
  decisions).
-/

namespace Epidemics
open Finset Dynamics

/-! ### Histories of an adaptive observation process -/

section History

variable {Ω β : Type*}

/-- The history of an adaptive observation process after `k` steps: the list of the first `k`
observations, the observation after the history `h` being `obs h ω`. -/
def hist (obs : List β → Ω → β) (ω : Ω) : ℕ → List β
  | 0 => []
  | k + 1 => hist obs ω k ++ [obs (hist obs ω k) ω]

@[simp] lemma length_hist (obs : List β → Ω → β) (ω : Ω) (k : ℕ) :
    (hist obs ω k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [hist, ih]

lemma hist_take (obs : List β → Ω → β) (ω : Ω) {j k : ℕ} (hjk : j ≤ k) :
    (hist obs ω k).take j = hist obs ω j := by
  induction k with
  | zero => obtain rfl : j = 0 := Nat.le_zero.mp hjk; rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · rw [hist, List.take_append_of_le_length (by simp; omega), ih (by omega)]
    · obtain rfl : j = k + 1 := le_antisymm hjk h
      exact List.take_of_length_le (by simp)

lemma hist_succ_eq_iff (obs : List β → Ω → β) (ω : Ω) (k : ℕ) (h : List β) (b : β) :
    hist obs ω (k + 1) = h ++ [b] ↔ hist obs ω k = h ∧ obs h ω = b := by
  rw [hist]
  constructor
  · intro e
    obtain ⟨e1, e2⟩ := List.append_inj' e rfl
    refine ⟨e1, ?_⟩
    rw [← e1]
    simpa using e2
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The product of the factors `f` along the first `m` steps, from step `j` on. -/
noncomputable def histProd (obs : List β → Ω → β) (f : List β → β → ℝ) (ω : Ω) (j m : ℕ) : ℝ :=
  ∏ k ∈ Finset.Ico j (j + m), f (hist obs ω k) (obs (hist obs ω k) ω)

lemma histProd_succ (obs : List β → Ω → β) (f : List β → β → ℝ) (ω : Ω) (j m : ℕ) :
    histProd obs f ω j (m + 1) =
      f (hist obs ω j) (obs (hist obs ω j) ω) * histProd obs f ω (j + 1) m := by
  unfold histProd
  rw [show j + (m + 1) = (j + 1) + m by omega, Finset.prod_eq_prod_Ico_succ_bot (by omega)]

lemma histProd_zero_succ (obs : List β → Ω → β) (f : List β → β → ℝ) (ω : Ω) (k : ℕ) :
    histProd obs f ω 0 (k + 1) =
      histProd obs f ω 0 k * f (hist obs ω k) (obs (hist obs ω k) ω) := by
  unfold histProd
  rw [zero_add, zero_add, Finset.prod_Ico_succ_top (Nat.zero_le k)]

lemma histProd_nonneg (obs : List β → Ω → β) {f : List β → β → ℝ} (hf0 : ∀ h b, 0 ≤ f h b)
    (ω : Ω) (j m : ℕ) : 0 ≤ histProd obs f ω j m :=
  prod_nonneg fun _ _ => hf0 _ _

variable [Fintype Ω] [Fintype β] [DecidableEq β]

/-- Conditioning step: from step `j` on, after the history `h₀`, the product of the factors has
conditional expectation at most `1`. -/
lemma expect_ind_histProd_le (P : Distribution Ω) (obs : List β → Ω → β)
    (f : List β → β → ℝ) (hf0 : ∀ h b, 0 ≤ f h b)
    (hf : ∀ h : List β, P.expect (fun ω => if hist obs ω h.length = h then f h (obs h ω) else 0)
      ≤ P.expect (fun ω => if hist obs ω h.length = h then 1 else 0)) (m : ℕ) :
    ∀ h₀ : List β, P.expect (fun ω => if hist obs ω h₀.length = h₀ then
        histProd obs f ω h₀.length m else 0) ≤
      P.expect (fun ω => if hist obs ω h₀.length = h₀ then 1 else 0) := by
  classical
  induction m with
  | zero => intro h₀; simp [histProd]
  | succ m ih =>
    intro h₀
    -- decompose along the next observation
    have hdec (ω : Ω) : (if hist obs ω h₀.length = h₀ then
        histProd obs f ω h₀.length (m + 1) else 0) =
        ∑ b : β, f h₀ b * (if hist obs ω (h₀ ++ [b]).length = h₀ ++ [b] then
          histProd obs f ω (h₀ ++ [b]).length m else 0) := by
      simp only [List.length_append, List.length_singleton]
      by_cases hh : hist obs ω h₀.length = h₀
      · rw [if_pos hh, histProd_succ, hh, sum_eq_single (obs h₀ ω)]
        · rw [if_pos ((hist_succ_eq_iff obs ω _ _ _).mpr ⟨hh, rfl⟩)]
        · intro b _ hb
          rw [if_neg (fun e => hb ((hist_succ_eq_iff obs ω _ _ _).mp e).2.symm), mul_zero]
        · simp
      · rw [if_neg hh]
        refine (sum_eq_zero fun b _ => ?_).symm
        rw [if_neg (fun e => hh ((hist_succ_eq_iff obs ω _ _ _).mp e).1), mul_zero]
    have hdec1 (ω : Ω) : (if hist obs ω h₀.length = h₀ then f h₀ (obs h₀ ω) else 0) =
        ∑ b : β, f h₀ b * (if hist obs ω (h₀ ++ [b]).length = h₀ ++ [b] then 1 else 0) := by
      simp only [List.length_append, List.length_singleton]
      by_cases hh : hist obs ω h₀.length = h₀
      · rw [if_pos hh, sum_eq_single (obs h₀ ω)]
        · rw [if_pos ((hist_succ_eq_iff obs ω _ _ _).mpr ⟨hh, rfl⟩), mul_one]
        · intro b _ hb
          rw [if_neg (fun e => hb ((hist_succ_eq_iff obs ω _ _ _).mp e).2.symm), mul_zero]
        · simp
      · rw [if_neg hh]
        refine (sum_eq_zero fun b _ => ?_).symm
        rw [if_neg (fun e => hh ((hist_succ_eq_iff obs ω _ _ _).mp e).1), mul_zero]
    calc P.expect (fun ω => if hist obs ω h₀.length = h₀ then
          histProd obs f ω h₀.length (m + 1) else 0)
        = ∑ b : β, f h₀ b * P.expect (fun ω => if hist obs ω (h₀ ++ [b]).length = h₀ ++ [b]
            then histProd obs f ω (h₀ ++ [b]).length m else 0) := by
          simp_rw [hdec, Distribution.expect_sum, Distribution.expect_mul]
      _ ≤ ∑ b : β, f h₀ b * P.expect (fun ω => if hist obs ω (h₀ ++ [b]).length = h₀ ++ [b]
            then 1 else 0) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (ih _) (hf0 _ _)
      _ = P.expect (fun ω => if hist obs ω h₀.length = h₀ then f h₀ (obs h₀ ω) else 0) := by
          simp_rw [hdec1, Distribution.expect_sum, Distribution.expect_mul]
      _ ≤ _ := hf h₀

/-- **Supermartingale lemma.** If the factors `f h b ≥ 0` have conditional expectation at most
`1` given every history `h`, then the product of the factors along the first `m` steps of the
process has expectation at most `1`. -/
theorem expect_prod_hist_le_one (P : Distribution Ω) (obs : List β → Ω → β)
    (f : List β → β → ℝ) (hf0 : ∀ h b, 0 ≤ f h b)
    (hf : ∀ h : List β, P.expect (fun ω => if hist obs ω h.length = h then f h (obs h ω) else 0)
      ≤ P.expect (fun ω => if hist obs ω h.length = h then 1 else 0)) (m : ℕ) :
    P.expect (fun ω => histProd obs f ω 0 m) ≤ 1 := by
  have := expect_ind_histProd_le P obs f hf0 hf m []
  simpa [hist] using this

end History

/-! ### Markov's inequality for a nonnegative product -/

/-- **Markov's inequality**: `P(a ≤ X) ≤ E[X] / a` for `X ≥ 0` and `a > 0`. -/
lemma prob_le_expect_div {α : Type*} [Fintype α] (P : Distribution α) (X : α → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    P.prob (fun ω => a ≤ X ω) ≤ P.expect X / a := by
  classical
  rw [Distribution.prob_eq_expect, le_div_iff₀ ha, mul_comm, ← Distribution.expect_mul]
  refine P.expect_mono fun ω => ?_
  split_ifs with h
  · linarith
  · linarith [hX ω]

/-! ### Coordinatewise combination of independent families -/

section Coord

variable {ι α β γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β] [Fintype γ]

/-- **Coordinatewise combination**: if `x ~ independent P` and `y ~ independent Q` are
independent, and `R i` is the law of `φ i a b` for `a ~ P i`, `b ~ Q i`, then
`fun i => φ i (x i) (y i)` has law `independent R`. -/
theorem expect_expect_coord (P : ι → Distribution α) (Q : ι → Distribution β)
    (R : ι → Distribution γ) (φ : ι → α → β → γ) [DecidableEq γ]
    (hR : ∀ i c, (R i).weight c =
      ∑ a, ∑ b, if φ i a b = c then (P i).weight a * (Q i).weight b else 0)
    (H : (ι → γ) → ℝ) :
    (Distribution.independent P).expect (fun x =>
        (Distribution.independent Q).expect fun y => H fun i => φ i (x i) (y i)) =
      (Distribution.independent R).expect H := by
  classical
  set g : ι → γ → α → β → ℝ := fun i c a b =>
    if φ i a b = c then (P i).weight a * (Q i).weight b else 0 with hg
  have key (z : ι → γ) : (∏ i, (R i).weight (z i)) =
      ∑ x : ι → α, ∑ y : ι → β, ∏ i, g i (z i) (x i) (y i) := by
    have h1 : ∀ i, (R i).weight (z i) = ∑ ab : α × β, g i (z i) ab.1 ab.2 := fun i => by
      rw [hR, Fintype.sum_prod_type']
    simp_rw [h1]
    rw [Fintype.prod_sum, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => α) (fun _ => β)) _ _
      fun w => rfl
  have hpt (x : ι → α) (y : ι → β) (z : ι → γ) : (∏ i, g i (z i) (x i) (y i)) =
      if (fun i => φ i (x i) (y i)) = z then
        (∏ i, (P i).weight (x i)) * ∏ i, (Q i).weight (y i) else 0 := by
    split_ifs with hz
    · subst hz
      simp [hg, prod_mul_distrib]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
      exact prod_eq_zero (mem_univ i) (by simp [hg, hi])
  simp only [Distribution.expect, Distribution.independent]
  symm
  calc ∑ z : ι → γ, (∏ i, (R i).weight (z i)) * H z
      = ∑ z : ι → γ, ∑ x : ι → α, ∑ y : ι → β, (∏ i, g i (z i) (x i) (y i)) * H z := by
        simp_rw [key, sum_mul]
    _ = ∑ x : ι → α, ∑ y : ι → β, ∑ z : ι → γ, (∏ i, g i (z i) (x i) (y i)) * H z := by
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_comm
    _ = ∑ x : ι → α, ∑ y : ι → β, (∏ i, (P i).weight (x i)) *
          ((∏ i, (Q i).weight (y i)) * H fun i => φ i (x i) (y i)) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        simp_rw [hpt, ite_mul, zero_mul]
        rw [sum_ite_eq]
        simp [mul_assoc]
    _ = _ := by simp_rw [mul_sum]

/-- **Independence of disjoint sets of coordinates**: under an independent product, a function
of the coordinates in `S` and a function of the coordinates outside `S` are uncorrelated. -/
theorem expect_mul_of_dep (P : ι → Distribution α) (S : Finset ι) {F G : (ι → α) → ℝ}
    (hF : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → F ω = F ω')
    (hG : ∀ ω ω', (∀ i ∉ S, ω i = ω' i) → G ω = G ω') :
    (Distribution.independent P).expect (fun ω => F ω * G ω) =
      (Distribution.independent P).expect F * (Distribution.independent P).expect G := by
  classical
  set φ : ι → α → α → α := fun i a b => if i ∈ S then a else b with hφ
  have hR : ∀ i c, (P i).weight c =
      ∑ a, ∑ b, if φ i a b = c then (P i).weight a * (P i).weight b else 0 := by
    intro i c
    by_cases hi : i ∈ S
    · simp only [hφ, if_pos hi]
      rw [sum_eq_single c (fun a _ ha => sum_eq_zero fun b _ => if_neg ha) (by simp)]
      simp [← mul_sum, (P i).sum_one]
    · simp only [hφ, if_neg hi]
      rw [sum_comm, sum_eq_single c (fun b _ hb => sum_eq_zero fun a _ => if_neg hb)
        (by simp)]
      simp [← sum_mul, (P i).sum_one]
  have hmerge := expect_expect_coord P P P φ hR (fun ω => F ω * G ω)
  have hFm (x y : ι → α) : F (fun i => φ i (x i) (y i)) = F x :=
    hF _ _ fun i hi => by simp [hφ, hi]
  have hGm (x y : ι → α) : G (fun i => φ i (x i) (y i)) = G y :=
    hG _ _ fun i hi => by simp [hφ, hi]
  rw [← hmerge]
  simp_rw [hFm, hGm, Distribution.expect_mul]
  rw [mul_comm, ← Distribution.expect_mul]
  congr 1
  funext x
  ring

end Coord

/-! ### Fresh observations of independent coordinates (deferred decisions) -/

section Fresh

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The coordinates read during the history `h`. -/
def readSet (supp : List β → Finset ι) (h : List β) : Finset ι :=
  (Finset.range h.length).biUnion fun j => supp (h.take j)

omit [Fintype ι] [Fintype α] in
/-- The event that the history is `h` depends only on the coordinates read along `h`. -/
lemma hist_eq_iff_of_agree (obs : List β → (ι → α) → β) (supp : List β → Finset ι)
    (hobs : ∀ h ω ω', (∀ i ∈ supp h, ω i = ω' i) → obs h ω = obs h ω') :
    ∀ (h : List β) (ω ω' : ι → α), (∀ i ∈ readSet supp h, ω i = ω' i) →
      (hist obs ω h.length = h ↔ hist obs ω' h.length = h) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intros; simp [hist]
  | append_singleton h b ih =>
    intro ω ω' hag
    have hag' : ∀ i ∈ readSet supp h, ω i = ω' i := fun i hi => hag i (by
      simp only [readSet, mem_biUnion, mem_range, List.length_append,
        List.length_singleton] at hi ⊢
      obtain ⟨j, hj, hij⟩ := hi
      exact ⟨j, by omega, by rwa [List.take_append_of_le_length (by omega)]⟩)
    have hsupp : ∀ i ∈ supp h, ω i = ω' i := fun i hi => hag i (by
      simp only [readSet, mem_biUnion, mem_range, List.length_append, List.length_singleton]
      exact ⟨h.length, by omega, by simpa using hi⟩)
    rw [List.length_append, List.length_singleton, hist_succ_eq_iff, hist_succ_eq_iff,
      ih ω ω' hag', hobs h ω ω' hsupp]

variable [Fintype β] [DecidableEq β]

/-- **Deferred decisions for adaptive observations of independent coordinates.** If every
observation `obs h ω` reads only the coordinates `supp h`, which were not read before along `h`,
and the factors satisfy `E[f h (obs h ω)] ≤ 1` for every history `h` (an unconditional
expectation), then the product of the factors along the process has expectation at most `1`. -/
theorem expect_prod_hist_le_one_of_fresh (P : ι → Distribution α)
    (obs : List β → (ι → α) → β) (supp : List β → Finset ι)
    (hobs : ∀ h ω ω', (∀ i ∈ supp h, ω i = ω' i) → obs h ω = obs h ω')
    (hfresh : ∀ h : List β, Disjoint (supp h) (readSet supp h))
    (f : List β → β → ℝ) (hf0 : ∀ h b, 0 ≤ f h b)
    (hf : ∀ h : List β, (Distribution.independent P).expect (fun ω => f h (obs h ω)) ≤ 1)
    (m : ℕ) :
    (Distribution.independent P).expect (fun ω => histProd obs f ω 0 m) ≤ 1 := by
  classical
  refine expect_prod_hist_le_one _ obs f hf0 (fun h => ?_) m
  have hind := expect_mul_of_dep P (readSet supp h)
    (F := fun ω => if hist obs ω h.length = h then (1 : ℝ) else 0)
    (G := fun ω => f h (obs h ω))
    (fun ω ω' hag => by
      simp only [hist_eq_iff_of_agree obs supp hobs h ω ω' hag])
    (fun ω ω' hag => by
      rw [hobs h ω ω' fun i hi => hag i (Finset.disjoint_left.mp (hfresh h) hi)])
  calc (Distribution.independent P).expect
        (fun ω => if hist obs ω h.length = h then f h (obs h ω) else 0)
      = (Distribution.independent P).expect (fun ω =>
          (if hist obs ω h.length = h then (1 : ℝ) else 0) * f h (obs h ω)) := by
        congr 1; funext ω; split_ifs <;> simp
    _ = _ * _ := hind
    _ ≤ (Distribution.independent P).expect
          (fun ω => if hist obs ω h.length = h then (1 : ℝ) else 0) * 1 :=
        mul_le_mul_of_nonneg_left (hf h)
          ((Distribution.independent P).expect_nonneg fun ω => by split_ifs <;> norm_num)
    _ = _ := mul_one _

/-- The moment-generating function of the total weight of the open coordinates of a block:
`E[exp (∑_{e ∈ B open} a e)] = ∏_{e ∈ B} (1 - r e + r e · exp (a e))`. -/
lemma expect_exp_sum_open {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1) (B : Finset ι) (a : ι → ℝ) :
    (Distribution.independent fun e => Distribution.bernoulli (r e) (hr0 e) (hr1 e)).expect
      (fun ω => Real.exp (∑ e ∈ B.filter fun e => ω e = true, a e)) =
      ∏ e ∈ B, (1 - r e + r e * Real.exp (a e)) := by
  classical
  set g : ι → Bool → ℝ := fun e b =>
    if e ∈ B then (if b = true then Real.exp (a e) else 1) else 1 with hg
  have hpt (ω : ι → Bool) : Real.exp (∑ e ∈ B.filter fun e => ω e = true, a e) =
      ∏ e, g e (ω e) := by
    rw [Real.exp_sum, Finset.prod_filter, hg]
    simp only
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [show (fun ω : ι → Bool => Real.exp (∑ e ∈ B.filter fun e => ω e = true, a e)) =
    fun ω => ∏ e, g e (ω e) from funext hpt, Distribution.independent_expect_prod, hg]
  simp only
  rw [← Finset.prod_subset (Finset.subset_univ B) (fun e _ he => by simp [he])]
  refine Finset.prod_congr rfl fun e he => ?_
  simp only [he, if_true, Distribution.bernoulli_expect]
  simp
  ring

/-- For `0 ≤ x ≤ κ - 1 ≤ 1`: `1 - r + r eˣ ≤ exp (κ r x)`. -/
lemma one_sub_add_mul_exp_le {r x κ : ℝ} (hr : 0 ≤ r) (hx0 : 0 ≤ x) (hxκ : x ≤ κ - 1)
    (hκ : κ ≤ 2) : 1 - r + r * Real.exp x ≤ Real.exp (κ * r * x) := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; linarith
  have h1 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx1)).2
  have h2 : Real.exp x - 1 ≤ κ * x := by nlinarith
  have h3 : 1 + κ * r * x ≤ Real.exp (κ * r * x) := by
    linarith [Real.add_one_le_exp (κ * r * x)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hr]

end Fresh

end Epidemics
