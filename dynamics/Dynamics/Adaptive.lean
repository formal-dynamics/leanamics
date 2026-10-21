import Dynamics.Independent

/-!
# Adaptive observations: a product supermartingale and deferred decisions

An adaptive process observes `obs h ω` after the history `h` of its previous observations, the
randomness being `ω` (`hist obs ω k` is the history after `k` steps). Examples: querying one coin
`ω (next h)` per step (EPI-3's depth-first search, where `obs h ω = ω (next h)`), or a block of
coins, or the partners of a node in a random matching (EPI-6's exploration).

* **Histories.** `hist`, its length, one more step (`hist_succ_eq_iff`), and the history as a
  list of prescribed answers (`hist_eq_iff`).
* **Supermartingale lemma** (`Distribution.expect_prod_hist_le_one`): if every factor
  `f h b ≥ 0` has conditional expectation at most `1` given the history `h`, the product of the
  factors along the process (`histProd`) has expectation at most `1`. With Markov's inequality this
  bounds the probability that the product is large.
* **Deferred decisions** (`Distribution.expect_prod_hist_le_one_of_fresh`): under an independent
  family `Distribution.independent P`, if each observation reads coordinates not read before
  along the history (`readSet`), the conditional expectation of a factor is its unconditional
  expectation, so it suffices that `E[f h (obs h ω)] ≤ 1` for every history `h`.
-/

namespace Dynamics
open Finset

/-! ### Histories of an adaptive observation process -/

section History

variable {Ω β : Type*}

/-- The history of an adaptive observation process after `k` steps: the list of the first `k`
observations, the observation after the history `h` being `obs h ω`. -/
def hist (obs : List β → Ω → β) (ω : Ω) : ℕ → List β
  | 0 => []
  | k + 1 => hist obs ω k ++ [obs (hist obs ω k) ω]

@[simp] lemma hist_zero (obs : List β → Ω → β) (ω : Ω) : hist obs ω 0 = [] := rfl

@[simp] lemma length_hist (obs : List β → Ω → β) (ω : Ω) (k : ℕ) :
    (hist obs ω k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [hist, ih]

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

/-- The history is a given list `L` iff every observation along `L` gives the next entry of
`L`. -/
lemma hist_eq_iff (obs : List β → Ω → β) (ω : Ω) (L : List β) :
    hist obs ω L.length = L ↔ ∀ k < L.length, some (obs (L.take k) ω) = L[k]? := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L b ih =>
    rw [List.length_append, List.length_singleton, hist_succ_eq_iff, ih]
    constructor
    · rintro ⟨hL, hb⟩ k hk
      rcases Nat.lt_or_ge k L.length with hkL | hkL
      · rw [List.take_append_of_le_length hkL.le, List.getElem?_append_left hkL]
        exact hL k hkL
      · obtain rfl : k = L.length := by omega
        simp [hb]
    · intro h
      refine ⟨fun k hk => ?_, by simpa using h L.length (by simp)⟩
      have := h k (by omega)
      rwa [List.take_append_of_le_length hk.le, List.getElem?_append_left hk] at this

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

end History

/-! ### The supermartingale lemma -/

namespace Distribution

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]

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
          simp_rw [hdec, expect_sum, expect_mul]
      _ ≤ ∑ b : β, f h₀ b * P.expect (fun ω => if hist obs ω (h₀ ++ [b]).length = h₀ ++ [b]
            then 1 else 0) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (ih _) (hf0 _ _)
      _ = P.expect (fun ω => if hist obs ω h₀.length = h₀ then f h₀ (obs h₀ ω) else 0) := by
          simp_rw [hdec1, expect_sum, expect_mul]
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

end Distribution

/-! ### Fresh observations of independent coordinates (deferred decisions) -/

section Fresh

variable {ι α β : Type*}

/-- The coordinates read during the history `h`, the observation after the history `h'` reading
the coordinates `supp h'`. -/
def readSet [DecidableEq ι] (supp : List β → Finset ι) (h : List β) : Finset ι :=
  (Finset.range h.length).biUnion fun j => supp (h.take j)

/-- The event that the history is `h` depends only on the coordinates read along `h`. -/
lemma hist_eq_iff_of_agree [DecidableEq ι] (obs : List β → (ι → α) → β)
    (supp : List β → Finset ι)
    (hobs : ∀ h ω ω', (∀ i ∈ supp h, ω i = ω' i) → obs h ω = obs h ω') :
    ∀ (h : List β) (ω ω' : ι → α), (∀ i ∈ readSet supp h, ω i = ω' i) →
      (hist obs ω h.length = h ↔ hist obs ω' h.length = h) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intros; simp
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

variable [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β] [DecidableEq β]

/-- **Deferred decisions for adaptive observations of independent coordinates.** If every
observation `obs h ω` reads only the coordinates `supp h`, which were not read before along `h`,
and the factors satisfy `E[f h (obs h ω)] ≤ 1` for every history `h` (an unconditional
expectation), then the product of the factors along the process has expectation at most `1`. -/
theorem Distribution.expect_prod_hist_le_one_of_fresh (P : ι → Distribution α)
    (obs : List β → (ι → α) → β) (supp : List β → Finset ι)
    (hobs : ∀ h ω ω', (∀ i ∈ supp h, ω i = ω' i) → obs h ω = obs h ω')
    (hfresh : ∀ h : List β, Disjoint (supp h) (readSet supp h))
    (f : List β → β → ℝ) (hf0 : ∀ h b, 0 ≤ f h b)
    (hf : ∀ h : List β, (Distribution.independent P).expect (fun ω => f h (obs h ω)) ≤ 1)
    (m : ℕ) :
    (Distribution.independent P).expect (fun ω => histProd obs f ω 0 m) ≤ 1 := by
  classical
  refine Distribution.expect_prod_hist_le_one _ obs f hf0 (fun h => ?_) m
  have hind := Distribution.expect_mul_of_dep P (readSet supp h)
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

end Fresh

end Dynamics
