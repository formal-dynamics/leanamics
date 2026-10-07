import Median.ManyValuesKernel
import Median.ManyValuesThreshold

/-! # Many values: an odd number of equally supported values

Counting behind `odd_split_consensus` (in `Median/ManyValues.lean`): if `2k+1` values are each
held by `n/(2k+1)` nodes and `v` has exactly `k` values below it, then both margins around `v`
equal `n/(2k+1)` (`odd_split_margins`), so `median_consensus_fast` applies with
`Δ = n/(2k+1)`. The counts are taken fiber by fiber over the image (`cast_card_filter_comp`).
The extra rounds of the final constant are harmless because consensus is absorbing
(`expList_run_const_mono`).
-/

namespace Median

open Finset Dynamics

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **Counting fiber by fiber.** If every value of the image of `x` is held by exactly `c`
nodes, the nodes holding a value with property `P` number `#{values with P} · c`. -/
lemma cast_card_filter_comp {ι : Type*} [Fintype ι] {β : Type*} [DecidableEq β] {x : ι → β}
    {c : ℝ} (hc : ∀ a ∈ univ.image x, ((univ.filter fun u => x u = a).card : ℝ) = c)
    (P : β → Prop) [DecidablePred P] :
    ((univ.filter fun u => P (x u)).card : ℝ) = ((univ.image x).filter P).card * c := by
  have h : (univ.filter fun u => P (x u)).card
      = ∑ b ∈ (univ.image x).filter P, (univ.filter fun u => x u = b).card := by
    rw [card_eq_sum_card_fiberwise (f := x) (t := (univ.image x).filter P)]
    · refine sum_congr rfl fun b hb => ?_
      have hPb : P b := (mem_filter.mp hb).2
      congr 1
      ext u
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hPb, h⟩⟩
    · intro u hu
      exact mem_filter.mpr ⟨mem_image_of_mem x (mem_univ u), (mem_filter.mp hu).2⟩
  rw [h, Nat.cast_sum, sum_congr rfl fun b hb => hc b (mem_filter.mp hb).1, sum_const,
    nsmul_eq_mul]

/-- In a finset `s ∋ v`, the elements `≤ v` are those `< v` and `v` itself. -/
lemma card_filter_le_eq_succ {s : Finset α} {v : α} (hv : v ∈ s) :
    (s.filter (· ≤ v)).card = (s.filter (· < v)).card + 1 := by
  have hins : s.filter (· ≤ v) = insert v (s.filter (· < v)) := by
    ext a
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨ha, hle⟩
      rcases hle.lt_or_eq with h | h
      · exact Or.inr ⟨ha, h⟩
      · exact Or.inl h
    · rintro (rfl | ⟨ha, h⟩)
      · exact ⟨hv, le_rfl⟩
      · exact ⟨ha, h.le⟩
  have hnot : v ∉ s.filter (· < v) := by simp
  rw [hins, card_insert_of_notMem hnot]

/-- **Both margins around the middle value equal `n/(2k+1)`.** If every value of `x` is held
by `n/(2k+1)` nodes and `v` is a value with exactly `k` values below it, then
`#{v ≤ x} - #{x < v} = #{x ≤ v} - #{v < x} = n/(2k+1)`. -/
theorem odd_split_margins {x : Config n α} {k : ℕ}
    (hc : ∀ a ∈ univ.image x, ((univ.filter fun u => x u = a).card : ℝ) = n / (2 * k + 1))
    {v : α} (hv : v ∈ univ.image x) (hlt : ((univ.image x).filter (· < v)).card = k) :
    ((univ.filter fun u => v ≤ x u).card : ℝ) - (univ.filter fun u => x u < v).card
        = n / (2 * k + 1)
      ∧ ((univ.filter fun u => x u ≤ v).card : ℝ) - (univ.filter fun u => v < x u).card
        = n / (2 * k + 1) := by
  -- `k c` nodes hold a value `< v` and `(k+1) c` a value `≤ v`, where `n = (2k+1) c`
  have hlt' := cast_card_filter_comp hc (· < v)
  have hle' := cast_card_filter_comp hc (· ≤ v)
  rw [hlt] at hlt'
  rw [card_filter_le_eq_succ hv, hlt] at hle'
  have hs1 := cast_card_filter_add_not (fun u => x u < v)
  have hs2 := cast_card_filter_add_not (fun u => x u ≤ v)
  simp only [not_lt, not_le] at hs1 hs2
  have hn : (n : ℝ) = (2 * k + 1) * (n / (2 * k + 1)) := by field_simp
  push_cast at hlt' hle'
  constructor <;> linarith

variable [NeZero n]

/-- **Padding.** The probability that all nodes hold `v` after `T` rounds is nondecreasing in
`T`: consensus is absorbing. -/
lemma expList_run_const_mono (x : Config n α) (v : α) :
    Monotone fun T =>
      expList (Round n) T (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) :=
  expList_foldl_mono step (P := fun y => y = fun _ => v)
    (fun y r hy => by subst hy; exact step_of_consensus _ ⟨v, fun _ => rfl⟩ r) x

end Median
