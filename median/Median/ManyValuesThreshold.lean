import Median.Basic

/-! # Many values: reduction to two binary thresholds

`median_consensus_fast` (in `Median/ManyValues.lean`) reduces consensus on a value `v` to two
runs of the binary dynamics driven by the same samples:

* the upper threshold `u ↦ [v ≤ x u]` is monotone, so it commutes with the median rule
  (`threshold_run`);
* the lower threshold `u ↦ [x u ≤ v]` is antitone, and the median of three also commutes with
  antitone maps, because it is self-dual (`med3_antitone`, `comp_run_of_med3`).

Their gaps are the two margins around `v` (`gap_upper`, `gap_lower`), and when both runs end
all-`true`, all nodes hold `v` (`run_eq_const_of_thresholds`).
-/

namespace Median

open Finset

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **The median commutes with antitone maps** (the median of three is self-dual). -/
theorem med3_antitone {β : Type*} [LinearOrder β] {f : α → β} (hf : Antitone f) (a b c : α) :
    f (med3 a b c) = med3 (f a) (f b) (f c) := by
  simp only [med3, hf.map_max, hf.map_min]
  rw [max_min_distrib_left, max_eq_right min_le_max]

/-- A map that commutes with the median of three commutes with the median dynamics: applying it
before or after a run with the same samples gives the same configuration. -/
theorem comp_run_of_med3 {β : Type*} [LinearOrder β] {f : α → β}
    (hf : ∀ a b c, f (med3 a b c) = med3 (f a) (f b) (f c)) (y : Config n α)
    (l : List (Round n)) : (fun u => f (run y l u)) = run (fun u => f (y u)) l := by
  induction l generalizing y with
  | nil => rfl
  | cons r l ih =>
    show (fun u => f (run (step y r) l u)) = run (step (fun u => f (y u)) r) l
    have hs : (fun u => f (step y r u)) = step (fun u => f (y u)) r :=
      funext fun u => hf (y u) (y (r u).1) (y (r u).2)
    rw [ih (step y r), hs]

/-- The lower threshold `a ↦ [a ≤ v]` is antitone. -/
lemma antitone_decide_le (v : α) : Antitone fun a : α => decide (a ≤ v) := by
  intro a b hab
  by_cases h : b ≤ v
  · simp [h, hab.trans h]
  · simp [h]

/-- **Consensus from two thresholds.** If, with the same samples, the threshold runs
`u ↦ [v ≤ x u]` and `u ↦ [x u ≤ v]` both end all-`true`, the run of `x` ends with all nodes
holding `v`. -/
theorem run_eq_const_of_thresholds {x : Config n α} {v : α} {l : List (Round n)}
    (h₁ : run (fun u => decide (v ≤ x u)) l = fun _ => true)
    (h₂ : run (fun u => decide (x u ≤ v)) l = fun _ => true) : run x l = fun _ => v := by
  funext u
  have e1 := congrFun (threshold_run v x l) u
  have e2 := congrFun (comp_run_of_med3 (med3_antitone (antitone_decide_le v)) x l) u
  rw [h₁] at e1
  rw [h₂] at e2
  simp only [decide_eq_true_eq] at e1 e2
  exact le_antisymm e2 e1

/-! ### The gaps of the two threshold runs -/

/-- Every node satisfies `p` or not: `#{p} + #{¬p} = n`. -/
lemma cast_card_filter_add_not (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) + ((univ.filter fun u => ¬ p u).card : ℝ) = n := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) p
  rw [card_univ, Fintype.card_fin] at h
  exact_mod_cast h

/-- The gap of the binary configuration `u ↦ [P u]` is `#{P} - #{¬P}`. -/
lemma gap_decide (P : Fin n → Prop) [DecidablePred P] :
    (ones (fun u => decide (P u)) : ℝ) - (n - ones (fun u => decide (P u)))
      = ((univ.filter P).card : ℝ) - (univ.filter fun u => ¬ P u).card := by
  have hones : ones (fun u => decide (P u)) = (univ.filter P).card := by simp [ones]
  have hs := cast_card_filter_add_not P
  rw [hones]
  linarith

/-- The gap of the upper threshold `u ↦ [v ≤ x u]` is the margin `#{v ≤ x} - #{x < v}`. -/
lemma gap_upper (x : Config n α) (v : α) :
    (ones (fun u => decide (v ≤ x u)) : ℝ) - (n - ones (fun u => decide (v ≤ x u)))
      = ((univ.filter fun u => v ≤ x u).card : ℝ) - (univ.filter fun u => x u < v).card := by
  rw [gap_decide]
  simp only [not_le]

/-- The gap of the lower threshold `u ↦ [x u ≤ v]` is the margin `#{x ≤ v} - #{v < x}`. -/
lemma gap_lower (x : Config n α) (v : α) :
    (ones (fun u => decide (x u ≤ v)) : ℝ) - (n - ones (fun u => decide (x u ≤ v)))
      = ((univ.filter fun u => x u ≤ v).card : ℝ) - (univ.filter fun u => v < x u).card := by
  rw [gap_decide]
  simp only [not_le]

end Median
