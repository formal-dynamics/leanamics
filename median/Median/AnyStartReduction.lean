import Median.AnyStartAux

/-! # Any start: the reduction to two values

Helpers for `consensus_of_binary` and `median_consensus_any` in `Median/AnyStart.lean`:

* `notConsensus_run_le_sum` (**threshold witness**): if a run of `x` has not reached consensus,
  two nodes hold values `a < b`; the threshold configuration `decide (b ≤ x ·)`, which follows
  the same rounds (`threshold_run`), has not reached consensus either, and `b` is an initial
  value above the minimum. So, pointwise in the rounds, `notConsensus` of the run is at most the
  sum of `notConsensus` over the threshold runs at the initial values above the minimum;
* `card_image_sub_one_le`: there are at most `n` of them.
-/

namespace Median
open Finset Dynamics

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **Threshold witness.** If `m` is below every initial value, then, pointwise in the rounds
`l`, failing to reach consensus from `x` is at most the sum, over the initial values `b ≠ m`, of
failing to reach consensus from the threshold configuration `decide (b ≤ x ·)`. -/
lemma notConsensus_run_le_sum [NeZero n] (x : Config n α) {m : α} (hm : ∀ v, m ≤ x v)
    (l : List (Round n)) :
    notConsensus (run x l)
      ≤ ∑ b ∈ (univ.image x).erase m, notConsensus (run (fun v => decide (b ≤ x v)) l) := by
  by_cases hc : Consensus (run x l)
  · rw [notConsensus_cons' hc]
    exact sum_nonneg fun b _ => notConsensus_nonneg' _
  rw [notConsensus_noncons' hc]
  -- two nodes `u, v` with `run x l u < run x l v`
  obtain ⟨u, v, hlt⟩ : ∃ u v, run x l u < run x l v := by
    by_contra h
    push Not at h
    exact hc ⟨run x l 0, fun w => le_antisymm (h 0 w) (h w 0)⟩
  -- the threshold at `b = run x l v`: an initial value above `m`, not in consensus after `l`
  have hb : run x l v ∈ (univ.image x).erase m := by
    refine mem_erase.mpr ⟨?_, run_mem_image x l v⟩
    obtain ⟨w, hw⟩ := run_mem x l u
    exact (((hm w).trans_eq hw.symm).trans_lt hlt).ne'
  have hnc : ¬ Consensus (run (fun w => decide (run x l v ≤ x w)) l) := by
    rw [← threshold_run]
    rintro ⟨c, hc⟩
    have hu : decide (run x l v ≤ run x l u) = c := hc u
    have hv : decide (run x l v ≤ run x l v) = c := hc v
    rw [decide_eq_false (not_le.mpr hlt)] at hu
    rw [decide_eq_true le_rfl] at hv
    exact Bool.false_ne_true (hu.trans hv.symm)
  calc (1 : ℝ) = notConsensus (run (fun w => decide (run x l v ≤ x w)) l) :=
        (notConsensus_noncons' hnc).symm
    _ ≤ ∑ b ∈ (univ.image x).erase m, notConsensus (run (fun w => decide (b ≤ x w)) l) :=
        single_le_sum (f := fun b => notConsensus (run (fun w => decide (b ≤ x w)) l))
          (fun b _ => notConsensus_nonneg' _) hb

/-- A configuration takes at most `n` distinct values. -/
lemma card_image_sub_one_le (x : Config n α) : ((univ.image x).card : ℝ) - 1 ≤ n := by
  have h : (univ.image x).card ≤ n := card_image_le.trans_eq (by simp)
  have : ((univ.image x).card : ℝ) ≤ n := by exact_mod_cast h
  linarith

end Median
