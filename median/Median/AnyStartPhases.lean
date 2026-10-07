import Median.AnyStartPotential
import Median.AnyStartDrift

/-! # Any start: escape from balance and the consensus phase

The two phases of `binary_any_start`, with `L = log n`:

* **escape** (`escape_bound`, `L ≥ 8192`): after `⌈2¹⁷ L⌉` rounds from any configuration, the
  gap is at least `128 √(nL)` in absolute value except with probability `2/n`. The potential
  `gapPot` drifts down (`avg_gapPot_step`, iterated by `expList_le_of_drift`) to at most
  `e^{-T/65536} + T e^{1/131072 - √n/512}` after `T` rounds, and below the threshold it is at
  least `e^{-√L/2}` (Markov's inequality);
* **consensus** (`finish_bound`, `L ≥ 128`): from a gap at least `128 √(nL)` in absolute value,
  `binary_consensus` (on the configuration, or on its flip if the gap is negative) reaches
  consensus within `⌈128 L⌉` rounds except with probability `128/n`.
-/

namespace Median
open Finset Real Dynamics

variable {n : ℕ}

/-- Not being in consensus is at most not being all `true`. -/
lemma notConsensus_le_one_sub_ite (z : Config n Bool) :
    notConsensus z ≤ 1 - if z = (fun _ => true) then (1 : ℝ) else 0 := by
  split_ifs with h
  · rw [notConsensus_cons ⟨true, fun v => by rw [h]⟩]
    norm_num
  · rw [sub_zero]
    exact notConsensus_le_one _

/-- The flipped configuration fails to reach consensus exactly when the configuration does. -/
lemma expList_notConsensus_run_flip (T : ℕ) (y : Config n Bool) :
    expList (Round n) T (fun l => notConsensus (run (fun v => !y v) l))
      = expList (Round n) T (fun l => notConsensus (run y l)) := by
  simp_rw [run_flip, notConsensus_flip]

variable [NeZero n]

/-- **Escape from balance.** For `log n ≥ 8192`, from any configuration, after `⌈2¹⁷ log n⌉`
rounds the gap is at least `128 √(n log n)` in absolute value, except with probability
at most `2/n`. -/
theorem escape_bound (hL : (8192 : ℝ) ≤ Real.log n) (x : Config n Bool) :
    expList (Round n) ⌈131072 * Real.log n⌉₊
        (fun l => if |gapR (run x l)| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0)
      ≤ 2 / n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hn10 : (10 : ℝ) ≤ n := by linarith [add_one_le_exp (Real.log n), exp_log hn0]
  obtain ⟨T, hT⟩ : ∃ T, T = ⌈131072 * Real.log n⌉₊ := ⟨_, rfl⟩
  rw [← hT]
  -- Markov: below the threshold, the potential is at least `e^{-√(log n)/2}`
  have hind (y : Config n Bool) :
      (if |gapR y| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0)
        ≤ exp (√(Real.log n) / 2) * gapPot y := by
    split_ifs with h
    · calc (1 : ℝ) = exp (√(Real.log n) / 2) * exp (-(√(Real.log n) / 2)) := by
            rw [← exp_add]
            simp
        _ ≤ exp (√(Real.log n) / 2) * gapPot y := by
            refine mul_le_mul_of_nonneg_left (exp_neg_le_gapPot ?_) (exp_pos _).le
            rw [sqrt_mul hn0.le] at h
            linarith
    · exact mul_nonneg (exp_pos _).le (gapPot_pos y).le
  -- the drift of the potential over `T` rounds
  have hdrift := expList_le_of_drift step gapPot (exp_pos _).le
    (exp_le_one_iff.mpr (by norm_num)) (exp_pos _).le (avg_gapPot_step hn10) T x
  have hT1 : 131072 * Real.log n ≤ T := by
    rw [hT]
    exact Nat.le_ceil _
  have hT2 : (T : ℝ) ≤ 131072 * Real.log n + 1 := by
    rw [hT]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  calc expList (Round n) T
        (fun l => if |gapR (run x l)| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0)
      ≤ expList (Round n) T (fun l => exp (√(Real.log n) / 2) * gapPot (run x l)) :=
        expList_le_expList fun l => hind _
    _ = exp (√(Real.log n) / 2) * expList (Round n) T (fun l => gapPot (run x l)) :=
        expList_const_mul _ _ _
    _ ≤ exp (√(Real.log n) / 2)
          * (exp (-(1 / 65536)) ^ T * gapPot x + T * exp (1 / 131072 - √(n : ℝ) / 512)) :=
        mul_le_mul_of_nonneg_left hdrift (exp_pos _).le
    _ ≤ 2 / n := escape_error_le hn0 hL hT1 hT2 (gapPot_le_one x)

/-- `binary_consensus` as a failure bound: from a gap at least `128 √(n log n)`, the dynamics
fails to reach consensus within `⌈128 log n⌉` rounds with probability at most `128/n`. -/
lemma expList_notConsensus_le_of_gap (hL : (128 : ℝ) ≤ Real.log n) {y : Config n Bool}
    (hy : 128 * √((n : ℝ) * Real.log n) ≤ gapR y) :
    expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l)) ≤ 128 / n := by
  have hc := binary_consensus hL y hy
  calc expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l))
      ≤ expList (Round n) ⌈128 * Real.log n⌉₊
          (fun l => 1 - if run y l = (fun _ => true) then (1 : ℝ) else 0) :=
        expList_le_expList fun l => notConsensus_le_one_sub_ite _
    _ = 1 - expList (Round n) ⌈128 * Real.log n⌉₊
          (fun l => if run y l = (fun _ => true) then (1 : ℝ) else 0) :=
        expList_one_sub _ _
    _ ≤ 128 / n := by linarith

/-- **The consensus phase.** For `log n ≥ 128`, from a configuration `y`, consensus fails within
`⌈128 log n⌉` rounds with probability at most `128/n`, unless `|g| < 128 √(n log n)`. -/
theorem finish_bound (hL : (128 : ℝ) ≤ Real.log n) (y : Config n Bool) :
    expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l))
      ≤ 128 / n + if |gapR y| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0 := by
  split_ifs with h
  · calc expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l)) ≤ 1 :=
          (expList_le_expList fun l => notConsensus_le_one _).trans_eq (expList_const _ _)
      _ ≤ 128 / n + 1 := le_add_of_nonneg_left (by positivity)
  rw [add_zero]
  push Not at h
  rcases le_or_gt 0 (gapR y) with hg | hg
  · exact expList_notConsensus_le_of_gap hL (by rwa [abs_of_nonneg hg] at h)
  · -- a negative gap: the flipped configuration has a positive one
    rw [← expList_notConsensus_run_flip]
    exact expList_notConsensus_le_of_gap hL (by rw [gapR_flip]; rwa [abs_of_neg hg] at h)

end Median
