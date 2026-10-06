import RumorSpread.Main
import RumorSpread.PullMain

/-!
# Main theorem: PUSH–PULL informs the complete graph in `O(log n)` rounds w.h.p.

Starting the PUSH–PULL protocol on `K_n` (`n ≥ 2`) from a single informed node, after
`⌈160 log n⌉` rounds all `n` nodes are informed with probability at least `1 - 2/n`
[KSSV00, Thm 2.1, in the weaker form `O(log n)` instead of `log₃ n + O(log log n)`]. Since
PUSH–PULL dominates PUSH and PULL pathwise (`run_subset_pushPullRun`,
`pullRun_subset_pushPullRun`), the bound follows from either `push_informs_all_whp` or
`pull_informs_all_whp`; we use the latter, which needs no change in the number of rounds.
-/

namespace RumorPush

open Finset

variable {n : ℕ}

/-- **PUSH–PULL rumor spreading on the complete graph, `O(log n)` rounds** [KSSV00, Thm 2.1,
in `O(log n)` form].

Start the PUSH–PULL protocol on `K_n` (`n ≥ 2`) with the single informed node `v₀`. After
`⌈160 log n⌉` rounds the probability that some node is still uninformed is at most `2/n`. -/
theorem pushPull_informs_all_whp (hn : 2 ≤ n) (v₀ : Fin n) :
    prPushPullNotAllInformed n v₀ ⌈(160 : ℝ) * Real.log n⌉₊ ≤ 2 / n := by
  refine le_trans ?_ (pull_informs_all_whp hn v₀)
  unfold prPushPullNotAllInformed prPullNotAllInformed
  apply expList_le_expList
  intro l
  by_cases h : pullRun {v₀} l = univ
  · have h' : pushPullRun {v₀} l = univ := by
      rw [← univ_subset_iff, ← h]
      exact pullRun_subset_pushPullRun {v₀} l
    rw [if_pos h, if_pos h']
  · rw [if_neg h]
    split <;> norm_num

/-- Complement form of `pushPull_informs_all_whp`: after `⌈160 log n⌉` rounds of PUSH–PULL,
**all** nodes are informed with probability at least `1 - 2/n`. -/
theorem pushPull_informs_all_whp' (hn : 2 ≤ n) (v₀ : Fin n) :
    1 - 2 / (n : ℝ)
      ≤ expList (Tgt n) ⌈(160 : ℝ) * Real.log n⌉₊
          (fun l => if pushPullRun {v₀} l = univ then (1 : ℝ) else 0) := by
  haveI := tgt_nonempty hn
  have hsum : expList (Tgt n) ⌈(160 : ℝ) * Real.log n⌉₊
        (fun l => if pushPullRun {v₀} l = univ then (1 : ℝ) else 0)
      + prPushPullNotAllInformed n v₀ ⌈(160 : ℝ) * Real.log n⌉₊ = 1 := by
    rw [prPushPullNotAllInformed, ← expList_add]
    have h : (fun l => (if pushPullRun {v₀} l = univ then (1 : ℝ) else 0)
        + (if pushPullRun {v₀} l = univ then (0 : ℝ) else 1)) = fun _ => (1 : ℝ) := by
      funext l
      split <;> norm_num
    rw [h, expList_const]
  have hmain := pushPull_informs_all_whp hn v₀
  linarith

end RumorPush
