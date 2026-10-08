import RumorSpread.PullGood

/-!
# Main theorem: PULL informs the complete graph in `O(log n)` rounds w.h.p.

Starting the PULL protocol on `K_n` (`n ≥ 2`) from a single informed node, after
`⌈160 log n⌉` rounds all `n` nodes are informed with probability at least `1 - 2/n`
[KSSV00, §2]. The constant is deliberately crude, as for PUSH in `Main.lean`: the growth phase
(informed set up to `n/2`) and the shrinking phase (expected uninformed count contracting, see
`pull_avg_uninformed`) are glued exactly as in `prNotAllInformed_le`: the proof instantiates the
generic `notAllOf_le_two_div` (`PullPhases.lean`) with the PULL inputs of `PullGood.lean`.
-/

namespace RumorPush

open Finset Dynamics

variable {n : ℕ}

/-- **PULL rumor spreading on the complete graph, `O(log n)` rounds** [KSSV00, §2].

Start the PULL protocol on `K_n` (`n ≥ 2`) with the single informed node `v₀`. After
`⌈160 log n⌉` rounds the probability that some node is still uninformed is at most `2/n`. -/
theorem pull_informs_all_whp (hn : 2 ≤ n) (v₀ : Fin n) :
    prPullNotAllInformed n v₀ ⌈(160 : ℝ) * Real.log n⌉₊ ≤ 2 / n := by
  haveI := tgt_nonempty hn
  exact notAllOf_le_two_div hn subset_pullStep (pull_prob_goodRound hn)
    (pull_avg_uninformed_contract hn) v₀

/-- Complement form of `pull_informs_all_whp`: after `⌈160 log n⌉` rounds of PULL, **all**
nodes are informed with probability at least `1 - 2/n`. -/
theorem pull_informs_all_whp' (hn : 2 ≤ n) (v₀ : Fin n) :
    1 - 2 / (n : ℝ)
      ≤ expList (Tgt n) ⌈(160 : ℝ) * Real.log n⌉₊
          (fun l => if pullRun {v₀} l = univ then (1 : ℝ) else 0) := by
  haveI := tgt_nonempty hn
  have hsum : expList (Tgt n) ⌈(160 : ℝ) * Real.log n⌉₊
        (fun l => if pullRun {v₀} l = univ then (1 : ℝ) else 0)
      + prPullNotAllInformed n v₀ ⌈(160 : ℝ) * Real.log n⌉₊ = 1 := by
    rw [prPullNotAllInformed, ← expList_add]
    have h : (fun l => (if pullRun {v₀} l = univ then (1 : ℝ) else 0)
        + (if pullRun {v₀} l = univ then (0 : ℝ) else 1)) = fun _ => (1 : ℝ) := by
      funext l
      split <;> norm_num
    rw [h, expList_const]
  have hmain := pull_informs_all_whp hn v₀
  linarith

end RumorPush
