import Median.Basic
import Median.Binary
import Median.AnyStartAux
import Median.AnyStartPhases
import Median.AnyStartReduction

/-! # Consensus from any configuration (median dynamics)

The main theorem of Doerr, Goldberg, Minder, Sauerwald and Scheideler (SPAA 2011, Theorem 1 of the
full version): without an adversary, from **any** configuration, with any number of distinct
values, the median dynamics reaches consensus within `O(log n)` rounds with high probability.

The proof here goes through two values. The threshold reduction (the paper's Lemma 17, our
`threshold_run`) and a union bound over the at most `n - 1` thresholds (`consensus_of_binary`)
turn a failure bound for every binary configuration into one for every configuration; amplifying
a `C/n` failure bound to `≤ (C/n)³` by running three blocks (consensus absorbs) makes the union
bound affordable. What remains is the binary dynamics (2-Choices) from an arbitrary, possibly
perfectly balanced, start (`binary_any_start`, the paper's Lemmas 13-16 followed by
`consensus_whp`): symmetry breaking until the gap reaches order `√(n log n)`.
-/

namespace Median
open Finset Dynamics

/-- **2-Choices from any start.** From any binary configuration, all nodes agree after
`⌈C log n⌉` rounds except with probability at most `C/n`. -/
theorem binary_any_start : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n Bool,
      expList (Round n) ⌈C * Real.log n⌉₊ (fun l => notConsensus (run x l)) ≤ C / n := by
  /- Two phases, with `L = log n`. **Escape** (`escape_bound`): the potential
  `gapPot y = exp (-|gap y| / (256 √n))` contracts in expectation by `e^{-1/65536}` per round
  (`avg_gapPot_step`: Hoeffding's lemma away from balance, Paley-Zygmund near balance), so after
  `⌈2¹⁷ L⌉` rounds Markov's inequality puts the gap above `128 √(nL)` in absolute value except
  with probability `2/n`. **Consensus** (`finish_bound`): `binary_consensus`, on the
  configuration or on its flip, then finishes within `⌈128 L⌉` rounds except with probability
  `128/n`. -/
  refine ⟨262144, by norm_num, fun n _ hL x => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hL0 : (0 : ℝ) ≤ Real.log n := by linarith
  -- the two phases fit into `⌈2¹⁸ L⌉` rounds, and more rounds never hurt
  have hT : ⌈131072 * Real.log n⌉₊ + ⌈128 * Real.log n⌉₊ ≤ ⌈262144 * Real.log n⌉₊ :=
    ceil_add_ceil_le (by positivity) (by positivity) (by linarith)
  calc expList (Round n) ⌈262144 * Real.log n⌉₊ (fun l => notConsensus (run x l))
      ≤ expList (Round n) (⌈131072 * Real.log n⌉₊ + ⌈128 * Real.log n⌉₊)
          (fun l => notConsensus (run x l)) := expList_run_mono x hT
    _ ≤ 128 / n + 2 / n :=
        expList_add_le (step (n := n) (α := Bool)) notConsensus
          (fun y => if |gapR y| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0)
          (fun y => finish_bound (by linarith) y) (escape_bound (by linarith) x)
    _ ≤ 262144 / n := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by norm_num) hn0.le

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **Reduction to two values.** If every binary configuration fails to reach consensus within
`T` rounds with probability at most `ε`, then a configuration with `m` distinct values fails with
probability at most `(m - 1) ε`. -/
theorem consensus_of_binary [NeZero n] {T : ℕ} {ε : ℝ}
    (hbin : ∀ y : Config n Bool, expList (Round n) T (fun l => notConsensus (run y l)) ≤ ε)
    (x : Config n α) :
    expList (Round n) T (fun l => notConsensus (run x l)) ≤ (((univ.image x).card : ℝ) - 1) * ε := by
  -- pointwise, a failed run is witnessed by a failed threshold run above the minimum value
  have hne : (univ.image x).Nonempty := univ_nonempty.image x
  obtain ⟨m, hmS, hm⟩ : ∃ m ∈ univ.image x, ∀ v, m ≤ x v :=
    ⟨_, min'_mem _ hne, fun v => min'_le _ _ (mem_image_of_mem x (mem_univ v))⟩
  calc expList (Round n) T (fun l => notConsensus (run x l))
      ≤ expList (Round n) T (fun l =>
          ∑ b ∈ (univ.image x).erase m, notConsensus (run (fun v => decide (b ≤ x v)) l)) :=
        expList_le_expList (notConsensus_run_le_sum x hm)
    _ = ∑ b ∈ (univ.image x).erase m,
          expList (Round n) T (fun l => notConsensus (run (fun v => decide (b ≤ x v)) l)) :=
        expList_finset_sum T _ _
    -- the union bound over the `card - 1` thresholds
    _ ≤ ∑ b ∈ (univ.image x).erase m, ε := sum_le_sum fun b _ => hbin _
    _ = (((univ.image x).card : ℝ) - 1) * ε := by
        rw [sum_const, nsmul_eq_mul, card_erase_of_mem hmS, Nat.cast_pred (card_pos.mpr hne)]

/-- **Consensus from any configuration** (the paper's Theorem 1, no adversary). From any
configuration with values in a linear order, all nodes agree after `⌈C log n⌉` rounds except
with probability at most `C/n`. -/
theorem median_consensus_any : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n α,
      expList (Round n) ⌈C * Real.log n⌉₊ (fun l => notConsensus (run x l)) ≤ C / n := by
  obtain ⟨C₀, hC₀, hbin⟩ := binary_any_start
  refine ⟨3 * C₀ + 3, by positivity, fun n _ hC x => ?_⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hL : (1 : ℝ) ≤ Real.log n := by linarith
  -- three blocks of `⌈C₀ log n⌉` rounds: a binary configuration fails w.p. at most `(C₀/n)³`
  have hbin3 (y : Config n Bool) := expList_amplify (hbin n (by linarith)) 3 y
  calc expList (Round n) ⌈(3 * C₀ + 3) * Real.log n⌉₊ (fun l => notConsensus (run x l))
      ≤ expList (Round n) (3 * ⌈C₀ * Real.log n⌉₊) (fun l => notConsensus (run x l)) :=
        expList_run_mono x (mul_ceil_le_ceil (mul_nonneg hC₀.le (by linarith))
          (by push_cast; linarith))
    -- the union bound over the at most `n - 1` threshold configurations
    _ ≤ (((univ.image x).card : ℝ) - 1) * (C₀ / n) ^ 3 := consensus_of_binary hbin3 x
    _ ≤ n * (C₀ / n) ^ 3 :=
        mul_le_mul_of_nonneg_right (card_image_sub_one_le x) (pow_nonneg (by positivity) 3)
    -- `C₀³ ≤ n`, since `3 C₀ ≤ log n`
    _ ≤ (3 * C₀ + 3) / n :=
        mul_div_pow_three_le hC₀.le hn (pow_three_le_of_log hC₀.le hn (by linarith))

end Median
