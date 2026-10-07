import Median.Basic
import Median.Binary
import Median.ManyValuesSegments
import Median.ManyValuesThreshold
import Median.ManyValuesSplit

/-! # Many values: the middle value wins fast (median dynamics)

Doerr, Goldberg, Minder, Sauerwald and Scheideler (SPAA 2011; Theorem 21 of the full version)
show that from a uniformly random start with `m` values the median rule reaches consensus in
`O(log m + log log n)` rounds when `m` is odd, but needs `Θ(log n)` rounds when `m` is even.
With two values the dynamics is 2-Choices, and a balanced start needs `Θ(log n)` rounds; with
three equally supported values the middle one wins in `O(log log n)` rounds. This file pins the
deterministic core of the odd case:

* `binary_consensus_fast`: with two values, a gap `Δ ≥ C √(n log n)` gives consensus within
  `O(log (n/Δ) + log log n)` rounds (the gap grows geometrically until the minority is a constant
  fraction, which then shrinks quadratically, `m ↦ ≈ 3m²/n`);
* `median_consensus_fast`: with values in a linear order, a margin `Δ` on both sides of a value
  `v` gives consensus on `v` within `O(log (n/Δ) + log log n)` rounds;
* `odd_split_consensus`: `2k+1` values with equal support: the middle value wins within
  `O(log k + log log n)` rounds.
-/

namespace Median
open Finset Dynamics

/-- **Fast binary consensus from a large gap.** If the `true` nodes outnumber the `false` ones by
at least `Δ ≥ C √(n log n)`, all nodes hold `true` after `⌈C (log (n/Δ) + log log n)⌉` rounds with
probability at least `1 - C/n`. -/
theorem binary_consensus_fast : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n Bool) (Δ : ℝ), C * √(n * Real.log n) ≤ Δ →
      Δ ≤ (ones x : ℝ) - (n - ones x) →
      1 - C / n ≤ expList (Round n) ⌈C * (Real.log (n / Δ) + Real.log (Real.log n))⌉₊
        (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  -- The paper's four segments (`Median/ManyValuesSegments.lean`), each failing w.p. `n⁻²` per
  -- round: the gap grows from `Δ` until the minority is below `n/4` (`T₁ = O(log (n/Δ))` rounds);
  -- linear saturation to `n/8` (6 rounds); quadratic saturation to `β = 512 log n`
  -- (`T₃ = O(log log n)` rounds); consensus (8 rounds). Then padding and the failure budget.
  open Real in
  · refine ⟨128, by norm_num, fun n _ hL x Δ hΔ hgap => ?_⟩
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
    have hΔ1 : 1 ≤ Δ := one_le_of_sqrt_le hL hΔ
    have hΔn : Δ ≤ n := hgap.trans (gapR_le x)
    -- the round counts `T₁ ≤ 5 log (n/Δ) + 2` and `T₃ ≤ 2 log log n + 3`
    obtain ⟨T₁, hT₁, hT₁b⟩ := exists_growth_rounds (by linarith) hΔn
    obtain ⟨T₃, hT₃, hT₃b⟩ := exists_quad_rounds hL
    -- compose the four segments (Markov property)
    have h := kernel_event_comp (Median.kernel n Bool) (by positivity)
      (kernel_event_comp (Median.kernel n Bool) (by positivity)
        (kernel_event_comp (Median.kernel n Bool) (by positivity) (growth_segment hL hΔ hT₁ hgap)
          fun _ => linear_sat_segment hL) fun _ => quad_sat_segment hL hT₃)
      fun _ => consensus_segment hL
    -- pad to `⌈128 (log (n/Δ) + log log n)⌉₊ ≥ T₁ + 6 + T₃ + 8` rounds: consensus absorbs
    have hw0 : 0 ≤ log (n / Δ) := log_nonneg ((one_le_div (by linarith)).mpr hΔn)
    have hLL : 1 ≤ log (log n) :=
      (le_log_iff_exp_le (by linarith)).mpr (by linarith [exp_one_lt_d9])
    have hR : ((T₁ + 6 + T₃ + 8 : ℕ) : ℝ) ≤ 128 * (log (n / Δ) + log (log n)) := by
      push_cast
      linarith
    have hpad := event_absorb_mono (K := Median.kernel n Bool) (P := (· ∈ consSet))
      (fun _ ha => cons_absorb ha) _ _ x (Nat.cast_le.mp (hR.trans (Nat.le_ceil _)))
    -- the failure budget: `(T₁ + 6 + T₃ + 10) n⁻² ≤ 128/n`
    have hwn : log (n / Δ) ≤ log n := log_le_log (by positivity) (div_le_self hn0.le hΔ1)
    have hbud := mul_one_div_sq_le (S := T₁ + 6 + T₃ + 10) (C := 128) hn0
      (by linarith [log_le_sub_one_of_pos hn0, log_le_self (by linarith : 0 ≤ log n)])
    rw [← kernel_event_true]
    refine le_trans ?_ (h.trans hpad)
    linarith only [hbud]

variable {α : Type*} [LinearOrder α]

/-- **Consensus on a value with a margin on both sides.** If the nodes holding values `≥ v`
outnumber those holding values `< v`, and those holding values `≤ v` outnumber those holding
values `> v`, both by at least `Δ ≥ C √(n log n)`, then all nodes hold `v` after
`⌈C (log (n/Δ) + log log n)⌉` rounds with probability at least `1 - 2C/n`. -/
theorem median_consensus_fast : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n α) (v : α) (Δ : ℝ), C * √(n * Real.log n) ≤ Δ →
      Δ ≤ ((univ.filter fun u => v ≤ x u).card : ℝ) - (univ.filter fun u => x u < v).card →
      Δ ≤ ((univ.filter fun u => x u ≤ v).card : ℝ) - (univ.filter fun u => v < x u).card →
      1 - 2 * C / n ≤ expList (Round n) ⌈C * (Real.log (n / Δ) + Real.log (Real.log n))⌉₊
        (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) := by
  -- Two binary runs with the same samples: `u ↦ [v ≤ x u]` and `u ↦ [x u ≤ v]`. The median rule
  -- commutes with both thresholds, their gaps are the two margins, and when both end all-`true`
  -- all nodes hold `v` (`Median/ManyValuesThreshold.lean`). Union bound: failure `2C/n`.
  obtain ⟨C, hC, hbin⟩ := binary_consensus_fast
  refine ⟨C, hC, fun n _ hL x v Δ hΔ h₁ h₂ => ?_⟩
  have hup := hbin n hL (fun u => decide (v ≤ x u)) Δ hΔ (by rw [gap_upper]; exact h₁)
  have hlo := hbin n hL (fun u => decide (x u ≤ v)) Δ hΔ (by rw [gap_lower]; exact h₂)
  have h := expList_ge_of_and (T := ⌈C * (Real.log (n / Δ) + Real.log (Real.log n))⌉₊)
    fun l => run_eq_const_of_thresholds (x := x) (v := v) (l := l)
  rw [show 2 * C / (n : ℝ) = C / n + C / n by ring]
  linarith

/-- **An odd number of equally supported values: the middle one wins fast.** If the nodes hold
`2k+1` distinct values, each held by `n/(2k+1)` nodes, and `C (2k+1) √(n log n) ≤ n`, then the
middle value `v` (exactly `k` values below it) is held by all nodes after
`⌈C (log (2k+1) + log log n)⌉` rounds with probability at least `1 - C/n`. -/
theorem odd_split_consensus : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n α) (k : ℕ), (univ.image x).card = 2 * k + 1 →
      (∀ a ∈ univ.image x, ((univ.filter fun u => x u = a).card : ℝ) = n / (2 * k + 1)) →
      C * (2 * k + 1) * √(n * Real.log n) ≤ n →
      ∀ v ∈ univ.image x, ((univ.image x).filter (· < v)).card = k →
        1 - C / n ≤ expList (Round n) ⌈C * (Real.log (2 * k + 1) + Real.log (Real.log n))⌉₊
          (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) := by
  -- Both margins around `v` equal `n/(2k+1)` (counting fiber by fiber over the image,
  -- `Median/ManyValuesSplit.lean`), so this is `median_consensus_fast` with `Δ = n/(2k+1)`, where
  -- `log (n/Δ) = log (2k+1)`, and `C' = 2C`; the extra rounds are harmless (consensus absorbs).
  obtain ⟨C, hC, hmed⟩ := median_consensus_fast (α := α)
  refine ⟨2 * C, by positivity, fun n _ hL x k _ hc hsize v hv hlt => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hk0 : (0 : ℝ) < 2 * k + 1 := by positivity
  obtain ⟨m₁, m₂⟩ := odd_split_margins hc hv hlt
  -- the margin `n/(2k+1)` is at least `C √(n log n)`
  have hΔ : C * √(n * Real.log n) ≤ n / (2 * k + 1) := by
    rw [le_div_iff₀ hk0]
    have hs := mul_nonneg hC.le (mul_nonneg hk0.le (Real.sqrt_nonneg ((n : ℝ) * Real.log n)))
    linarith only [hs, hsize]
  have h := hmed n (by linarith) x v _ hΔ m₁.ge m₂.ge
  rw [div_div_cancel₀ hn0.ne'] at h
  exact h.trans (expList_run_const_mono x v (nat_ceil_mul_le_of_le hC.le (by linarith)))

end Median
