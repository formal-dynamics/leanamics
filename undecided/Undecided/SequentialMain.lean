import Undecided.SequentialWhp

/-! # Fast robust approximate majority: main results of [AAE08]

Angluin, Aspnes and Eisenstat, *A simple population protocol for fast robust approximate
majority*, Distributed Computing 21 (2008) [AAE08], for the protocol of `Undecided.Sequential`
(`x ↦ Op.a`, `y ↦ Op.b`, blank `↦ Op.u`), with `n ≥ 2` agents and natural logarithms.

* [AAE08, Theorem 1] (`consensus_whp`): from every non-blank configuration, consensus (all `x` or
  all `y`) is reached within `O(n log n)` interactions with probability `1 - O(n^{-c})`, for every
  fixed `c`.
* [AAE08, Theorem 2] (`majority_whp`): if the initial majority `x` exceeds the minority by
  `C √n log n`, then the consensus is on `x`, with the same time and probability bounds.
* `approximate_majority`: the case `c = 1` of the latter.

Consensus configurations are absorbing, so "consensus at every time `T ≥ C n log n`" is the same
as "consensus within `C n log n` interactions". The paper's explicit constants, its "sufficiently
large `n`" and its `ω(√n log n)` are absorbed into one existential constant `C`, which depends on
the error exponent `c`. See `undecided/FORMALIZATION_DIFFERENCES.md` for the comparison with the
paper's statements.
-/

namespace Undecided.Sequential
open Dynamics

/-- **Convergence** [AAE08, Theorem 1]. For every error exponent `c` there is a constant `C` such
that, for every `n ≥ 2` and every non-blank configuration `s` of `n` agents, after any number
`T ≥ C n log n` of uniformly random interactions all agents hold `x` or all hold `y`
(`x_T = n` or `y_T = n`), with probability at least `1 - C / n ^ c`.

The paper's bound is `Pr[τ* ≥ 6769 n log n + 6773 c n log n + 2552 n] ≤ 5 n^{-c}` for every fixed
`c > 0` and sufficiently large `n`, where `τ*` is the first time with `x = n` or `y = n`. -/
theorem consensus_whp (c : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ s : Config n, (∃ v, s v ≠ .u) →
      ∀ T : ℕ, C * n * Real.log n ≤ T →
        1 - C / (n : ℝ) ^ c ≤ expList (Interaction n) T
          (fun l => if count (run s l) .a = n ∨ count (run s l) .b = n then (1 : ℝ) else 0) := by
  refine ⟨constC c, fun n hn s hs T hT => ?_⟩
  rcases lt_or_ge n 16 with hsmall | hbig
  · exact le_trans (small_n c hn hsmall) (expList_nonneg fun l => by split <;> norm_num)
  haveI := nonempty_interaction hn
  have key := prob_notCons_le hbig s (nonblank_of_exists hs) _ T (threshold_le c hbig T hT)
  have hind : (fun l => if count (run s l) .a = n ∨ count (run s l) .b = n then (1 : ℝ) else 0) =
      fun l => 1 - (if Cons (run s l) then 0 else 1) := by
    funext l
    by_cases h : Cons (run s l)
    · rw [if_pos h, if_pos (show count (run s l) .a = n ∨ count (run s l) .b = n from h)]; ring
    · rw [if_neg h, if_neg (show ¬(count (run s l) .a = n ∨ count (run s l) .b = n) from h)]
      ring
  rw [hind, expList_one_sub]
  have herr := error_le c hbig 0 (by positivity)
  linarith

/-- **Correctness** [AAE08, Theorem 2], with the convergence time of [AAE08, Theorem 1]. For
every error exponent `c` there is a constant `C` such that, for every `n ≥ 2` and every
configuration `s` of `n` agents (blanks allowed) in which the `x`-agents outnumber the `y`-agents
by at least `C √n log n`, after any number `T ≥ C n log n` of uniformly random interactions all
agents hold `x`, with probability at least `1 - C / n ^ c`.

The paper assumes a difference `ω(√n log n)` between the initial majority and minority
populations, and concludes convergence to the majority with high probability. -/
theorem majority_whp (c : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ s : Config n,
      C * √(n : ℝ) * Real.log n ≤ (count s .a : ℝ) - count s .b →
      ∀ T : ℕ, C * n * Real.log n ≤ T →
        1 - C / (n : ℝ) ^ c ≤ expList (Interaction n) T
          (fun l => if count (run s l) .a = n then (1 : ℝ) else 0) := by
  refine ⟨constC c, fun n hn s hgap T hT => ?_⟩
  rcases lt_or_ge n 16 with hsmall | hbig
  · exact le_trans (small_n c hn hsmall) (expList_nonneg fun l => by split <;> norm_num)
  haveI := nonempty_interaction hn
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hbig
  have hpos : 0 < constC c * √(n : ℝ) * Real.log n := by
    have h1 := constC_ge c
    have h2 := one_le_log hbig
    have h3 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have h4 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    exact mul_pos (mul_pos (by linarith) h3) (by linarith)
  have hu : count s .b < count s .a := by
    have : (count s .b : ℝ) < count s .a := by linarith
    exact_mod_cast this
  have key := prob_notAllX_le hbig s hu (L := ((c + 2 : ℕ) : ℝ) * Real.log n) (by positivity) T
    (threshold_le c hbig T hT)
  have hind : (fun l => if count (run s l) .a = n then (1 : ℝ) else 0) =
      fun l => 1 - (if count (run s l) .a = n then 0 else 1) := by
    funext l
    by_cases h : count (run s l) .a = n
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [hind, expList_one_sub]
  have herr := error_le c hbig _ (gap_error_le c hbig _ hgap)
  linarith

/-- **Approximate majority** (roadmap UND-2; [AAE08, Theorems 1 and 2] with error `O(1/n)`).
There is a constant `C` such that, from any configuration of `n ≥ 2` agents whose initial gap
`x₀ - y₀` is at least `C √n log n`, the initial majority `x` wins within `C n log n` interactions
with probability at least `1 - C / n`. -/
theorem approximate_majority :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ s : Config n,
      C * √(n : ℝ) * Real.log n ≤ (count s .a : ℝ) - count s .b →
      ∀ T : ℕ, C * n * Real.log n ≤ T →
        1 - C / n ≤ expList (Interaction n) T
          (fun l => if count (run s l) .a = n then (1 : ℝ) else 0) := by
  obtain ⟨C, hC⟩ := majority_whp 1
  exact ⟨C, fun n hn s hgap T hT => by simpa [pow_one] using hC n hn s hgap T hT⟩

end Undecided.Sequential
