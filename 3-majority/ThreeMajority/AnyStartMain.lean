import ThreeMajority.AnyStartVsVoter
import ThreeMajority.AnyStartVoter

/-!
# 3-Majority from any configuration (BCEKMN17, Theorem 4; roadmap MAJ-6, part (b))

Theorem 4 of Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn, Natale (PODC 2017,
arXiv:1702.04921): from any configuration, 3-Majority reaches consensus w.h.p. within
`O(n^{3/4} log^{7/8} n)` rounds. The proof has two phases.

* Phase 1 (`threeMaj_reduce_whp`): from up to `n` colours to `k` colours within
  `24 (n/k) log n` rounds w.p. `≥ 1 − 1/n`, by Lemma 2 (3-Majority is at least as fast as
  Voter) and Lemma 3 (the Voter bound). It is used with `k ≈ n^{1/4} log^{1/8} n`.
* Phase 2: from `k ≤ n^{1/3−ε}` colours to consensus, the paper cites Theorem 3.1 of
  Becchetti, Clementi, Natale, Pasquale, Trevisan (*Stabilizing consensus with many opinions*,
  SODA 2016), restated as Theorem 8 of BCEKMN17. That result is not part of this paper and is
  not formalized here: `Bcnpt16Phase2 ε` states it for one `ε`, and the main theorem
  `threeMaj_anyStart_consensus` takes it as a hypothesis, exactly as the paper's proof does.
-/

namespace ThreeMajority

open Finset Dynamics

/-- **Phase 1** of Theorem 4 (BCEKMN17, Section 3, from Lemmas 2 and 3): from any configuration,
3-Majority has at most `k` colours after any `T ≥ 24 (n/k) log n` rounds, with probability at
least `1 − 1/n`. -/
theorem threeMaj_reduce_whp {n : ℕ} {σ : Type*} [Finite σ] [DecidableEq σ] (hn : 2 ≤ n)
    (c : Fin n → σ) {k : ℕ} (hk : 1 ≤ k) {T : ℕ}
    (hT : 24 * ((n : ℝ) / k) * Real.log n ≤ T) :
    expList (Tgt3 n) T (fun l => if k < numColours (runCol c l) then 1 else 0) ≤ 1 / n := by
  sorry

/-- **Theorem 8** of BCEKMN17 (Theorem 3.1 of Becchetti, Clementi, Natale, Pasquale, Trevisan,
SODA 2016), for one `ε`, as a hypothesis: there are constants `C, N` such that for `n ≥ N`, from
any configuration of colours in `[n]` with `k ≤ n^{1/3 − ε}` colours, 3-Majority reaches
consensus within any `T ≥ C (k² log^{1/2} n + k log n)(k + log n)` rounds, with probability at
least `1 − 1/n`. -/
def Bcnpt16Phase2 (ε : ℝ) : Prop :=
  ∃ C N : ℝ, ∀ n : ℕ, N ≤ n → ∀ c : Fin n → Fin n,
    (numColours c : ℝ) ≤ (n : ℝ) ^ (1 / 3 - ε) →
    ∀ T : ℕ, C * (((numColours c : ℝ) ^ 2 * √(Real.log n) + numColours c * Real.log n) *
        (numColours c + Real.log n)) ≤ T →
      expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) ≤ 1 / n

/-- **Theorem 4** (BCEKMN17): from any configuration of colours in `[n]`, 3-Majority reaches
consensus within any `T ≥ C n^{3/4} log^{7/8} n` rounds with probability at least `1 − 2/n`, for
`n ≥ N`. The cited Phase 2 result (Theorem 8, for `ε = 1/24`) is a hypothesis. -/
theorem threeMaj_anyStart_consensus (h : Bcnpt16Phase2 (1 / 24)) :
    ∃ C N : ℝ, ∀ n : ℕ, N ≤ n → ∀ c : Fin n → Fin n, ∀ T : ℕ,
      C * (n : ℝ) ^ ((3 : ℝ) / 4) * Real.log n ^ ((7 : ℝ) / 8) ≤ T →
        expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) ≤ 2 / n := by
  sorry

end ThreeMajority
