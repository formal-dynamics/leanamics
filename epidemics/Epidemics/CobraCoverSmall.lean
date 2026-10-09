import Epidemics.CobraCoverGrowth
import Epidemics.CobraCoverEngine

/-! # BIPS from a single source: the small-set phase (EPI-4, Lemma 2)

Cooper, Radzik, Rivera, PODC 2016 (arXiv:1602.05768), Section 4, Lemma 2.

BIPS with persistent source `v` starts from `A₀ = {v}`. Lemma 2 says that the infected set exceeds
any size `m ≤ n/2` within `T = 13 m/(1 - λ) + 24 C log n/(1 - λ)²` rounds, except with probability
`n^{-C}`. Proof (exponential supermartingale): with `x = (1 - λ)/2`, `φ = log (1 + x)` and
`E_t = {|A_s| ≤ m for all s ≤ t}`, the quantity `G_t = E(e^{-φ(|A_t| - |A₀|)} 1_{E_{t-1}})`
satisfies `G_t ≤ e^{log(1 + x) - x} G_{t-1}` by Lemma 1 and the one-round MGF bound
(computations (8) to (16)), so `P(E_t) ≤ e^{φ m} G_t ≤ e^{m φ + t (log (1 + x) - x)} ≤ n^{-C}` (17).
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

/-- **Lemma 2** (Section 4). Let `G` be `r`-regular (`r > 0`) with `λ = lambdaG G r < 1`, let
`k ≥ 2`, `m ≤ n/2`, `C` real and `T ≥ 13 m/(1 - λ) + 24 C log n/(1 - λ)²`. Then BIPS with source
`v` started from `A₀ = {v}` has `|A_s| ≤ m` for all `s ≤ T` with probability at most `n^{-C}`;
that is, `|A_t| > m` for some `t ≤ T` with probability at least `1 - n^{-C}`. The paper states
`1 - O(n^{-C})` and `k = 2`; its proof gives exactly `n^{-C}` and works for `k ≥ 2`. -/
theorem bips_small_phase {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (hlam : lambdaG G r < 1) (v : V) {m T : ℕ} (hm : 2 * m ≤ Fintype.card V) (C : ℝ)
    (hT : 13 * (m : ℝ) / (1 - lambdaG G r) +
      24 * C * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 2 ≤ T) :
    expList (Choices G k) T
        (fun l => if ∀ s ≤ T, (bipsRun v {v} (l.take s)).card ≤ m then (1 : ℝ) else 0) ≤
      (Fintype.card V : ℝ) ^ (-C) := by
  classical
  haveI : Nonempty (Choices G k) := choices_nonempty_of_regular hreg hr
  have hc0 : 0 < 1 - lambdaG G r := by linarith
  have hc1 : 1 - lambdaG G r ≤ 1 := by linarith [lambdaG_nonneg G r]
  have hgrowth (A : Finset V) :
      (A.card : ℝ) * (1 + (1 - lambdaG G r) * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
    have hlam0 : 0 ≤ lambdaG G r := lambdaG_nonneg G r
    have hsq : lambdaG G r ^ 2 ≤ lambdaG G r := by
      simpa using pow_le_pow_of_le_one hlam0 (le_of_lt hlam) (by omega : 1 ≤ 2)
    haveI : Nonempty V := ⟨v⟩
    have hdiv : (A.card : ℝ) / ↑(Fintype.card V) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
      exact_mod_cast Finset.card_le_univ A
    have hfrac : 0 ≤ 1 - (A.card : ℝ) / ↑(Fintype.card V) := by linarith
    have hcoef : (1 - lambdaG G r) * (1 - (A.card : ℝ) / ↑(Fintype.card V)) ≤
        (1 - lambdaG G r ^ 2) * (1 - (A.card : ℝ) / ↑(Fintype.card V)) :=
      mul_le_mul_of_nonneg_right (by linarith) hfrac
    calc (A.card : ℝ) * (1 + (1 - lambdaG G r) * (1 - (A.card : ℝ) / ↑(Fintype.card V)))
        ≤ (A.card : ℝ) * (1 + (1 - lambdaG G r ^ 2) * (1 - (A.card : ℝ) / ↑(Fintype.card V))) :=
          mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast Nat.zero_le A.card)
      _ ≤ avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
          simpa using bips_expected_growth hreg hr hk v A
  have hphase :=
    round_small_phase (bipsStep v) v (fun A ρ => source_mem_bipsStep v A ρ)
      (fun A ψ => bips_mgf_le v A ψ) hc0 hc1 hgrowth hm C hT
  rw [smallProb] at hphase
  have heq :
      expList (Choices G k) T
          (fun l => if ∀ s ≤ T, (bipsRun v {v} (l.take s)).card ≤ m then (1 : ℝ) else 0) =
        expList (Choices G k) T (fun l =>
          if ∀ s ≤ T, (roundRun (bipsStep v) {v} (l.take s)).card ≤ m then (1 : ℝ) else 0) := by
    refine congrArg (expList (Choices G k) T) (funext fun l => ?_)
    refine if_congr ?_ rfl rfl
    simp [bipsRun, roundRun]
  exact (heq.trans_le hphase)

end Epidemics
