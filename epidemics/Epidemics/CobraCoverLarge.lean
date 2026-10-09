import Epidemics.CobraCoverGrowth
import Epidemics.CobraCoverEngineLarge
import Epidemics.CobraCoverEngineEnd

/-! # BIPS for large sets: growth to `9n/10` and the end phase (EPI-4, Lemmas 3 and 4)

Cooper, Radzik, Rivera, PODC 2016 (arXiv:1602.05768), Section 5, Lemmas 3 and 4.

Both lemmas start BIPS with source `v` from an arbitrary infected set `A₀` (the state reached by
the previous phase).

* **Lemma 3** (`bips_large_phase`): from `|A₀| ≥ 4000 log n/(1 - λ)²`, the infected set reaches
  `9n/10` within `24 log n/(1 - λ)` rounds, except with probability `T n^{-5}`: while
  `|A| < 9n/10`, Lemma 1 gives `E|A'| ≥ |A| (1 + (1 - λ)/10)` and the Chernoff bound (18) with
  `ε = √(10 log n/|A|) ≤ (1 - λ)/20` gives `|A'| ≥ |A| (1 + (1 - λ)/23)` except with probability
  `n^{-5}`.
* **Lemma 4** (`bips_end_phase`): from `|A₀| ≥ 9n/10`, when `(9/10) n ≥ 4000 log n/(1 - λ)²`,
  all vertices are infected after `8 log n/(1 - λ)` rounds, except with probability `n^{-5}`: the
  infected set stays above `9n/10` except with probability `t n^{-8}` (22), and the number `B_t`
  of healthy vertices satisfies `E B_{t+1} ≤ θ E B_t + t n^{-7}` with `θ = 1 - (9/10)(1 - λ²)`
  (21)–(23).
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

/-- **Lemma 3** (Section 5). Let `G` be `r`-regular (`r > 0`) with `λ = lambdaG G r < 1`, and
`k ≥ 2`. If BIPS with source `v` starts from a set `A₀` with `|A₀| ≥ 4000 log n/(1 - λ)²`, then
for every `T ≥ 24 log n/(1 - λ)` the probability that `|A_s| < 9n/10` for all `s ≤ T` is at most
`T/n⁵`. The paper states `23 log n/(1 - λ)` rounds and probability `1 - n^{-4}`; its doubling
count needs a minor correction (`log₂ n` doublings, not `ln n`), and `24 log n/(1 - λ)` rounds
suffice since `(1 + (1 - λ)/23)^T ≥ e^{T(1 - λ)/24}`. -/
theorem bips_large_phase {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (hlam : lambdaG G r < 1) (v : V) (A₀ : Finset V)
    (hA₀ : 4000 * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 2 ≤ A₀.card) {T : ℕ}
    (hT : 24 * Real.log (Fintype.card V) / (1 - lambdaG G r) ≤ T) :
    expList (Choices G k) T
        (fun l => if ∀ s ≤ T, 10 * (bipsRun v A₀ (l.take s)).card < 9 * Fintype.card V
          then (1 : ℝ) else 0) ≤
      T / (Fintype.card V : ℝ) ^ 5 := by
  classical
  haveI : Nonempty (Choices G k) := choices_nonempty_of_regular hreg hr
  haveI : Nonempty V := ⟨v⟩
  have hn : 2 ≤ Fintype.card V := two_le_card_of_pos_regular hreg hr
  have hc0 : 0 < 1 - lambdaG G r := by linarith
  have hc1 : 1 - lambdaG G r ≤ 1 := by linarith [lambdaG_nonneg G r]
  have hgrowth (A : Finset V) :
      (A.card : ℝ) * (1 + (1 - lambdaG G r) * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
    have hlam0 : 0 ≤ lambdaG G r := lambdaG_nonneg G r
    have hsq : lambdaG G r ^ 2 ≤ lambdaG G r := by
      simpa using pow_le_pow_of_le_one hlam0 (le_of_lt hlam) (by omega : 1 ≤ 2)
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
    round_large_phase (bipsStep v) hc0 hc1 hgrowth (fun A δ μ hδ0 hδ1 hμ =>
      bips_chernoff_lower v A hδ0 hδ1 hμ) hn hA₀ hT
  have heq :
      expList (Choices G k) T
          (fun l => if ∀ s ≤ T, 10 * (bipsRun v A₀ (l.take s)).card < 9 * Fintype.card V
            then (1 : ℝ) else 0) =
        expList (Choices G k) T (fun l =>
          if ∀ s ≤ T, 10 * (roundRun (bipsStep v) A₀ (l.take s)).card < 9 * Fintype.card V
            then (1 : ℝ) else 0) := by
    refine congrArg (expList (Choices G k) T) (funext fun l => ?_)
    refine if_congr ?_ rfl rfl
    simp [bipsRun, roundRun]
  exact heq.trans_le hphase

/-- **Lemma 4** (Section 5). Let `G` be `r`-regular (`r > 0`) with `λ = lambdaG G r < 1`, `k ≥ 2`,
and assume `4000 log n/(1 - λ)² ≤ (9/10) n` (the paper's `1 - λ ≫ √(log n / n)`). If BIPS with
source `v` starts from a set `A₀` with `|A₀| ≥ 9n/10`, then for every `T ≥ 8 log n/(1 - λ)` the
whole graph is infected at time `T` except with probability at most `n^{-5}`. The paper's proof
gives `n^{-5} + O(T² n^{-7})` (its `E B_T ≤ θ^T + ⋯` needs a minor correction to
`θ^T (n/10) + ⋯`, and its `T = 5 log n/log(1/θ)` should be `6 log n/log(1/θ)`); with
`B₀ ≤ n/10` and `T² ≤ n²` the total is at most `n^{-5}`. -/
theorem bips_end_phase {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (hlam : lambdaG G r < 1)
    (hn : 4000 * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 2 ≤ 9 * Fintype.card V / 10)
    (v : V) (A₀ : Finset V) (hA₀ : 9 * Fintype.card V ≤ 10 * A₀.card) {T : ℕ}
    (hT : 8 * Real.log (Fintype.card V) / (1 - lambdaG G r) ≤ T) :
    expList (Choices G k) T (fun l => if bipsRun v A₀ l = univ then (0 : ℝ) else 1) ≤
      1 / (Fintype.card V : ℝ) ^ 5 := by
  classical
  haveI : Nonempty (Choices G k) := choices_nonempty_of_regular hreg hr
  haveI : Nonempty V := ⟨v⟩
  have hn2 : 2 ≤ Fintype.card V := two_le_card_of_pos_regular hreg hr
  have hc0 : 0 < 1 - lambdaG G r := by linarith
  have hc1 : 1 - lambdaG G r ≤ 1 := by linarith [lambdaG_nonneg G r]
  have hgrowth (A : Finset V) :
      (A.card : ℝ) * (1 + (1 - lambdaG G r) * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤
        avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
    have hlam0 : 0 ≤ lambdaG G r := lambdaG_nonneg G r
    have hsq : lambdaG G r ^ 2 ≤ lambdaG G r := by
      simpa using pow_le_pow_of_le_one hlam0 (le_of_lt hlam) (by omega : 1 ≤ 2)
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
  have hgap : 4000 * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 2 ≤
      (9 / 10) * (Fintype.card V : ℝ) := by
    have hcast : ((9 * Fintype.card V / 10 : ℕ) : ℝ) ≤
        (9 : ℝ) * (Fintype.card V : ℝ) / 10 := by
      have hmul := Nat.div_mul_le_self (9 * Fintype.card V) 10
      have hR : ((9 * Fintype.card V / 10 : ℕ) : ℝ) * 10 ≤
          (9 : ℝ) * (Fintype.card V : ℝ) := by exact_mod_cast hmul
      rwa [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    have heq : (9 : ℝ) * (Fintype.card V : ℝ) / 10 = (9 / 10) * (Fintype.card V : ℝ) := by ring
    linarith
  have hphase :=
    round_end_phase (bipsStep v) hc0 hc1 hgrowth (fun A δ μ hδ0 hδ1 hμ =>
      bips_chernoff_lower v A hδ0 hδ1 hμ) (fun A B ρ h => bipsStep_mono v h ρ)
      (fun ρ => bipsStep_univ v (by omega) ρ) hn2 hgap hA₀ hT
  have heq :
      expList (Choices G k) T (fun l => if bipsRun v A₀ l = univ then (0 : ℝ) else 1) =
        expList (Choices G k) T (fun l =>
          if roundRun (bipsStep v) A₀ l = univ then (0 : ℝ) else 1) := by
    refine congrArg (expList (Choices G k) T) (funext fun l => ?_)
    refine if_congr ?_ rfl rfl
    simp [bipsRun, roundRun]
  exact heq.trans_le hphase

end Epidemics
