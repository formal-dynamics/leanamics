import Epidemics.CobraCoverUnion
import Epidemics.CobraCoverGrowth

/-! # BIPS as a growth process (EPI-4, Theorems 1 and 2)

BIPS with source `v` satisfies the hypotheses (H1)–(H5) of `GrowthProcess` with rate
`c = 1 - λ`: the source is persistent (`source_mem_bipsStep`), the moment generating function
bound is `bips_mgf_le`, Lemma 1 (`bips_expected_growth`) gives growth with `1 - λ² ≥ 1 - λ`,
and BIPS is monotone with `V` absorbing. Theorems 1 and 2 are then the generic
`GrowthProcess.fail_le`, `GrowthProcess.tail_sum_le_log`, `cover_fail_le_log` and
`cover_tail_sum_le_log` with `c = 1 - λ`.
-/

namespace Epidemics
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Lowering the rate `c` weakens the growth bound `|A| (1 + c (1 - |A|/n)) ≤ X`. -/
lemma growth_of_rate_le {c c' X : ℝ} (hcc : c ≤ c') (A : Finset V)
    (h : (A.card : ℝ) * (1 + c' * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤ X) :
    (A.card : ℝ) * (1 + c * (1 - (A.card : ℝ) / ↑(Fintype.card V))) ≤ X := by
  refine le_trans ?_ h
  have hfrac : 0 ≤ 1 - (A.card : ℝ) / ↑(Fintype.card V) := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
    · rw [h0, Nat.cast_zero, div_zero, sub_zero]
      exact zero_le_one
    · rw [sub_nonneg, div_le_one (by exact_mod_cast hpos)]
      exact_mod_cast card_le_univ A
  have := mul_le_mul_of_nonneg_right hcc hfrac
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

variable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- **BIPS is a growth process with rate `1 - λ`** (for `k ≥ 2` and `λ < 1`). -/
theorem bips_growthProcess {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (hlam : lambdaG G r < 1) (v : V) :
    GrowthProcess (bipsStep v : Finset V → Choices G k → Finset V) v (1 - lambdaG G r) where
  src_mem A ρ := source_mem_bipsStep v A ρ
  mgf A ψ := bips_mgf_le v A ψ
  growth A := by
    have hlam0 : 0 ≤ lambdaG G r := lambdaG_nonneg G r
    have hsq : lambdaG G r ^ 2 ≤ lambdaG G r := by nlinarith
    exact growth_of_rate_le (by linarith) A (bips_expected_growth hreg hr hk v A)
  mono A B ρ h := bipsStep_mono v h ρ
  univ_eq ρ := bipsStep_univ v (by omega) ρ

/-- The gap hypothesis `128 √(log n/n) ≤ 1 - λ` gives `λ < 1` and `1 - λ ≤ 1` (`n ≥ 2`). -/
lemma lambdaG_lt_one_of_gap [Nonempty V] {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    (hgap : 128 * √(log (Fintype.card V) / Fintype.card V) ≤ 1 - lambdaG G r) :
    lambdaG G r < 1 ∧ 1 - lambdaG G r ≤ 1 := by
  have hc1 : 1 - lambdaG G r ≤ 1 := by linarith [lambdaG_nonneg G r]
  have := (gap_pos_and_half hc1 (two_le_card_of_pos_regular hreg hr) hgap).1
  exact ⟨by linarith, hc1⟩

end Epidemics
