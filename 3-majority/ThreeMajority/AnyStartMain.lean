import ThreeMajority.AnyStartVsVoter
import ThreeMajority.AnyStartVoter
import ThreeMajority.AnyStartAsymptotics

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

/-- The probability of `k < F` is one minus that of `F ≤ k`. -/
lemma expList_lt_eq_one_sub {α : Type*} [Fintype α] [Nonempty α] (T k : ℕ) (F : List α → ℕ) :
    expList α T (fun l => if k < F l then (1 : ℝ) else 0) =
      1 - expList α T (fun l => if F l ≤ k then (1 : ℝ) else 0) := by
  have h : (fun l => if k < F l then (1 : ℝ) else 0) =
      fun l => 1 + (-1) * (if F l ≤ k then (1 : ℝ) else 0) := by
    funext l
    by_cases hl : F l ≤ k
    · rw [if_neg (not_lt.mpr hl), if_pos hl]
      ring
    · rw [if_pos (not_le.mp hl), if_neg hl]
      ring
  rw [h, expList_add, expList_const, expList_const_mul]
  ring

/-- **Phase 1** of Theorem 4 (BCEKMN17, Section 3, from Lemmas 2 and 3): from any configuration,
3-Majority has at most `k` colours after any `T ≥ 24 (n/k) log n` rounds, with probability at
least `1 − 1/n`. -/
theorem threeMaj_reduce_whp {n : ℕ} {σ : Type*} [Finite σ] [DecidableEq σ] (hn : 2 ≤ n)
    (c : Fin n → σ) {k : ℕ} (hk : 1 ≤ k) {T : ℕ}
    (hT : 24 * ((n : ℝ) / k) * Real.log n ≤ T) :
    expList (Tgt3 n) T (fun l => if k < numColours (runCol c l) then 1 else 0) ≤ 1 / n := by
  haveI : NeZero n := ⟨by omega⟩
  have hV := voter_reduce_whp hn c hk hT
  have hle := voter_le_threeMaj c k T
  rw [expList_lt_eq_one_sub] at hV ⊢
  linarith

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
  obtain ⟨C₂, N₂, h₂⟩ := h
  obtain ⟨C, N, hCN⟩ := anyStart_asymptotics |C₂| (abs_nonneg C₂)
  refine ⟨C, max N N₂, fun n hn c T hT => ?_⟩
  obtain ⟨hn2, hk1, hkpow, hrounds⟩ := hCN n (le_of_max_le_left hn)
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, k = phase1Colours n := ⟨_, rfl⟩
  rw [← hk] at hk1 hkpow hrounds
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  -- the Phase 2 length for `m ≤ k` colours is at most the one for `k` colours
  have hB (m : ℕ) (hm : m ≤ k) :
      C₂ * (((m : ℝ) ^ 2 * √(Real.log n) + m * Real.log n) * (m + Real.log n)) ≤
        |C₂| * (((k : ℝ) ^ 2 * √(Real.log n) + k * Real.log n) * (k + Real.log n)) := by
    have hmk : (m : ℝ) ≤ k := by exact_mod_cast hm
    have h0 : 0 ≤ ((m : ℝ) ^ 2 * √(Real.log n) + m * Real.log n) * (m + Real.log n) := by
      positivity
    calc _ ≤ |C₂| * (((m : ℝ) ^ 2 * √(Real.log n) + m * Real.log n) * (m + Real.log n)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C₂) h0
      _ ≤ _ := by gcongr
  -- Phase 1 takes `T₁ = ⌈24 (n/k) log n⌉` rounds, Phase 2 the remaining `T₂`
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, T₁ = ⌈24 * ((n : ℝ) / k) * Real.log n⌉₊ := ⟨_, rfl⟩
  have hT₁le : (T₁ : ℝ) ≤ 24 * ((n : ℝ) / k) * Real.log n + 1 :=
    hT₁ ▸ (Nat.ceil_lt_add_one (by positivity)).le
  have hBk : 0 ≤ |C₂| * (((k : ℝ) ^ 2 * √(Real.log n) + k * Real.log n) * (k + Real.log n)) := by
    positivity
  have hT₁T : T₁ ≤ T := by exact_mod_cast (by linarith : (T₁ : ℝ) ≤ T)
  obtain ⟨T₂, rfl⟩ : ∃ T₂, T = T₁ + T₂ := ⟨T - T₁, by omega⟩
  have hT₂ : |C₂| * (((k : ℝ) ^ 2 * √(Real.log n) + k * Real.log n) * (k + Real.log n)) ≤ T₂ := by
    push_cast at hT
    linarith
  rw [expList_append]
  calc expList (Tgt3 n) T₁ (fun l₁ => expList (Tgt3 n) T₂
          (fun l₂ => if numColours (runCol c (l₁ ++ l₂)) ≤ 1 then 0 else 1))
      ≤ expList (Tgt3 n) T₁
          (fun l₁ => (if k < numColours (runCol c l₁) then 1 else 0) + 1 / n) := by
        refine expList_le_expList fun l₁ => ?_
        by_cases hm : k < numColours (runCol c l₁)
        · -- Phase 1 failed: bound the probability by `1`
          rw [if_pos hm]
          calc _ ≤ expList (Tgt3 n) T₂ (fun _ => (1 : ℝ)) :=
                expList_le_expList fun l₂ => by split_ifs <;> norm_num
            _ = 1 := expList_const T₂ 1
            _ ≤ 1 + 1 / n := le_add_of_nonneg_right (by positivity)
        · -- Phase 1 succeeded: the cited Phase 2 bound applies to `runCol c l₁`
          rw [if_neg hm, zero_add]
          have hm' := not_lt.mp hm
          simp_rw [runCol_append]
          refine h₂ n (le_of_max_le_right hn) (runCol c l₁)
            ((Nat.cast_le.mpr hm').trans hkpow) T₂ ((hB _ hm').trans hT₂)
    _ = expList (Tgt3 n) T₁ (fun l₁ => if k < numColours (runCol c l₁) then 1 else 0) + 1 / n := by
        rw [expList_add, expList_const]
    _ ≤ 1 / n + 1 / n := by
        gcongr
        exact threeMaj_reduce_whp hn2 c hk1 (hT₁ ▸ Nat.le_ceil _)
    _ = 2 / n := by ring

end ThreeMajority
