import Median.Basic
import Median.Binary
import Median.AnyStartAux

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
  sorry

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **Reduction to two values.** If every binary configuration fails to reach consensus within
`T` rounds with probability at most `ε`, then a configuration with `m` distinct values fails with
probability at most `(m - 1) ε`. -/
theorem consensus_of_binary [NeZero n] {T : ℕ} {ε : ℝ}
    (hbin : ∀ y : Config n Bool, expList (Round n) T (fun l => notConsensus (run y l)) ≤ ε)
    (x : Config n α) :
    expList (Round n) T (fun l => notConsensus (run x l)) ≤ (((univ.image x).card : ℝ) - 1) * ε := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set S := univ.image x with hS
  have hSne : S.Nonempty := ⟨x ⟨0, hn⟩, Finset.mem_image_of_mem x (Finset.mem_univ _)⟩
  set m := S.min' hSne with hm
  have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hmem : m ∈ S := Finset.min'_mem S hSne
  -- pointwise, a failure of `x` is witnessed by a failed threshold configuration
  have hpt : ∀ l : List (Round n), notConsensus (run x l)
      ≤ ∑ b ∈ S.erase m, notConsensus (run (fun v => decide (b ≤ x v)) l) := by
    intro l
    rcases notConsensus_cases' (run x l) with h0 | h1
    · rw [h0]
      exact Finset.sum_nonneg fun b _ => notConsensus_nonneg' _
    · have hnc : ¬ Consensus (run x l) := by
        intro hc
        rw [notConsensus_cons' hc] at h1
        norm_num at h1
      obtain ⟨u, v, huv⟩ : ∃ u v : Fin n, run x l u ≠ run x l v := by
        by_contra hcon
        push Not at hcon
        exact hnc ⟨run x l ⟨0, hn⟩, fun w => hcon _ _⟩
      have key : ∀ u v : Fin n, run x l u < run x l v →
          1 ≤ ∑ b ∈ S.erase m, notConsensus (run (fun w => decide (b ≤ x w)) l) := by
        intro u v hlt
        have hbS : run x l v ∈ S := run_mem_image x l v
        have haS : run x l u ∈ S := run_mem_image x l u
        have hbm : run x l v ≠ m := by
          intro heq
          have hminle : m ≤ run x l u := Finset.min'_le S _ haS
          rw [heq] at hlt
          exact absurd hlt (not_lt.mpr hminle)
        have hmemE : run x l v ∈ S.erase m := Finset.mem_erase.mpr ⟨hbm, hbS⟩
        have hthr : run (fun w => decide (run x l v ≤ x w)) l
            = fun w => decide (run x l v ≤ run x l w) := (threshold_run _ x l).symm
        have hnc2 : ¬ Consensus (run (fun w => decide (run x l v ≤ x w)) l) := by
          rintro ⟨c, hc⟩
          have hu : decide (run x l v ≤ run x l u) = c := by
            have := hc u
            rw [hthr] at this
            exact this
          have hv : decide (run x l v ≤ run x l v) = c := by
            have := hc v
            rw [hthr] at this
            exact this
          rw [decide_eq_false (not_le.mpr hlt)] at hu
          rw [decide_eq_true (le_refl _)] at hv
          exact absurd hv (by rw [← hu]; simp)
        have hone : notConsensus (run (fun w => decide (run x l v ≤ x w)) l) = 1 :=
          notConsensus_noncons' hnc2
        have hsingle : notConsensus (run (fun w => decide (run x l v ≤ x w)) l)
            ≤ ∑ b ∈ S.erase m, notConsensus (run (fun w => decide (b ≤ x w)) l) :=
          Finset.single_le_sum (f := fun b => notConsensus (run (fun w => decide (b ≤ x w)) l))
            (fun b _ => notConsensus_nonneg' _) hmemE
        rwa [hone] at hsingle
      rcases lt_or_gt_of_ne huv with h | h
      · rw [h1]; exact key u v h
      · rw [h1]; exact key v u h
  calc expList (Round n) T (fun l => notConsensus (run x l))
      ≤ expList (Round n) T
          (fun l => ∑ b ∈ S.erase m, notConsensus (run (fun v => decide (b ≤ x v)) l)) :=
        expList_le_expList hpt
    _ = ∑ b ∈ S.erase m,
          expList (Round n) T (fun l => notConsensus (run (fun v => decide (b ≤ x v)) l)) :=
        expList_finset_sum T _ _
    _ ≤ ∑ b ∈ S.erase m, ε := Finset.sum_le_sum fun b _ => hbin _
    _ = ((S.erase m).card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((S.card : ℝ) - 1) * ε := by
        rw [Finset.card_erase_of_mem hmem, Nat.cast_sub hcard1, Nat.cast_one]

/-- **Consensus from any configuration** (the paper's Theorem 1, no adversary). From any
configuration with values in a linear order, all nodes agree after `⌈C log n⌉` rounds except
with probability at most `C/n`. -/
theorem median_consensus_any : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n α,
      expList (Round n) ⌈C * Real.log n⌉₊ (fun l => notConsensus (run x l)) ≤ C / n := by
  obtain ⟨C₀, hC₀pos, hbin⟩ := binary_any_start
  refine ⟨3 * C₀ + 3, by positivity, ?_⟩
  intro n _ hC x
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hL1 : (1 : ℝ) ≤ Real.log n := le_trans (by linarith) hC
  have hC₀L : C₀ ≤ Real.log n := by
    have hle : C₀ ≤ 3 * C₀ + 3 := by nlinarith
    exact hle.trans hC
  have hne : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  -- the binary bound of `binary_any_start`, amplified over three blocks
  have hbin3 : ∀ y : Config n Bool, expList (Round n) (3 * ⌈C₀ * Real.log n⌉₊)
      (fun l => notConsensus (run y l)) ≤ (C₀ / (n : ℝ)) ^ 3 :=
    fun y => expList_amplify (hbin n hC₀L) 3 y
  -- the reduction to two values, with at most `n` distinct values
  have hred := consensus_of_binary (T := 3 * ⌈C₀ * Real.log n⌉₊)
    (ε := (C₀ / (n : ℝ)) ^ 3) hbin3 x
  have hcard : (((univ.image x).card : ℝ) - 1) ≤ (n : ℝ) := by
    have hcardn : (univ.image x).card ≤ n := by
      simpa using Finset.card_image_le (f := x) (s := (univ : Finset (Fin n)))
    have h1 : (1 : ℕ) ≤ (univ.image x).card :=
      Finset.card_pos.mpr ⟨x ⟨0, hn⟩, Finset.mem_image_of_mem x (Finset.mem_univ _)⟩
    have hcast : (((univ.image x).card : ℝ) - 1) = (((univ.image x).card - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub h1, Nat.cast_one]
    rw [hcast]
    exact_mod_cast (Nat.sub_le (univ.image x).card 1).trans hcardn
  -- the constant `C₀` is small enough that `C₀³ ≤ n`
  have hcube : C₀ ^ 3 ≤ (n : ℝ) := by
    by_cases h1 : C₀ ≤ 1
    · have h13 : C₀ ^ 3 ≤ 1 := pow_le_one₀ hC₀pos.le h1
      exact h13.trans (by exact_mod_cast hn)
    · have h1' : 1 < C₀ := not_le.mp h1
      have hle : 3 * Real.log C₀ ≤ 3 * C₀ + 3 := by
        have hl : Real.log C₀ ≤ C₀ := Real.log_le_self hC₀pos.le
        nlinarith
      have hle2 : 3 * Real.log C₀ ≤ Real.log n := hle.trans hC
      have hex : Real.exp (3 * Real.log C₀) = C₀ ^ 3 := by
        rw [show (3 : ℝ) * Real.log C₀ = ((3 : ℕ) : ℝ) * Real.log C₀ by norm_num,
          Real.exp_nat_mul, Real.exp_log hC₀pos]
      have hexpn : Real.exp (3 * Real.log C₀) ≤ Real.exp (Real.log n) :=
        Real.exp_le_exp.mpr hle2
      rwa [hex, Real.exp_log hnR] at hexpn
  -- failure within `3 ⌈C₀ log n⌉₊` rounds is at most `1/n`
  have hpow : (0 : ℝ) ≤ C₀ / (n : ℝ) := div_nonneg hC₀pos.le hnR.le
  have h3T : expList (Round n) (3 * ⌈C₀ * Real.log n⌉₊)
      (fun l => notConsensus (run x l)) ≤ 1 / (n : ℝ) := by
    have h2 : (((univ.image x).card : ℝ) - 1) * (C₀ / (n : ℝ)) ^ 3
        ≤ (n : ℝ) * (C₀ / (n : ℝ)) ^ 3 :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hpow 3)
    have hval : (n : ℝ) * (C₀ / (n : ℝ)) ^ 3 = C₀ ^ 3 / (n : ℝ) ^ 2 := by
      field_simp
    have h3 : (n : ℝ) * (C₀ / (n : ℝ)) ^ 3 ≤ 1 / (n : ℝ) := by
      rw [hval, div_le_div_iff₀ (pow_pos hnR 2) hnR]
      nlinarith [hcube, hnR]
    exact hred.trans (h2.trans h3)
  -- the round counts fit: `3 ⌈C₀ log n⌉₊ < (3C₀ + 3) log n ≤ ⌈(3C₀ + 3) log n⌉₊`
  have hTn : ((⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < C₀ * Real.log n + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hC₀pos.le (by linarith))
  have h3Tlt : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < 3 * C₀ * Real.log n + 3 := by
    have h1 : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) = 3 * ((⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) := by
      push_cast
      ring
    rw [h1]
    nlinarith [hTn]
  have hmid : 3 * C₀ * Real.log n + 3 ≤ (3 * C₀ + 3) * Real.log n := by
    have hexp : (3 : ℝ) ≤ 3 * Real.log n := by linarith
    nlinarith [hexp]
  have hceil : 3 * ⌈C₀ * Real.log n⌉₊ ≤ ⌈(3 * C₀ + 3) * Real.log n⌉₊ := by
    have hlt : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < (3 * C₀ + 3) * Real.log n :=
      lt_of_lt_of_le h3Tlt hmid
    have hle : (3 * C₀ + 3) * Real.log n
        ≤ ((⌈(3 * C₀ + 3) * Real.log n⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hlt' : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < ((⌈(3 * C₀ + 3) * Real.log n⌉₊ : ℕ) : ℝ) :=
      lt_of_lt_of_le hlt hle
    exact_mod_cast hlt'.le
  -- pad up to `⌈C log n⌉₊` rounds using that consensus absorbs
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ⌈(3 * C₀ + 3) * Real.log n⌉₊ = 3 * ⌈C₀ * Real.log n⌉₊ + d :=
    ⟨⌈(3 * C₀ + 3) * Real.log n⌉₊ - 3 * ⌈C₀ * Real.log n⌉₊, by omega⟩
  rw [hd]
  refine le_trans (expList_run_anti x (3 * ⌈C₀ * Real.log n⌉₊) d) ?_
  have hlast : 1 / (n : ℝ) ≤ (3 * C₀ + 3) / (n : ℝ) := by
    rw [div_le_div_iff₀ hnR hnR]
    nlinarith
  exact h3T.trans hlast

end Median
