import Epidemics.CobraCoverSmall
import Epidemics.CobraCoverLarge
import Epidemics.CobraCoverChain
import Epidemics.CobraCoverSchedule

/-! # BIPS infection time (EPI-4, Theorem 2)

The three phases are chained at their first hitting times. From `{v}`, Lemma 2 reaches size
`m = ⌈4000 log n / (1 - λ)²⌉₊`; from any larger set, Lemma 3 reaches `9n/10` and Lemma 4
finishes the graph. `phase_schedule` puts the lengths under `60000 log n / (1 - λ)³` once
`1 - λ ≥ 128 √(log n / n)`.
-/

namespace Epidemics
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

omit [DecidableRel G.Adj] in
lemma bipsRun_append (v : V) (A : Finset V) (l₁ l₂ : List (Choices G k)) :
    bipsRun v A (l₁ ++ l₂) = bipsRun v (bipsRun v A l₁) l₂ := by
  simp [bipsRun, List.foldl_append]

/-- One BIPS run from `{v}` fails to infect `V` with probability at most `3/n³` after
`60000 log n / (1 - λ)³` rounds. -/
lemma bips_fail_le {k r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (v : V) (T : ℕ)
    (hgap : 128 * √(Real.log (Fintype.card V) / Fintype.card V) ≤ 1 - lambdaG G r)
    (hT : 60000 * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 3 ≤ T) :
    expList (Choices G k) T (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) ≤
      3 / (Fintype.card V : ℝ) ^ 3 := by
  classical
  haveI : Nonempty V := ⟨v⟩
  haveI : Nonempty (Choices G k) := choices_nonempty_of_regular hreg hr
  let n := Fintype.card V
  let y : ℝ := 1 - lambdaG G r
  have hn2 : 2 ≤ n := two_le_card_of_pos_regular hreg hr
  have hlog0 : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hy0 : 0 < y := by
    have hroot : 0 < √(log (n : ℝ) / n) :=
      sqrt_pos.mpr (div_pos hlog0 (by exact_mod_cast (show 0 < n by omega)))
    have : 0 < 128 * √(log (n : ℝ) / n) := mul_pos (by norm_num) hroot
    exact lt_of_lt_of_le this hgap
  have hy1 : y ≤ 1 := by linarith [lambdaG_nonneg G r]
  have hlam : lambdaG G r < 1 := by linarith
  let m := Nat.ceil (4000 * log (n : ℝ) / y ^ 2)
  let T₁ := Nat.ceil (13 * (m : ℝ) / y + 72 * log (n : ℝ) / y ^ 2)
  let T₂ := Nat.ceil (24 * log (n : ℝ) / y)
  let T₃ := Nat.ceil (8 * log (n : ℝ) / y)
  obtain ⟨_, htwo, hnat, hT2n, htime⟩ :=
    phase_schedule hn2 hy0 hy1 hgap rfl rfl rfl rfl
  let Pmed : Finset V → Prop := fun A => m < A.card
  let Pbig : Finset V → Prop := fun A => 9 * n ≤ 10 * A.card
  let Q : Finset V → Prop := fun A => A = univ
  have hEnd : ∀ b, Pbig b → ∀ T', T₃ ≤ T' →
      expList (Choices G k) T' (fun l => if Q (l.foldl (bipsStep v) b) then (0 : ℝ) else 1) ≤
        1 / (n : ℝ) ^ 5 := by
    intro b hb T' hT'
    have hTend : 8 * log (n : ℝ) / y ≤ T' := by
      refine le_trans (Nat.le_ceil (8 * log (n : ℝ) / y)) ?_
      exact_mod_cast hT'
    -- `phase_schedule` gives the integer quotient; Lemma 4 asks for the real one.
    have hnreal : 4000 * log (n : ℝ) / y ^ 2 ≤ 9 * (n : ℝ) / 10 := by
      refine hnat.trans ?_
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
      exact_mod_cast Nat.div_mul_le_self (9 * n) 10
    exact bips_end_phase hreg hr hk hlam hnreal v b hb hTend
  have hLarge : ∀ b, Pmed b → ∀ T', T₂ + T₃ ≤ T' →
      expList (Choices G k) T' (fun l => if Q (l.foldl (bipsStep v) b) then (0 : ℝ) else 1) ≤
        (T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5 := by
    intro b hb T' hT'
    have hhit := round_first_hit (bipsStep v) Pbig Q
      (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 5) hEnd b T₂ (T' - T₂) (by omega)
    have hsplit : T₂ + (T' - T₂) = T' := by omega
    rw [hsplit] at hhit
    have hsize : 4000 * log (n : ℝ) / y ^ 2 ≤ (b.card : ℝ) := by
      have hmle := Nat.le_ceil (4000 * log (n : ℝ) / y ^ 2)
      have hcard : m ≤ b.card := le_of_lt hb
      exact hmle.trans (by exact_mod_cast hcard)
    have hTl : 24 * log (n : ℝ) / y ≤ T₂ := Nat.le_ceil _
    have hbig := bips_large_phase hreg hr hk hlam v b hsize hTl
    have hnever :
        expList (Choices G k) T₂ (fun l =>
          if ∀ s ≤ T₂, ¬ Pbig ((l.take s).foldl (bipsStep v) b) then (1 : ℝ) else 0) ≤
          (T₂ : ℝ) / (n : ℝ) ^ 5 := by
      have heq :
          expList (Choices G k) T₂ (fun l =>
            if ∀ s ≤ T₂, ¬ Pbig ((l.take s).foldl (bipsStep v) b) then (1 : ℝ) else 0) =
            expList (Choices G k) T₂ (fun l =>
              if ∀ s ≤ T₂, 10 * (bipsRun v b (l.take s)).card < 9 * n then (1 : ℝ) else 0) := by
        refine congrArg (expList (Choices G k) T₂) (funext fun l => if_congr ?_ rfl rfl)
        refine forall_congr' fun s => imp_congr_right fun _ => ?_
        simp only [Pbig, bipsRun, Nat.not_le]
      exact heq.trans_le hbig
    linarith
  have hTs : 13 * (m : ℝ) / y + 24 * (3 : ℝ) * log (n : ℝ) / y ^ 2 ≤ T₁ := by
    have h72 : (24 : ℝ) * 3 = 72 := by norm_num
    rw [h72]
    exact Nat.le_ceil _
  have hsmall := bips_small_phase hreg hr hk hlam v htwo (3 : ℝ) hTs
  have hhit := round_first_hit (bipsStep v) Pmed Q
    (by positivity : (0 : ℝ) ≤ (T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5)
    hLarge ({v} : Finset V) T₁ (T₂ + T₃) le_rfl
  have hnever :
      expList (Choices G k) T₁ (fun l =>
        if ∀ s ≤ T₁, ¬ Pmed ((l.take s).foldl (bipsStep v) ({v} : Finset V)) then (1 : ℝ) else 0) ≤
        (n : ℝ) ^ (-3 : ℝ) := by
    have heq :
        expList (Choices G k) T₁ (fun l =>
          if ∀ s ≤ T₁, ¬ Pmed ((l.take s).foldl (bipsStep v) ({v} : Finset V))
            then (1 : ℝ) else 0) =
          expList (Choices G k) T₁ (fun l =>
            if ∀ s ≤ T₁, (bipsRun v {v} (l.take s)).card ≤ m then (1 : ℝ) else 0) := by
      refine congrArg (expList (Choices G k) T₁) (funext fun l => if_congr ?_ rfl rfl)
      refine forall_congr' fun s => imp_congr_right fun _ => ?_
      simp only [Pmed, bipsRun, Nat.not_lt]
    exact heq.trans_le hsmall
  have hAt : expList (Choices G k) (T₁ + T₂ + T₃)
      (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) ≤
      (n : ℝ) ^ (-3 : ℝ) + ((T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5) := by
    have hsum := hhit.trans (add_le_add_left hnever ((T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5))
    rw [← Nat.add_assoc] at hsum
    simp only [Q] at hsum
    exact hsum
  have hpow : (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 := by
    have hneg : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ (3 : ℝ))⁻¹ :=
      rpow_neg (by exact_mod_cast (show 0 ≤ n by omega)) _
    have hnat : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by
      rw [← Nat.cast_ofNat]
      exact rpow_natCast (n : ℝ) 3
    rw [hneg, hnat, ← one_div]
  have hnum : (T₂ : ℝ) / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 3 ≤
      3 / (n : ℝ) ^ 3 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hdiv : (T₂ : ℝ) / n ^ 5 ≤ n / n ^ 5 :=
      div_le_div_of_nonneg_right hT2n (pow_nonneg hn0.le 5)
    have hsplit : (n : ℝ) / n ^ 5 = 1 / n ^ 4 := by
      have hpow5 : (n : ℝ) ^ 5 = n * n ^ 4 := by ring
      rw [div_eq_mul_inv, div_eq_mul_inv, hpow5, mul_inv_rev, mul_comm ((n : ℝ) ^ 4)⁻¹,
        ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
    have h43 : 1 / (n : ℝ) ^ 4 ≤ 1 / n ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hn0 4) (pow_pos hn0 3), one_mul, one_mul]
      exact pow_le_pow_right₀ hone (by omega : 3 ≤ 4)
    have h53 : 1 / (n : ℝ) ^ 5 ≤ 1 / n ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hn0 5) (pow_pos hn0 3), one_mul, one_mul]
      exact pow_le_pow_right₀ hone (by omega : 3 ≤ 5)
    have hadd : (1 : ℝ) / n ^ 3 + 1 / n ^ 3 + 1 / n ^ 3 = 3 / n ^ 3 := by ring
    linarith
  have hphase : expList (Choices G k) (T₁ + T₂ + T₃)
      (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) ≤ 3 / (n : ℝ) ^ 3 := by
    rw [hpow] at hAt
    linarith
  have hsumle : T₁ + T₂ + T₃ ≤ T := by
    have hR : (T₁ : ℝ) + (T₂ : ℝ) + (T₃ : ℝ) ≤ (T : ℝ) := htime.trans hT
    exact_mod_cast hR
  have hmono (R : ℕ) : expList (Choices G k) ((T₁ + T₂ + T₃) + R)
      (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) ≤
      expList (Choices G k) (T₁ + T₂ + T₃)
        (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) := by
    rw [expList_append]
    refine expList_le_expList fun l₁ => ?_
    have hpoint : ∀ l₂,
        (if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) ≤
          if bipsRun v {v} l₁ = univ then 0 else 1 := by
      intro l₂
      by_cases hA : bipsRun v {v} l₁ = univ
      · have hfull : bipsRun v {v} (l₁ ++ l₂) = univ := by
          rw [bipsRun_append, hA, bipsRun_univ v (by omega)]
        simp [hA, hfull]
      · have : (if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) ≤ 1 := by
          split_ifs <;> norm_num
        simpa [hA] using this
    exact (expList_le_expList hpoint).trans_eq (expList_const R _)
  rw [show T = (T₁ + T₂ + T₃) + (T - (T₁ + T₂ + T₃)) by omega]
  exact (hmono _).trans hphase

/-- Every partial tail sum of `P(infec(v) > s)` is at most `130000 log n / (1 - λ)³`. -/
lemma bips_tail_sum_le {k r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (v : V) (H : ℕ)
    (hgap : 128 * √(Real.log (Fintype.card V) / Fintype.card V) ≤ 1 - lambdaG G r) :
    ∑ s ∈ range H,
        expList (Choices G k) s (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) ≤
      130000 * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 3 := by
  classical
  haveI : Nonempty V := ⟨v⟩
  haveI : Nonempty (Choices G k) := choices_nonempty_of_regular hreg hr
  let n := Fintype.card V
  let y : ℝ := 1 - lambdaG G r
  have hn2 : 2 ≤ n := two_le_card_of_pos_regular hreg hr
  have hlog0 : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hy0 : 0 < y := by
    have hroot : 0 < √(log (n : ℝ) / n) :=
      sqrt_pos.mpr (div_pos hlog0 (by exact_mod_cast (show 0 < n by omega)))
    exact lt_of_lt_of_le (mul_pos (by norm_num) hroot) hgap
  have hy1 : y ≤ 1 := by linarith [lambdaG_nonneg G r]
  let L : ℝ := log (n : ℝ) / y ^ 3
  let T₀ := Nat.ceil (60000 * L)
  have hT₀ : 60000 * log (n : ℝ) / y ^ 3 ≤ T₀ := by
    rw [show 60000 * log (n : ℝ) / y ^ 3 = 60000 * L by ring]
    exact Nat.le_ceil _
  have hfail := bips_fail_le hreg hr hk v T₀ hgap hT₀
  have hhalf : 3 / (n : ℝ) ^ 3 ≤ (1 : ℝ) / 2 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_le_iff₀ (pow_pos hn0 3)]
    have h8 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
      simpa [show (2 : ℝ) ^ 3 = 8 by norm_num] using hpow
    linarith
  let a : ℕ → ℝ := fun s =>
    expList (Choices G k) s (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1)
  have ha0 : ∀ s, 0 ≤ a s := fun s =>
    expList_nonneg fun l => by split_ifs <;> norm_num
  have ha1 : ∀ s, a s ≤ 1 := fun s =>
    expList_fail_le_one s (fun l => bipsRun v {v} l = univ)
  have hT0pos : 0 < T₀ := by
    have hLpos : 0 < 60000 * L := mul_pos (by norm_num) (div_pos hlog0 (pow_pos hy0 3))
    exact_mod_cast (lt_of_lt_of_le hLpos (Nat.le_ceil (60000 * L)))
  have hshift : ∀ s, a (s + T₀) ≤ (1 / 2) * a s := by
    intro s
    have happ : a (s + T₀) =
        expList (Choices G k) s fun l₁ => expList (Choices G k) T₀ fun l₂ =>
          if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1 := by
      simp only [a, expList_append]
    rw [happ]
    have hpt : ∀ l₁, expList (Choices G k) T₀
        (fun l₂ => if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) ≤
        (1 / 2) * (if bipsRun v {v} l₁ = univ then 0 else 1) := by
      intro l₁
      by_cases hA : bipsRun v {v} l₁ = univ
      · have hinner : ∀ l₂, bipsRun v {v} (l₁ ++ l₂) = univ := by
          intro l₂
          rw [bipsRun_append, hA, bipsRun_univ v (by omega)]
        have hzero : expList (Choices G k) T₀
            (fun l₂ => if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) = 0 := by
          have : (fun l₂ => if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) =
              fun _ => (0 : ℝ) := by funext l₂; simp [hinner l₂]
          rw [this, expList_const]
        rw [hzero, hA]
        norm_num
      · have hv : v ∈ bipsRun v {v} l₁ := source_mem_bipsRun v (by simp) l₁
        have hmono : ∀ l₂ : List (Choices G k),
            (if bipsRun v (bipsRun v {v} l₁) l₂ = univ then (0 : ℝ) else 1) ≤
              if bipsRun v {v} l₂ = univ then 0 else 1 := by
          intro l₂
          by_cases hsmall : bipsRun v {v} l₂ = univ
          · have hsub := bipsRun_mono v (singleton_subset_iff.mpr hv) l₂
            rw [hsmall] at hsub
            have hbig : bipsRun v (bipsRun v {v} l₁) l₂ = univ := univ_subset_iff.mp hsub
            simp [hsmall, hbig]
          · have : (if bipsRun v (bipsRun v {v} l₁) l₂ = univ then (0 : ℝ) else 1) ≤ 1 := by
              split_ifs <;> norm_num
            simpa [hsmall] using this
        have hrun : expList (Choices G k) T₀
            (fun l₂ => if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) ≤ a T₀ := by
          have heq : (fun l₂ => if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) =
              fun l₂ => if bipsRun v (bipsRun v {v} l₁) l₂ = univ then (0 : ℝ) else 1 := by
            funext l₂; simp [bipsRun_append]
          rw [heq]
          exact expList_le_expList hmono
        have : a T₀ ≤ 1 / 2 := hfail.trans hhalf
        have hle := hrun.trans this
        rw [if_neg hA]
        linarith
    have havg : expList (Choices G k) s
        (fun l₁ => expList (Choices G k) T₀
          (fun l₂ => if bipsRun v {v} (l₁ ++ l₂) = univ then (0 : ℝ) else 1)) ≤
        expList (Choices G k) s
          (fun l₁ => (1 / 2) * (if bipsRun v {v} l₁ = univ then 0 else 1)) :=
      expList_le_expList hpt
    rw [expList_const_mul] at havg
    simpa [a] using havg
  have hsum := sum_range_shift_le hT0pos (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1) ha0 ha1 hshift H
  have hden : (T₀ : ℝ) / (1 - 1 / 2) = 2 * (T₀ : ℝ) := by ring
  have hceil : (T₀ : ℝ) ≤ 60000 * L + 1 := le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hLge : log (n : ℝ) ≤ L := by
    rw [le_div_iff₀ (pow_pos hy0 3)]
    have hpow : y ^ 3 ≤ 1 := pow_le_one₀ hy0.le hy1
    exact (mul_le_mul_of_nonneg_left hpow hlog0.le).trans_eq (mul_one _)
  have hlog2 : log 2 ≤ log (n : ℝ) :=
    log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn2)
  have htwo : (2 : ℝ) ≤ 10000 * L := by
    have := log_two_gt_d9
    nlinarith
  have hscale : 2 * (T₀ : ℝ) ≤ 130000 * L := by
    have : 120000 * L + 2 ≤ 130000 * L := by linarith
    linarith
  calc ∑ s ∈ range H, a s ≤ (T₀ : ℝ) / (1 - 1 / 2) := hsum
    _ = 2 * (T₀ : ℝ) := hden
    _ ≤ 130000 * L := hscale
    _ = 130000 * log (n : ℝ) / y ^ 3 := by ring

end Epidemics
