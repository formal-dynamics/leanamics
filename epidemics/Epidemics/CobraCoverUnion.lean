import Epidemics.CobraCoverPhases

/-! # From the infection time to the cover time (EPI-4, Theorems 1 and 3)

Cooper, Radzik, Rivera, PODC 2016 (arXiv:1602.05768), proof of Theorem 1 and equation (1).

The argument only uses three facts about a COBRA-like step `cstep` and a family of BIPS-like steps
`bstep w` (source `w`), so it is stated once for both branching factors `k` and `1 + ρ`:

* the duality `P(Hit_C(w) > t) = P(C ∩ A_t = ∅ ∣ A₀ = {w})` (Theorem 4);
* `cstep` maps nonempty sets to nonempty sets;
* the BIPS failure bound `P(A_T ≠ V ∣ A₀ = {w}) ≤ ε`.

*Cover time.* `⋃_{t=1}^T C_t ≠ V` iff some `w` is missed at the times `1, …, T`. For a fixed `w`,
splitting off the first round, missing `w` at the times `1, …, T₀ + 1` from `D` is not hitting
`w` within `T₀` rounds from `C₁ = cstep D ρ ≠ ∅`, which by duality has probability
`P(C₁ ∩ A_{T₀} = ∅) ≤ P(A_{T₀} ≠ V) ≤ ε`; the union bound over `w` gives `n ε`
(`cover_fail_le`).

*Expectation* (equation (1)). After `s` rounds COBRA restarts from the nonempty set `C_s`, so
`P(cov > s + T₀ + 1) ≤ n ε P(cov > s)`; with `n ε ≤ 1/2` every partial tail sum is at most
`2 (T₀ + 1)` (`cover_tail_sum_le`).
-/

namespace Epidemics
open Finset Dynamics Real

lemma List.take_append_length_add {α : Type*} (l₁ l₂ : List α) (t : ℕ) :
    (l₁ ++ l₂).take (l₁.length + t) = l₁ ++ l₂.take t := by
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R]
variable (cstep : Finset V → R → Finset V) (bstep : V → Finset V → R → Finset V)

omit [Fintype R] [Nonempty R] in
/-- **Union bound, pathwise**: if `⋃_{t=1}^T C_t ≠ V`, some vertex is missed at all the times
`1, …, T`. -/
lemma not_cover_le_sum (D : Finset V) (T : ℕ) (l : List R) :
    (if (Icc 1 T).biUnion (fun s => roundRun cstep D (l.take s)) = univ then (0 : ℝ) else 1) ≤
      ∑ w : V, if w ∉ (Icc 1 T).biUnion (fun s => roundRun cstep D (l.take s))
        then (1 : ℝ) else 0 := by
  have hnn : ∀ w ∈ (univ : Finset V),
      0 ≤ if w ∉ (Icc 1 T).biUnion (fun s => roundRun cstep D (l.take s)) then (1 : ℝ) else 0 :=
    fun w _ => by split_ifs <;> norm_num
  split_ifs with h
  · exact sum_nonneg hnn
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ (Icc 1 T).biUnion (fun s => roundRun cstep D (l.take s)) := by
      by_contra hcon
      push Not at hcon
      exact h (eq_univ_iff_forall.mpr hcon)
    refine le_of_eq_of_le ?_ (single_le_sum hnn (mem_univ w))
    rw [if_pos hw]

omit [Fintype V] [DecidableEq V] [Fintype R] [Nonempty R] in
lemma roundRun_nonempty (hne : ∀ D ρ, D.Nonempty → (cstep D ρ).Nonempty) {D : Finset V}
    (hD : D.Nonempty) (l : List R) : (roundRun cstep D l).Nonempty := by
  induction l generalizing D with
  | nil => exact hD
  | cons ρ l ih => exact ih (hne D ρ hD)

/-- **One vertex.** By the first-round split and the duality, COBRA from a nonempty `D` misses
`w` at all the times `1, …, T₀ + 1` with probability at most `P(A_{T₀} ≠ V ∣ A₀ = {w})`. -/
lemma miss_le
    (hdual : ∀ (w : V) (C : Finset V) (t : ℕ),
      expList R t (fun l => if ∀ s ≤ t, w ∉ roundRun cstep C (l.take s) then (1 : ℝ) else 0) =
        expList R t (fun l => if C ∩ roundRun (bstep w) {w} l = ∅ then (1 : ℝ) else 0))
    (hne : ∀ D ρ, D.Nonempty → (cstep D ρ).Nonempty) (w : V) {T₀ : ℕ} {ε : ℝ}
    (hfail : expList R T₀ (fun l => if roundRun (bstep w) {w} l = univ then (0 : ℝ) else 1) ≤ ε)
    {D : Finset V} (hD : D.Nonempty) :
    expList R (T₀ + 1) (fun l =>
        if w ∉ (Icc 1 (T₀ + 1)).biUnion (fun s => roundRun cstep D (l.take s))
          then (1 : ℝ) else 0) ≤
      ε := by
  rw [expList_succ]
  refine (avg_le_avg fun ρ => ?_).trans_eq (avg_const ε)
  have hiff : ∀ l : List R,
      w ∉ (Icc 1 (T₀ + 1)).biUnion (fun s => roundRun cstep D ((ρ :: l).take s)) ↔
      ∀ s ≤ T₀, w ∉ roundRun cstep (cstep D ρ) (l.take s) := by
    intro l
    rw [mem_biUnion]
    push Not
    constructor
    · intro h s hs
      have := h (s + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
      rwa [roundRun_take_succ] at this
    · intro h s hs
      obtain ⟨hs1, hs2⟩ := mem_Icc.mp hs
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      rw [roundRun_take_succ]
      exact h t (by omega)
  simp_rw [hiff]
  rw [hdual w (cstep D ρ) T₀]
  refine le_trans (expList_le_expList fun l => ?_) hfail
  have hne' := hne D ρ hD
  split_ifs with h1 h2 h2
  · rw [h2, inter_univ] at h1
    exact absurd h1 hne'.ne_empty
  all_goals norm_num

/-- **Cover time, union bound** (proof of Theorem 1): if `P(A_{T₀} ≠ V ∣ A₀ = {w}) ≤ ε` for
every `w`, COBRA from a nonempty `D` has `⋃_{t=1}^{T₀+1} C_t ≠ V` with probability at most
`n ε`. -/
theorem cover_fail_le
    (hdual : ∀ (w : V) (C : Finset V) (t : ℕ),
      expList R t (fun l => if ∀ s ≤ t, w ∉ roundRun cstep C (l.take s) then (1 : ℝ) else 0) =
        expList R t (fun l => if C ∩ roundRun (bstep w) {w} l = ∅ then (1 : ℝ) else 0))
    (hne : ∀ D ρ, D.Nonempty → (cstep D ρ).Nonempty) {T₀ : ℕ} {ε : ℝ}
    (hfail : ∀ w,
      expList R T₀ (fun l => if roundRun (bstep w) {w} l = univ then (0 : ℝ) else 1) ≤ ε)
    {D : Finset V} (hD : D.Nonempty) :
    expList R (T₀ + 1) (fun l =>
        if (Icc 1 (T₀ + 1)).biUnion (fun s => roundRun cstep D (l.take s)) = univ
          then (0 : ℝ) else 1) ≤
      Fintype.card V * ε := by
  refine (expList_le_expList fun l => not_cover_le_sum cstep D (T₀ + 1) l).trans ?_
  rw [expList_finset_sum (T₀ + 1) univ (fun w l =>
    if w ∉ (Icc 1 (T₀ + 1)).biUnion (fun s => roundRun cstep D (l.take s)) then (1 : ℝ) else 0)]
  refine (sum_le_sum fun w _ => miss_le cstep bstep hdual hne w (hfail w) hD).trans_eq ?_
  rw [sum_const, card_univ, nsmul_eq_mul]

/-- **Restarting COBRA** (equation (1)): under the hypotheses of `cover_fail_le` and
`n ε ≤ 1/2`, every partial tail sum `∑_{s < H} P(⋃_{t=1}^s C_t ≠ V)` is at most
`2 (T₀ + 1)`. -/
theorem cover_tail_sum_le
    (hdual : ∀ (w : V) (C : Finset V) (t : ℕ),
      expList R t (fun l => if ∀ s ≤ t, w ∉ roundRun cstep C (l.take s) then (1 : ℝ) else 0) =
        expList R t (fun l => if C ∩ roundRun (bstep w) {w} l = ∅ then (1 : ℝ) else 0))
    (hne : ∀ D ρ, D.Nonempty → (cstep D ρ).Nonempty) {T₀ : ℕ} {ε : ℝ}
    (hfail : ∀ w,
      expList R T₀ (fun l => if roundRun (bstep w) {w} l = univ then (0 : ℝ) else 1) ≤ ε)
    (hhalf : Fintype.card V * ε ≤ 1 / 2) {D : Finset V} (hD : D.Nonempty) (H : ℕ) :
    ∑ s ∈ range H, expList R s (fun l =>
        if (Icc 1 s).biUnion (fun t => roundRun cstep D (l.take t)) = univ then (0 : ℝ) else 1) ≤
      2 * ((T₀ : ℝ) + 1) := by
  classical
  let a : ℕ → ℝ := fun s => expList R s (fun l =>
    if (Icc 1 s).biUnion (fun t => roundRun cstep D (l.take t)) = univ then (0 : ℝ) else 1)
  have ha0 : ∀ s, 0 ≤ a s := fun s => expList_nonneg fun l => by split_ifs <;> norm_num
  have ha1 : ∀ s, a s ≤ 1 := fun s => expList_fail_le_one s _
  have hshift : ∀ s, a (s + (T₀ + 1)) ≤ (1 / 2) * a s := by
    intro s
    have happ : a (s + (T₀ + 1)) = expList R s fun l₁ => expList R (T₀ + 1) fun l₂ =>
        if (Icc 1 (s + (T₀ + 1))).biUnion (fun t => roundRun cstep D ((l₁ ++ l₂).take t)) = univ
          then (0 : ℝ) else 1 := expList_append _ _ _
    rw [happ, show (1 / 2) * a s = expList R s (fun l₁ => (1 / 2) *
      if (Icc 1 s).biUnion (fun t => roundRun cstep D (l₁.take t)) = univ
        then (0 : ℝ) else 1) from (expList_const_mul _ _ _).symm]
    refine expList_le_of_length fun l₁ hl₁ => ?_
    by_cases hA : (Icc 1 s).biUnion (fun t => roundRun cstep D (l₁.take t)) = univ
    · rw [if_pos hA, mul_zero]
      have h0 : ∀ l₂ : List R, (if (Icc 1 (s + (T₀ + 1))).biUnion
          (fun t => roundRun cstep D ((l₁ ++ l₂).take t)) = univ then (0 : ℝ) else 1) = 0 := by
        intro l₂
        rw [if_pos]
        refine eq_univ_iff_forall.mpr fun x => ?_
        have hx : x ∈ (Icc 1 s).biUnion (fun t => roundRun cstep D (l₁.take t)) := by
          rw [hA]; exact mem_univ x
        obtain ⟨t, ht, hxt⟩ := mem_biUnion.mp hx
        obtain ⟨ht1, ht2⟩ := mem_Icc.mp ht
        refine mem_biUnion.mpr ⟨t, mem_Icc.mpr ⟨ht1, by omega⟩, ?_⟩
        rwa [List.take_append_of_le_length (by omega)]
      simp_rw [h0]
      rw [expList_const]
    · rw [if_neg hA, mul_one]
      refine le_trans (expList_le_expList fun l₂ => ?_)
        ((cover_fail_le cstep bstep hdual hne hfail
          (roundRun_nonempty cstep hne hD l₁)).trans hhalf)
      by_cases hU : (Icc 1 (T₀ + 1)).biUnion
          (fun t => roundRun cstep (roundRun cstep D l₁) (l₂.take t)) = univ
      · rw [if_pos hU, if_pos]
        refine eq_univ_iff_forall.mpr fun x => ?_
        have hx : x ∈ (Icc 1 (T₀ + 1)).biUnion
            (fun t => roundRun cstep (roundRun cstep D l₁) (l₂.take t)) := by
          rw [hU]; exact mem_univ x
        obtain ⟨t, ht, hxt⟩ := mem_biUnion.mp hx
        obtain ⟨ht1, ht2⟩ := mem_Icc.mp ht
        refine mem_biUnion.mpr ⟨s + t, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        rw [← hl₁, List.take_append_length_add, roundRun_append]
        exact hxt
      · rw [if_neg hU]
        split_ifs <;> norm_num
  have hsum := sum_range_shift_le (Nat.succ_pos T₀) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1) ha0 ha1 hshift H
  refine hsum.trans_eq ?_
  push_cast
  ring

omit [DecidableEq V] [Fintype R] [Nonempty R] in
/-- `c > 0` and `log n/c³ ≥ 1/2` under the gap hypothesis `c ≥ 128 √(log n/n)`, `c ≤ 1`,
`n ≥ 2`. -/
lemma gap_pos_and_half {c : ℝ} (hc1 : c ≤ 1) (hn2 : 2 ≤ Fintype.card V)
    (hgap : 128 * √(log (Fintype.card V) / Fintype.card V) ≤ c) :
    0 < c ∧ (1 / 2 : ℝ) ≤ log (Fintype.card V) / c ^ 3 := by
  have hlog0 : 0 < log (Fintype.card V : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Fintype.card V by omega))
  have hc0 : 0 < c := by
    have hroot : 0 < √(log (Fintype.card V : ℝ) / Fintype.card V) :=
      sqrt_pos.mpr (div_pos hlog0 (by exact_mod_cast (show 0 < Fintype.card V by omega)))
    linarith [mul_pos (by norm_num : (0 : ℝ) < 128) hroot]
  refine ⟨hc0, ?_⟩
  have hLge : log (Fintype.card V : ℝ) ≤ log (Fintype.card V) / c ^ 3 := by
    rw [le_div_iff₀ (pow_pos hc0 3)]
    have hpow : c ^ 3 ≤ 1 := pow_le_one₀ hc0.le hc1
    nlinarith
  have hlog2 : log 2 ≤ log (Fintype.card V : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast hn2)
  linarith [log_two_gt_d9]

/-- **Cover time** (generic form of Theorems 1 and 3, probability bound): if every `bstep w` is a
growth process with rate `c ≥ 128 √(log n/n)`, then for `T ≥ 60002 log n/c³` COBRA from a
nonempty `D` has `⋃_{t=1}^T C_t ≠ V` with probability at most `3/n²`. -/
theorem cover_fail_le_log
    (hdual : ∀ (w : V) (C : Finset V) (t : ℕ),
      expList R t (fun l => if ∀ s ≤ t, w ∉ roundRun cstep C (l.take s) then (1 : ℝ) else 0) =
        expList R t (fun l => if C ∩ roundRun (bstep w) {w} l = ∅ then (1 : ℝ) else 0))
    (hne : ∀ D ρ, D.Nonempty → (cstep D ρ).Nonempty) {c : ℝ}
    (hP : ∀ w, GrowthProcess (bstep w) w c) (hc1 : c ≤ 1) (hn2 : 2 ≤ Fintype.card V)
    (hgap : 128 * √(log (Fintype.card V) / Fintype.card V) ≤ c) {D : Finset V}
    (hD : D.Nonempty) {T : ℕ} (hT : 60002 * log (Fintype.card V) / c ^ 3 ≤ T) :
    expList R T (fun l =>
        if (Icc 1 T).biUnion (fun s => roundRun cstep D (l.take s)) = univ then (0 : ℝ) else 1) ≤
      3 / (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨hc0, hL⟩ := gap_pos_and_half hc1 hn2 hgap
  have hsplit : 60002 * log (Fintype.card V : ℝ) / c ^ 3 =
      60000 * log (Fintype.card V : ℝ) / c ^ 3 + 2 * (log (Fintype.card V) / c ^ 3) := by ring
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) ≤ T := by
      have : 0 ≤ 60000 * log (Fintype.card V : ℝ) / c ^ 3 := by
        have : 0 ≤ log (Fintype.card V : ℝ) := log_natCast_nonneg _
        positivity
      linarith
    exact_mod_cast this
  have hT' : 60000 * log (Fintype.card V : ℝ) / c ^ 3 ≤ ((T - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hT1, Nat.cast_one]
    linarith
  have hfail := fun w => (hP w).fail_le hc1 hn2 hgap hT'
  have h := cover_fail_le cstep bstep hdual hne hfail hD
  rw [Nat.sub_add_cancel hT1] at h
  refine h.trans_eq ?_
  have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  field_simp

/-- **Cover time in expectation** (generic form of Theorems 1 and 3, equation (1)): under the
hypotheses of `cover_fail_le_log`, every partial tail sum `∑_{s < H} P(⋃_{t=1}^s C_t ≠ V)` is at
most `130000 log n/c³`. -/
theorem cover_tail_sum_le_log
    (hdual : ∀ (w : V) (C : Finset V) (t : ℕ),
      expList R t (fun l => if ∀ s ≤ t, w ∉ roundRun cstep C (l.take s) then (1 : ℝ) else 0) =
        expList R t (fun l => if C ∩ roundRun (bstep w) {w} l = ∅ then (1 : ℝ) else 0))
    (hne : ∀ D ρ, D.Nonempty → (cstep D ρ).Nonempty) {c : ℝ}
    (hP : ∀ w, GrowthProcess (bstep w) w c) (hc1 : c ≤ 1) (hn2 : 2 ≤ Fintype.card V)
    (hgap : 128 * √(log (Fintype.card V) / Fintype.card V) ≤ c) {D : Finset V}
    (hD : D.Nonempty) (H : ℕ) :
    ∑ s ∈ range H, expList R s (fun l =>
        if (Icc 1 s).biUnion (fun t => roundRun cstep D (l.take t)) = univ then (0 : ℝ) else 1) ≤
      130000 * log (Fintype.card V) / c ^ 3 := by
  obtain ⟨hc0, hL⟩ := gap_pos_and_half hc1 hn2 hgap
  have hbig := GrowthProcess.card_ge_of_gap hc1 hn2 hgap
  set n := Fintype.card V with hn_def
  set L := log (n : ℝ) / c ^ 3 with hL_def
  let T₀ := Nat.ceil (60000 * L)
  have hT₀ : 60000 * log (n : ℝ) / c ^ 3 ≤ T₀ := by
    rw [show 60000 * log (n : ℝ) / c ^ 3 = 60000 * L by rw [hL_def]; ring]
    exact Nat.le_ceil _
  have hfail := fun w => (hP w).fail_le hc1 hn2 hgap hT₀
  have hhalf : (n : ℝ) * (3 / (n : ℝ) ^ 3) ≤ 1 / 2 := by
    have hn : (16385 : ℝ) ≤ n := by exact_mod_cast hbig
    have hn0 : (0 : ℝ) < n := by linarith
    rw [show (n : ℝ) * (3 / (n : ℝ) ^ 3) = 3 / (n : ℝ) ^ 2 by field_simp,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hceil : (T₀ : ℝ) < 60000 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  refine (cover_tail_sum_le cstep bstep hdual hne hfail hhalf hD H).trans ?_
  rw [show 130000 * log (n : ℝ) / c ^ 3 = 130000 * L by rw [hL_def]; ring]
  linarith

end Epidemics
