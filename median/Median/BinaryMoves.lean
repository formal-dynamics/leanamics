import Median.BinaryAux
import Dynamics.Phases

/-! # The binary median dynamics: the phase moves

The ingredients for the consensus theorem (assembled in `Median/BinaryAssembly.lean`):
the numerics for `log n ≥ 128`, the kernel plumbing (probabilities,
absorbing-event monotonicity, the `expList` conversion) and the three
one-round phase moves, each with failure probability at most `n⁻²`
(or `n^{-1/2}` for the final Markov move):

* **Growth** `growthSet G`: the minority is below `n/4`, or the gap is at least
  `G`. One round multiplies the gap by `5/4` except with probability `n⁻²`
  (`growth_move`), as long as `16384 n log n ≤ G²`.
* **Saturation** `satSet t = {m < t}`: from `{m < t}`, `t ≤ n/4`, one round
  lands in `{m < max ((7/8)t, β)}` with `β = 512 log n` except with
  probability `n⁻²` (`sat_move`, Bernstein).
* **Consensus** `consSet`: from `{m < β}`, one round reaches consensus except
  with probability `n^{-1/2}` (`mono_move`, Markov: `𝔼[m'] ≤ 3β²/n ≤ n^{-1/2}`).

`sat_move` goes through opaque abbreviations for the sums `∑ v, avg (fcoord x v)`,
which keeps every tactic within the default elaboration budget. The generic probability
facts (monotonicity of `prob`, the one-round bound `1 - 𝔼[bad]`, absorbing events, the
`log n` conversions) come from `Dynamics.Tail`.
-/

namespace Median

open Finset Real Dynamics

/-! ### Scalar numerics -/

/-- `log n ≥ 128` already forces `n ≥ 2`. -/
lemma two_le_of_log {n : ℕ} (hL : (128 : ℝ) ≤ log n) : 2 ≤ n := by
  have h : 0 < log n := lt_of_lt_of_le (by norm_num) hL
  have h1 := one_le_of_log_pos h
  rcases n with _ | _ | n
  · simp at h
  · norm_num at hL
  · omega

/-! ### The regime `log n ≥ 128` -/

/-- With `log n ≥ 128`, `n` is at least `2²⁰ log n`. -/
lemma big_log_le {n : ℕ} (hL : (128 : ℝ) ≤ log n) : 2 ^ 20 * log n ≤ (n : ℝ) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ log n := hL.trans' (by norm_num)
  have h8 : (log n) ^ 8 / 40320 ≤ (n : ℝ) := by
    have h := Real.pow_div_factorial_le_exp _
      (Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)) 8
    have h8 : ((8 : ℕ).factorial : ℝ) = 40320 := by rfl
    rw [h8] at h
    rwa [exp_log hn0] at h
  have hL7 : (2 : ℝ) ^ 20 * 40320 ≤ (log n) ^ 7 := by
    have h5 : (128 : ℝ) ^ 7 ≤ (log n) ^ 7 := pow_le_pow_left₀ (by norm_num) hL 7
    have hdec : (2 : ℝ) ^ 20 * 40320 ≤ (128 : ℝ) ^ 7 := by norm_num
    linarith
  refine le_trans ?_ h8
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 40320)]
  have hgoal : (2 : ℝ) ^ 20 * log n * 40320 ≤ log n * (log n) ^ 7 := by
    calc (2 : ℝ) ^ 20 * log n * 40320 = log n * ((2 : ℝ) ^ 20 * 40320) := by ring
      _ ≤ log n * (log n) ^ 7 := mul_le_mul_of_nonneg_left hL7 hL0
  rw [show (log n) ^ 8 = log n * (log n) ^ 7 from by ring]
  exact hgoal

/-- `log (5/4) ≥ 1/5`. -/
lemma log_five_fourth_ge : 1 / 5 ≤ log ((5 : ℝ) / 4) := by
  calc (1 : ℝ) / 5 = 1 - (((5 : ℝ) / 4))⁻¹ := by norm_num
    _ ≤ log ((5 : ℝ) / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)

/-- `log (8/7) ≥ 1/8`. -/
lemma log_eight_seventh_ge : 1 / 8 ≤ log ((8 : ℝ) / 7) := by
  calc (1 : ℝ) / 8 = 1 - (((8 : ℝ) / 7))⁻¹ := by norm_num
    _ ≤ log ((8 : ℝ) / 7) := Real.one_sub_inv_le_log_of_pos (by norm_num)

/-- With `log n ≥ 128`, `3 (512 log n)² ≤ exp (log n / 2)`. -/
lemma markov_exp {n : ℕ} (hL : (128 : ℝ) ≤ log n) :
    3 * (512 * log n) ^ 2 ≤ exp (log n / 2) := by
  have hL0 : 0 ≤ log n := hL.trans' (by norm_num)
  have h := Real.pow_div_factorial_le_exp _ (show 0 ≤ log n / 2 by linarith) 12
  have h12 : ((12 : ℕ).factorial : ℝ) = 479001600 := by rfl
  rw [h12] at h
  have hL12 : (log n / 2) ^ 12 = (log n) ^ 12 / 4096 := by
    rw [div_pow]
    norm_num
  have hL10 : (3 : ℝ) * 512 * 512 * 4096 * 479001600 ≤ (log n) ^ 10 := by
    have h5 : (128 : ℝ) ^ 10 ≤ (log n) ^ 10 := pow_le_pow_left₀ (by norm_num) hL 10
    have hdec : (3 : ℝ) * 512 * 512 * 4096 * 479001600 ≤ (128 : ℝ) ^ 10 := by norm_num
    linarith
  refine le_trans ?_ h
  have hcomb : (log n) ^ 12 / 4096 / 479001600
      = (log n) ^ 12 / (4096 * 479001600) := by
    field_simp
  rw [hL12, hcomb, le_div_iff₀ (by norm_num : (0 : ℝ) < 4096 * 479001600)]
  have hsplit : (log n) ^ 12 = (log n) ^ 2 * (log n) ^ 10 := by ring
  rw [hsplit]
  have hprod : 3 * (512 * log n) ^ 2 * (4096 * 479001600)
      = (log n) ^ 2 * ((3 : ℝ) * 512 * 512 * 4096 * 479001600) := by
    ring
  rw [hprod]
  exact mul_le_mul_of_nonneg_left hL10 (pow_nonneg hL0 2)

/-- With `log n ≥ 128`, `3 (512 log n)² / n ≤ exp (-(log n / 2))`. -/
lemma markov_le {n : ℕ} (hL : (128 : ℝ) ≤ log n) :
    3 * (512 * log n) ^ 2 / (n : ℝ) ≤ exp (-(log n / 2)) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := markov_exp hL
  refine (div_le_iff₀ hn0).mpr ?_
  have hexp : exp (-(log n / 2)) * (n : ℝ) = exp (log n / 2) := by
    have h1 : exp (-(log n / 2)) * exp (log n) = exp (log n / 2) := by
      rw [← exp_add, show -(log n / 2) + log n = log n / 2 from by ring]
    have h2 : exp (log n) = (n : ℝ) := exp_log hn0
    calc exp (-(log n / 2)) * (n : ℝ)
        = exp (-(log n / 2)) * exp (log n) := by rw [h2]
      _ = exp (log n / 2) := h1
  rw [hexp]
  exact hm

/-! ### Kernel plumbing -/

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- A configuration that is not all-`true` has at least one `false` node. -/
lemma falsesR_pos {x : Config n Bool} (h : x ≠ (fun _ => true)) : 1 ≤ falsesR x := by
  by_cases hx : ones x = n
  · exfalso
    apply h
    have hfull : univ.filter (fun v => x v = true) = univ := by
      apply Finset.eq_univ_of_card
      rw [show (univ.filter (fun v => x v = true)).card = ones x from rfl, hx]
      simp
    funext v
    have hv := mem_univ v
    rw [← hfull] at hv
    exact (Finset.mem_filter.mp hv).2
  · have h3 : (1 : ℕ) ≤ n - ones x := by
      have hle := ones_le x
      omega
    rw [← cast_nat_sub x]
    exact_mod_cast h3

lemma kernel_eq : Median.kernel n Bool
    = Dynamics.Kernel.ofStep (Median.step (n := n) (α := Bool)) := rfl

/-- Consensus: every node holds `true`. -/
def consSet : Set (Config n Bool) := {x | x = (fun _ => true)}

omit [NeZero n] in
lemma mem_consSet {y : Config n Bool} : y ∈ consSet ↔ y = (fun _ => true) := Iff.rfl

omit [NeZero n] in
/-- Consensus is absorbing: one more round keeps every node at `true`. -/
lemma step_cons {y : Config n Bool} (hy : y = (fun _ => true)) (r : Round n) :
    step y r = (fun _ => true) := by
  funext v
  simp only [step, hy]
  simp [med3]

/-- From consensus, one round stays in consensus with probability one. -/
lemma cons_absorb {y : Config n Bool} (hy : y ∈ consSet) :
    (Median.kernel n Bool y).prob (· ∈ consSet) = 1 := by
  classical
  rw [kernel_eq, Dynamics.Kernel.prob_ofStep]
  have hfun : (fun r : Round n =>
      if step y r ∈ consSet then (1 : ℝ) else 0) = fun _ : Round n => (1 : ℝ) := by
    funext r
    exact if_pos (mem_consSet.mpr (step_cons (mem_consSet.mp hy) r))
  rw [hfun, avg_const]

/-- Kernel occupation probabilities of the all-`true` event are expectations
over lists of rounds. -/
lemma kernel_event_true (T : ℕ) (x : Config n Bool) :
    (Median.kernel n Bool).event (fun y => y = (fun _ => true)) T x
      = expList (Round n) T (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  classical
  rw [kernel_eq, Dynamics.Kernel.event_ofStep]
  congr 1
  funext l
  rw [show l.foldl Median.step x = run x l from rfl]
  by_cases h : run x l = (fun _ => true) <;> simp [h]

/-! ### Phase sets -/

/-- The growth phase: either the minority is below `n/4`, or the gap is at
least `G`. -/
def growthSet (n : ℕ) (G : ℝ) : Set (Config n Bool) :=
  {x | falsesR x < (n : ℝ) / 4 ∨ G ≤ gapR x}

/-- The saturation phase: the minority is below `t`. -/
def satSet (n : ℕ) (t : ℝ) : Set (Config n Bool) := {x | falsesR x < t}

lemma mem_growthSet {n : ℕ} {G : ℝ} {y : Config n Bool} :
    y ∈ growthSet n G ↔ falsesR y < (n : ℝ) / 4 ∨ G ≤ gapR y := Iff.rfl

lemma mem_satSet {n : ℕ} {t : ℝ} {y : Config n Bool} :
    y ∈ satSet n t ↔ falsesR y < t := Iff.rfl

omit [NeZero n] in
/-- The gap is twice the number of `true` nodes minus `n`. -/
lemma gapR_two (y : Config n Bool) : gapR y = 2 * (ones y : ℝ) - (n : ℝ) := by
  have h1 := falses_plus_ones y
  have h2 := gapR_eq y
  linarith

/-- A larger threshold shrinks the growth phase. -/
lemma growthSet_sub (n : ℕ) {G G' : ℝ} (h : G ≤ G') : growthSet n G' ⊆ growthSet n G := by
  intro y hy
  rcases mem_growthSet.mp hy with hm | hg
  · exact mem_growthSet.mpr (Or.inl hm)
  · exact mem_growthSet.mpr (Or.inr (le_trans h hg))

/-- A larger threshold grows the saturation phase. -/
lemma satSet_sub (n : ℕ) {t t' : ℝ} (h : t ≤ t') : satSet n t ⊆ satSet n t' :=
  fun _ hy => lt_of_lt_of_le (mem_satSet.mp hy) h

/-- Once the gap threshold `G` exceeds `n`, the growth phase forces the
minority below `n/4`. -/
lemma growthSet_sub_satSet (n : ℕ) {G : ℝ} (hG : (n : ℝ) < G) :
    growthSet n G ⊆ satSet n ((n : ℝ) / 4) := by
  intro y hy
  rcases mem_growthSet.mp hy with hm | hg
  · exact mem_satSet.mpr hm
  · exfalso
    have hle := gapR_le y
    have hle' : gapR y ≤ (n : ℝ) := by exact_mod_cast hle
    exact absurd (le_trans hg hle') (not_le.mpr hG)

/-- If `2 log n ≤ c` then `exp (-c) ≤ 1/n²`. -/
lemma exp_le_inv_sq {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 2 * log n ≤ c) :
    exp (-c) ≤ 1 / (n : ℝ) ^ 2 := by
  calc exp (-c) ≤ exp (-(2 * log n)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn

/-- With `log n ≥ 128`, the per-round failure `1/n²` is below the per-phase
failure `exp (-(log n)/2)`. -/
lemma inv_sq_le_exp {n : ℕ} (hL : (128 : ℝ) ≤ log n) :
    1 / (n : ℝ) ^ 2 ≤ exp (-(log n / 2)) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have h1 : exp (-(2 * log n)) = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn
  have hL0 : 0 ≤ log n := hL.trans' (by norm_num)
  have h2 : exp (-(2 * log n)) ≤ exp (-(log n / 2)) := Real.exp_le_exp.mpr (by linarith)
  rw [← h1]
  exact h2

/-- The fourth power of the per-phase failure is `1/n²`. -/
lemma exp_half_pow_four {n : ℕ} (hn : 1 ≤ n) :
    (exp (-(log n / 2))) ^ 4 = 1 / (n : ℝ) ^ 2 := by
  have e1 : (exp (-(log n / 2))) ^ 2 = exp (-(log n)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have e2 : (exp (-(log n / 2))) ^ 4 = (exp (-(log n))) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e1]
  rw [e2, pow_two, ← Real.exp_add,
    show -(log n) + -(log n) = -(2 * log n) from by ring]
  exact exp_neg_two_log hn

/-! ### One-round phase transitions -/

/-- If the denominator of Bernstein's exponent is at most `D` and `c D ≤ λ²`,
then the bound is at most `exp (-c)`. -/
lemma bernstein_exp_le {lam σ2 D c : ℝ} (hσ0 : 0 < σ2) (hlam : 0 ≤ lam)
    (hD : 0 < D) (hden : 2 * σ2 * (1 + lam / (3 * σ2)) ≤ D)
    (hcD : c * D ≤ lam ^ 2) :
    exp (-(lam ^ 2 / (2 * σ2 * (1 + lam / (3 * σ2))))) ≤ exp (-c) := by
  have hden0 : 0 < 2 * σ2 * (1 + lam / (3 * σ2)) := by
    have h1 : (0 : ℝ) ≤ lam / (3 * σ2) := div_nonneg hlam (by positivity)
    positivity
  refine Real.exp_le_exp.mpr ?_
  have h1 : c ≤ lam ^ 2 / D := (le_div_iff₀ hD).mpr hcD
  have h2 : lam ^ 2 / D ≤ lam ^ 2 / (2 * σ2 * (1 + lam / (3 * σ2))) := by
    refine le_div_iff₀ hden0 |>.mpr ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    exact mul_le_mul_of_nonneg_left hden (pow_nonneg hlam 2)
  linarith

/-- One round keeps the minority below `n/4` except with probability `1/n²`
(Hoeffding's upper tail for the number of `false` nodes). -/
lemma growth_move_small (hL : (128 : ℝ) ≤ log n) {x : Config n Bool}
    (hx : falsesR x < (n : ℝ) / 4) :
    1 - 1 / (n : ℝ) ^ 2
      ≤ (Median.kernel n Bool x).prob (· ∈ satSet n ((n : ℝ) / 4)) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : ∑ v, avg (fcoord x v) ≤ 5 / 8 * falsesR x :=
    expfalses_le_five_eighth x (le_of_lt hx)
  have hlam : 0 ≤ (n : ℝ) / 4 - ∑ v, avg (fcoord x v) := by
    have h58 : 5 / 8 * falsesR x ≤ 5 / 8 * ((n : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (le_of_lt hx) (by norm_num)
    linarith
  have hlam3 : 3 * (n : ℝ) / 32 ≤ (n : ℝ) / 4 - ∑ v, avg (fcoord x v) := by
    have h58 : 5 / 8 * falsesR x ≤ 5 / 8 * ((n : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (le_of_lt hx) (by norm_num)
    linarith
  have hbad : avg (fun r : Round n =>
      if ∑ v, avg (fcoord x v) + ((n : ℝ) / 4 - ∑ v, avg (fcoord x v))
          ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ exp (-(2 * ((n : ℝ) / 4 - ∑ v, avg (fcoord x v)) ^ 2 / n)) := falses_tail_upper x hlam
  have hkey : 2 * log n
      ≤ 2 * ((n : ℝ) / 4 - ∑ v, avg (fcoord x v)) ^ 2 / n := by
    rw [le_div_iff₀ hn0]
    have hsq : 3 * (n : ℝ) / 32 * (3 * (n : ℝ) / 32)
        ≤ ((n : ℝ) / 4 - ∑ v, avg (fcoord x v))
          * ((n : ℝ) / 4 - ∑ v, avg (fcoord x v)) :=
      mul_self_le_mul_self (by linarith) hlam3
    have hn1024 : 1024 * log n ≤ (n : ℝ) := by
      have hbig := big_log_le hL
      refine le_trans (mul_le_mul_of_nonneg_right (by norm_num)
        (hL.trans' (by norm_num))) hbig
    have h9 : 1024 * log n ≤ 9 * (n : ℝ) := by linarith
    nlinarith [hsq, h9, hn0]
  have h0 : ∀ r : Round n, 0 ≤ (if ∑ v, avg (fcoord x v)
      + ((n : ℝ) / 4 - ∑ v, avg (fcoord x v))
      ≤ falsesR (step x r) then (1 : ℝ) else 0) := fun r => by split <;> norm_num
  have h1 : ∀ r : Round n, step x r ∉ satSet n ((n : ℝ) / 4) →
      1 ≤ (if ∑ v, avg (fcoord x v)
        + ((n : ℝ) / 4 - ∑ v, avg (fcoord x v))
        ≤ falsesR (step x r) then (1 : ℝ) else 0) := by
    intro r hr
    have hr' : ¬ (falsesR (step x r) < (n : ℝ) / 4) := hr
    have hadd : ∑ v, avg (fcoord x v)
        + ((n : ℝ) / 4 - ∑ v, avg (fcoord x v)) = (n : ℝ) / 4 := by ring
    rw [hadd, if_pos (le_of_not_gt hr')]
  have hstep : 1 - avg (fun r : Round n =>
      if ∑ v, avg (fcoord x v) + ((n : ℝ) / 4 - ∑ v, avg (fcoord x v))
          ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ (Median.kernel n Bool x).prob (· ∈ satSet n ((n : ℝ) / 4)) :=
    Kernel.one_sub_avg_le_prob_ofStep step _ x _ h0 h1
  have hfin := exp_le_inv_sq hn hkey
  linarith

/-- One round multiplies the gap by `5/4` except with probability `1/n²`
(Hoeffding's lower tail for the number of `true` nodes). -/
lemma growth_move_big (hL : (128 : ℝ) ≤ log n) {G : ℝ} (hG0 : 0 ≤ G)
    (hG2 : 16384 * (n : ℝ) * log n ≤ G ^ 2) {x : Config n Bool}
    (hm4 : (n : ℝ) / 4 ≤ falsesR x) (hg : G ≤ gapR x) :
    1 - 1 / (n : ℝ) ^ 2
      ≤ (Median.kernel n Bool x).prob (· ∈ growthSet n ((5 / 4) * G)) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ log n := hL.trans' (by norm_num)
  have hnL : 0 ≤ (n : ℝ) * log n := mul_nonneg (by positivity) hL0
  have hgp : gapR x = (n : ℝ) - 2 * falsesR x := by
    have h1 := falses_plus_ones x
    have h2 := gapR_eq x
    linarith
  have hg0 : 0 ≤ gapR x := le_trans hG0 hg
  have hgle : gapR x ≤ (n : ℝ) / 2 := by linarith
  have hE : (n : ℝ) / 2 + 11 / 16 * gapR x ≤ ∑ v, avg (coord x v) := expones_ge x hg0 hgle
  have hlam : 0 ≤ G / 16 := by positivity
  have hbad : avg (fun r : Round n =>
      if (ones (step x r) : ℝ) + G / 16 ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0)
      ≤ exp (-(2 * (G / 16) ^ 2 / n)) := ones_tail_lower x hlam
  have hkey : 2 * log n ≤ 2 * (G / 16) ^ 2 / n := by
    rw [le_div_iff₀ hn0]
    have h2 : 2 * (G / 16) ^ 2 = G ^ 2 / 128 := by
      field_simp
      ring
    rw [h2, le_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
    have hring : 2 * log n * (n : ℝ) * 128 = 256 * (n : ℝ) * log n := by ring
    rw [hring]
    linarith
  have h0 : ∀ r : Round n, 0 ≤
      (if (ones (step x r) : ℝ) + G / 16 ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0) :=
    fun r => by split <;> norm_num
  have h1 : ∀ r : Round n, step x r ∉ growthSet n ((5 / 4) * G) →
      1 ≤ (if (ones (step x r) : ℝ) + G / 16
        ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0) := by
    intro r hr
    have hr' : ¬ (falsesR (step x r) < (n : ℝ) / 4 ∨ (5 / 4) * G
        ≤ gapR (step x r)) := hr
    push Not at hr'
    have hones' : (ones (step x r) : ℝ) = ((n : ℝ) + gapR (step x r)) / 2 := by
      have h1 := falses_plus_ones (step x r)
      have h2 := gapR_eq (step x r)
      linarith
    have hgG : 11 / 16 * G ≤ 11 / 16 * gapR x := mul_le_mul_of_nonneg_left hg (by norm_num)
    have hE' : (n : ℝ) / 2 + 11 / 16 * G ≤ ∑ v, avg (coord x v) := by
      linarith
    have hlt : (ones (step x r) : ℝ) + G / 16 < ∑ v, avg (coord x v) := by
      have hgaplt : gapR (step x r) < (5 / 4) * G := hr'.2
      have honeslt : (ones (step x r) : ℝ) < (n : ℝ) / 2 + 5 / 8 * G := by linarith
      linarith
    rw [if_pos (le_of_lt hlt)]
  have hstep : 1 - avg (fun r : Round n =>
      if (ones (step x r) : ℝ) + G / 16 ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0)
      ≤ (Median.kernel n Bool x).prob (· ∈ growthSet n ((5 / 4) * G)) :=
    Kernel.one_sub_avg_le_prob_ofStep step _ x _ h0 h1
  have hfin := exp_le_inv_sq hn hkey
  linarith

/-- One round of the growth phase. -/
lemma growth_move (hL : (128 : ℝ) ≤ log n) {G : ℝ} (hG0 : 0 ≤ G)
    (hG2 : 16384 * (n : ℝ) * log n ≤ G ^ 2) {x : Config n Bool}
    (hx : x ∈ growthSet n G) :
    1 - 1 / (n : ℝ) ^ 2
      ≤ (Median.kernel n Bool x).prob (· ∈ growthSet n ((5 / 4) * G)) := by
  have hsmall : falsesR x < (n : ℝ) / 4 → 1 - 1 / (n : ℝ) ^ 2
      ≤ (Median.kernel n Bool x).prob (· ∈ satSet n ((n : ℝ) / 4)) :=
    growth_move_small hL
  have hsub : satSet n ((n : ℝ) / 4) ⊆ growthSet n ((5 / 4) * G) :=
    fun y hy => mem_growthSet.mpr (Or.inl (mem_satSet.mp hy))
  rcases mem_growthSet.mp hx with hm | hg
  · exact le_trans (growth_move_small hL hm) (Distribution.prob_mono _ hsub)
  · by_cases hm4 : (n : ℝ) / 4 ≤ falsesR x
    · exact growth_move_big hL hG0 hG2 hm4 hg
    · push Not at hm4
      exact le_trans (growth_move_small hL hm4) (Distribution.prob_mono _ hsub)

/-- One round of the saturation phase: from a minority below `t ≤ n/4` the
minority drops below `max ((7/8) t) β` except with probability `1/n²`, where
`β = 512 log n` (Bernstein's inequality). -/
lemma sat_move (hL : (128 : ℝ) ≤ log n) {t : ℝ} (_ht0 : 0 ≤ t) (htn : t ≤ (n : ℝ) / 4)
    {x : Config n Bool} (hx : falsesR x < t) :
    1 - 1 / (n : ℝ) ^ 2
      ≤ (Median.kernel n Bool x).prob
        (· ∈ satSet n (max ((7 / 8) * t) (512 * log n))) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hL0 : 0 ≤ log n := hL.trans' (by norm_num)
  have hβ12 : 12 ≤ 512 * log n := by linarith
  have hβn : 512 * log n ≤ (n : ℝ) / 4 := by
    have h2048 : (2048 : ℝ) * log n ≤ (n : ℝ) := by
      have hbig := big_log_le hL
      refine le_trans (mul_le_mul_of_nonneg_right (by norm_num) hL0) hbig
    linarith
  have hxn4 : falsesR x ≤ (n : ℝ) / 4 := le_of_lt (lt_of_lt_of_le hx htn)
  have hE : ∑ v, avg (fcoord x v) ≤ 3 / 4 * falsesR x := expfalses_le_three_fourth x hxn4
  have hE0 : 0 ≤ ∑ v, avg (fcoord x v) :=
    Finset.sum_nonneg fun v _ => avg_nonneg fun p => fcoord_nonneg x v p
  -- abbreviations: the variance proxy and the Bernstein excess
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ∑ v, avg (fcoord x v) + 1 := ⟨_, rfl⟩
  have hσ0 : 0 < s := by rw [hsdef]; linarith
  have hvar : ∑ v, variance (fcoord x v) ≤ s := by
    rw [hsdef]
    have h1 : ∑ v, variance (fcoord x v) ≤ ∑ v, avg (fcoord x v) :=
      Finset.sum_le_sum fun v _ => variance_le_avg_of_zero_one (fcoord_zero_one x v)
    linarith
  have hden_eq : ∀ d : ℝ, 0 ≤ d → 2 * s * (1 + d / (3 * s)) = 2 * s + 2 * d / 3 := by
    intro d _hd0
    have hsnz : s ≠ 0 := by
      rw [hsdef]
      linarith
    field_simp
  by_cases hmβ : 512 * log n ≤ falsesR x
  · -- shrink: `β ≤ m`; the expected minority is at most `(7/8) m`
    obtain ⟨d, hddef⟩ : ∃ d : ℝ,
        d = (7 / 8) * falsesR x - ∑ v, avg (fcoord x v) := ⟨_, rfl⟩
    have hd0 : 0 ≤ d := by
      rw [hddef]
      have h34 : (3 / 4 : ℝ) * falsesR x = 6 / 8 * falsesR x := by ring
      linarith
    have hdle : d ≤ falsesR x := by
      rw [hddef]
      have hm0 : 0 ≤ falsesR x := falsesR_nonneg x
      have hm78 : (7 / 8) * falsesR x ≤ falsesR x := by nlinarith
      linarith
    have hs_le : s ≤ 3 / 4 * falsesR x + 1 := by rw [hsdef]; linarith
    have hterm : 2 * s + 2 * d / 3 ≤ 3 * falsesR x := by
      linarith [hs_le, hdle, hmβ, hβ12]
    have hD : 0 < 3 * falsesR x := by linarith [hβ12, hmβ]
    have hbad := falses_tail_bernstein x hd0 hσ0 hvar
    have hden : 2 * s * (1 + d / (3 * s)) ≤ 3 * falsesR x := by
      rw [hden_eq d hd0]
      exact hterm
    have hle8 : falsesR x / 8 ≤ d := by
      rw [hddef]
      have h34 : (3 / 4 : ℝ) * falsesR x = 6 / 8 * falsesR x := by ring
      linarith
    have hcD : (2 * log n) * (3 * falsesR x) ≤ d ^ 2 := by
      have h384 : 384 * log n ≤ falsesR x := by nlinarith [hL0, hmβ]
      have h1 : 384 * log n * falsesR x ≤ falsesR x * falsesR x :=
        mul_le_mul_of_nonneg_right h384 (falsesR_nonneg x)
      have h2 : falsesR x * falsesR x ≤ 64 * d * d := by
        have hsq : falsesR x / 8 * (falsesR x / 8) ≤ d * d :=
          mul_self_le_mul_self (div_nonneg (falsesR_nonneg x) (by norm_num)) hle8
        have hrf : falsesR x / 8 * (falsesR x / 8) = falsesR x * falsesR x / 64 := by
          field_simp
          ring
        rw [hrf] at hsq
        nlinarith [hsq]
      nlinarith [h1, h2]
    have h0 : ∀ r : Round n, 0 ≤
        (if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0) :=
      fun r => by split <;> norm_num
    have h1 : ∀ r : Round n, step x r ∉ satSet n (max ((7 / 8) * t) (512 * log n)) →
        1 ≤ (if ∑ v, avg (fcoord x v) + d
          ≤ falsesR (step x r) then (1 : ℝ) else 0) := by
      intro r hr
      have hr' : ¬ (falsesR (step x r) < max ((7 / 8) * t) (512 * log n)) := hr
      have hadd : ∑ v, avg (fcoord x v)
          + d = (7 / 8) * falsesR x := by rw [hddef]; ring
      have h78 : (7 / 8) * falsesR x < (7 / 8) * t :=
        mul_lt_mul_of_pos_left hx (by norm_num)
      have hcond : (7 / 8) * falsesR x ≤ falsesR (step x r) :=
        le_trans (le_of_lt (lt_of_lt_of_le h78 (le_max_left _ _))) (le_of_not_gt hr')
      rw [hadd, if_pos hcond]
    have hstep : 1 - avg (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0)
        ≤ (Median.kernel n Bool x).prob
          (· ∈ satSet n (max ((7 / 8) * t) (512 * log n))) :=
      Kernel.one_sub_avg_le_prob_ofStep step _ x _ h0 h1
    have hexp := bernstein_exp_le hσ0 hd0 hD hden hcD
    have hfin : exp (-(2 * log n)) = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn
    linarith
  · -- small: `m < β`; keep the minority below `β`
    have hmb : falsesR x < 512 * log n := not_le.mp hmβ
    have hmb' : falsesR x ≤ 512 * log n := le_of_lt hmb
    obtain ⟨d, hddef⟩ : ∃ d : ℝ,
        d = 512 * log n - ∑ v, avg (fcoord x v) := ⟨_, rfl⟩
    have hEβ : ∑ v, avg (fcoord x v) ≤ 3 / 4 * (512 * log n) := by
      have h1 : 3 / 4 * falsesR x ≤ 3 / 4 * (512 * log n) :=
        mul_le_mul_of_nonneg_left hmb' (by norm_num)
      linarith
    have h34 : (3 / 4 : ℝ) * (512 * log n) ≤ 512 * log n := by linarith
    have hd0 : 0 ≤ d := by rw [hddef]; linarith
    have hdle : d ≤ 512 * log n := by rw [hddef]; linarith
    have hs_le : s ≤ 3 / 4 * (512 * log n) + 1 := by rw [hsdef]; linarith
    have hterm : 2 * s + 2 * d / 3 ≤ 3 * (512 * log n) := by
      linarith [hs_le, hdle, hβ12]
    have hD : 0 < 3 * (512 * log n) := by linarith [hβ12]
    have hbad := falses_tail_bernstein x hd0 hσ0 hvar
    have hden : 2 * s * (1 + d / (3 * s)) ≤ 3 * (512 * log n) := by
      rw [hden_eq d hd0]
      exact hterm
    have hle4 : 512 * log n / 4 ≤ d := by
      rw [hddef]
      linarith
    have hcD : (2 * log n) * (3 * (512 * log n)) ≤ d ^ 2 := by
      have h96 : 96 * log n ≤ 512 * log n := by linarith
      have h1 : 96 * log n * (512 * log n)
          ≤ (512 * log n) * (512 * log n) :=
        mul_le_mul_of_nonneg_right h96 (by linarith [hβ12])
      have h2 : (512 * log n) * (512 * log n)
          ≤ 16 * d * d := by
        have hsq : 512 * log n / 4 * (512 * log n / 4) ≤ d * d :=
          mul_self_le_mul_self
            (div_nonneg (by linarith [hβ12] : (0 : ℝ) ≤ 512 * log n) (by norm_num)) hle4
        have hrf : 512 * log n / 4 * (512 * log n / 4)
            = (512 * log n) * (512 * log n) / 16 := by
          field_simp
          ring
        rw [hrf] at hsq
        nlinarith [hsq]
      nlinarith [h1, h2]
    have h0 : ∀ r : Round n, 0 ≤
        (if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0) :=
      fun r => by split <;> norm_num
    have h1 : ∀ r : Round n, step x r ∉ satSet n (max ((7 / 8) * t) (512 * log n)) →
        1 ≤ (if ∑ v, avg (fcoord x v) + d
          ≤ falsesR (step x r) then (1 : ℝ) else 0) := by
      intro r hr
      have hr' : ¬ (falsesR (step x r) < max ((7 / 8) * t) (512 * log n)) := hr
      have hadd : ∑ v, avg (fcoord x v)
          + d = 512 * log n := by rw [hddef]; ring
      have hcond : 512 * log n ≤ falsesR (step x r) :=
        le_trans (le_max_right _ _) (le_of_not_gt hr')
      rw [hadd, if_pos hcond]
    have hstep : 1 - avg (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + d ≤ falsesR (step x r) then (1 : ℝ) else 0)
        ≤ (Median.kernel n Bool x).prob
          (· ∈ satSet n (max ((7 / 8) * t) (512 * log n))) :=
      Kernel.one_sub_avg_le_prob_ofStep step _ x _ h0 h1
    have hexp := bernstein_exp_le hσ0 hd0 hD hden hcD
    have hfin : exp (-(2 * log n)) = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn
    linarith

/-- One round from a minority below `512 log n` reaches consensus except with
probability `exp (-(log n)/2)` (Markov's inequality). -/
lemma mono_move (hL : (128 : ℝ) ≤ log n) {x : Config n Bool}
    (hx : falsesR x < 512 * log n) :
    1 - exp (-(log n / 2)) ≤ (Median.kernel n Bool x).prob (· ∈ consSet) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : ∑ v, avg (fcoord x v) ≤ 3 * falsesR x ^ 2 / n := expfalses_le x
  have hE2 : 3 * falsesR x ^ 2 / n ≤ 3 * (512 * log n) ^ 2 / n := by
    rw [div_le_div_iff₀ hn0 hn0]
    refine mul_le_mul_of_nonneg_right ?_ hn0.le
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (falsesR_nonneg x) (le_of_lt hx) 2) (by norm_num)
  have hM := markov_le hL
  have hbad : avg (fun r : Round n => if 1 ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ ∑ v, avg (fcoord x v) := falses_tail_markov x
  have h0 : ∀ r : Round n, 0 ≤ (if 1 ≤ falsesR (step x r) then (1 : ℝ) else 0) :=
    fun r => by split <;> norm_num
  have h1 : ∀ r : Round n, step x r ∉ consSet →
      1 ≤ (if 1 ≤ falsesR (step x r) then (1 : ℝ) else 0) := by
    intro r hr
    have hr' : step x r ≠ (fun _ => true) := fun h => hr (mem_consSet.mpr h)
    have hfz : falsesR (step x r) ≠ 0 := fun h => hr' ((eq_true_iff_falsesR_zero).mpr h)
    have hone : 1 ≤ falsesR (step x r) := by
      have hc : ((n - ones (step x r) : ℕ) : ℝ) = falsesR (step x r) := cast_nat_sub _
      have hne : (n - ones (step x r) : ℕ) ≠ 0 := by
        intro h0
        apply hfz
        rw [← hc, h0]
        norm_num
      have hle := ones_le (step x r)
      have h1n : 1 ≤ n - ones (step x r) := by omega
      rw [← hc]
      exact_mod_cast h1n
    rw [if_pos hone]
  have hstep : 1 - avg (fun r : Round n =>
      if 1 ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ (Median.kernel n Bool x).prob (· ∈ consSet) :=
    Kernel.one_sub_avg_le_prob_ofStep step _ x _ h0 h1
  linarith

end Median
