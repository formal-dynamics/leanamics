import Plurality.Corollaries
import Plurality.AnyStartMoments
import Plurality.AnyStartKernel

/-!
# Two opinions from any configuration

Binary 3-Majority reaches consensus from **any** configuration, including the perfectly balanced
one, within `O(log n)` rounds with high probability (Becchetti, Clementi, Natale, *Consensus
dynamics: an overview*, SIGACT News 2020, §4 Case 3, where the argument is given for the binary
median dynamics of Doerr, Goldberg, Minder, Sauerwald, Scheideler, SPAA 2011).

The gap `s = |I| - (n - |I|)` evolves in two stages.

* **Symmetry breaking** (`majority3_symmetry_breaking`). Near balance the expected drift of the
  gap is too weak for step-by-step concentration. Instead, by the variance of one round, the gap
  jumps to order `√n` with constant probability (`jump_near_balance`), and above that it grows by
  a constant factor except with probability exponentially small in its size (`growth_far`). The
  hitting-time bound of Doerr et al. (Claim 2.9, `Dynamics.Kernel.drift_hitting_log`), applied
  to `X = ⌊|s| / (√n / 100)⌋`, then shows that `|s|` reaches `22 √(3 n log n)` within
  `O(log n)` rounds except with probability `1/n`.
* **Vanishing bias** (`majority3_vanishing_bias`). From a gap `22 √(3 n log n)`, consensus
  follows within `390 log n` rounds with probability `1 - 429 log n / n`; a negative gap is the
  same statement for the complementary set.
-/

namespace Plurality

open Finset Dynamics
open ThreeMajority (Tgt3 Y_maj Y_maj_zero_one sampleCountOf)

variable {n : ℕ}

/-- The gap `|I| - (n - |I|)` between the nodes holding opinion `1` (the set `I`) and the
others. -/
noncomputable def gap (I : Finset (Fin n)) : ℝ := (I.card : ℝ) - (n - I.card)

/-- Binary 3-Majority as a finite Markov kernel on the set of nodes holding opinion `1`. -/
noncomputable def binKernel (n : ℕ) [NeZero n] : Kernel (Finset (Fin n)) :=
  Kernel.ofStep (ThreeMajority.step (n := n))

/-! ### The gap and the complement symmetry -/

section Symmetry

lemma card_le_n (I : Finset (Fin n)) : (I.card : ℝ) ≤ n := by
  exact_mod_cast (card_le_univ I).trans_eq (Fintype.card_fin n)

lemma abs_gap_le (I : Finset (Fin n)) : |gap I| ≤ n := by
  have := card_le_n I
  have h0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  unfold gap
  rw [abs_le]
  constructor <;> linarith

lemma gap_compl (I : Finset (Fin n)) : gap Iᶜ = -gap I := by
  have h := card_le_n I
  unfold gap
  rw [card_compl, Fintype.card_fin, Nat.cast_sub (by exact_mod_cast h)]
  ring

lemma sampleCountOf_compl_add (I : Finset (Fin n)) (s : Fin n × Fin n × Fin n) :
    sampleCountOf Iᶜ s + sampleCountOf I s = 3 := by
  unfold sampleCountOf
  by_cases h1 : s.1 ∈ I <;> by_cases h2 : s.2.1 ∈ I <;> by_cases h3 : s.2.2 ∈ I <;>
    simp [h1, h2, h3]

/-- Exchanging the two opinions commutes with a round. -/
lemma step_compl (I : Finset (Fin n)) (r : Tgt3 n) :
    ThreeMajority.step Iᶜ r = (ThreeMajority.step I r)ᶜ := by
  ext v
  have h := sampleCountOf_compl_add I (r v)
  simp only [ThreeMajority.mem_step, mem_compl, ThreeMajority.sampleCount]
  omega

lemma run_compl (I : Finset (Fin n)) (l : List (Tgt3 n)) :
    ThreeMajority.run Iᶜ l = (ThreeMajority.run I l)ᶜ := by
  induction l generalizing I with
  | nil => rfl
  | cons r l ih => rw [ThreeMajority.run_cons, ThreeMajority.run_cons, step_compl, ih]

lemma run_eq_foldl (I : Finset (Fin n)) (l : List (Tgt3 n)) :
    ThreeMajority.run I l = l.foldl ThreeMajority.step I := by
  induction l generalizing I with
  | nil => rfl
  | cons r l ih => rw [ThreeMajority.run_cons, ih]; rfl

lemma prob_binKernel_compl [NeZero n] (P : Finset (Fin n) → Prop) (I : Finset (Fin n)) :
    (binKernel n Iᶜ).prob P = (binKernel n I).prob (fun J => P Jᶜ) := by
  simp only [binKernel, Kernel.prob_ofStep]
  congr 1
  funext r
  rw [step_compl]

/-- `gap (step I r) = 2 ∑ᵥ Yᵥ - n` for the independent `{0,1}` contributions `Yᵥ` of the
nodes. -/
lemma gap_step (I : Finset (Fin n)) (r : Tgt3 n) :
    gap (ThreeMajority.step I r) = 2 * ∑ v, Y_maj I v (r v) - n := by
  unfold gap
  rw [← ThreeMajority.card_step_eq_sum]
  ring

end Symmetry

/-! ### The mean of the next gap -/

section Mean

/-- The probability `p = 3x² - 2x³` that a node adopts opinion `1`, with `x = |I|/n`. -/
lemma avg_Y_maj [NeZero n] (I : Finset (Fin n)) (v : Fin n) :
    Dynamics.avg (Y_maj I v)
      = 3 * ((I.card : ℝ) / n) ^ 2 - 2 * ((I.card : ℝ) / n) ^ 3 := by
  have h := ThreeMajority.avg_Y_maj_eq I v
  rw [ThreeMajority.avg_ind_eq] at h
  rw [show Dynamics.avg (Y_maj I v) = ThreeMajority.avg (Y_maj I v) from rfl, h]
  ring

/-- The mean of the next gap is `n (2p - 1) = s (3/2 - s²/(2n²))` for the gap `s`. -/
lemma two_mul_sum_avg_sub [NeZero n] (I : Finset (Fin n)) :
    2 * ∑ v, Dynamics.avg (Y_maj I v) - n
      = gap I * (3 / 2 - (gap I / n) ^ 2 / 2) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  simp only [avg_Y_maj, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold gap
  field_simp
  ring

/-- The mean of the next gap is at most `3|s|/2` in absolute value. -/
lemma abs_mean_le [NeZero n] (I : Finset (Fin n)) :
    |2 * ∑ v, Dynamics.avg (Y_maj I v) - n| ≤ 3 / 2 * |gap I| := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [two_mul_sum_avg_sub, abs_mul]
  have hd : |gap I / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hn, div_le_one hn]; exact abs_gap_le I
  have hd2 : (gap I / n) ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (gap I / n)]
  have h0 : 0 ≤ 3 / 2 - (gap I / n) ^ 2 / 2 := by linarith
  rw [abs_of_nonneg h0]
  have : 3 / 2 - (gap I / n) ^ 2 / 2 ≤ 3 / 2 := by nlinarith [sq_nonneg (gap I / n)]
  nlinarith [abs_nonneg (gap I)]

/-- For `0 ≤ s ≤ n/2` the mean of the next gap is at least `11 s/8`. -/
lemma mean_ge [NeZero n] (I : Finset (Fin n)) (h0 : 0 ≤ gap I) (h1 : gap I ≤ n / 2) :
    11 / 8 * gap I ≤ 2 * ∑ v, Dynamics.avg (Y_maj I v) - n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [two_mul_sum_avg_sub]
  have hd0 : 0 ≤ gap I / n := div_nonneg h0 hn.le
  have hd1 : gap I / n ≤ 1 / 2 := by rw [div_le_iff₀ hn]; linarith
  have : (gap I / n) ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith

end Mean

/-- **A `√n` jump near balance** (the variance of one round). If the gap is at most `4√n/25` in
absolute value and `n ≥ 5`, then after one round it is at least `√n/5` in absolute value with
probability at least `9/64`. -/
theorem jump_near_balance [NeZero n] (hn : 5 ≤ n) (I : Finset (Fin n))
    (hI : |gap I| ≤ 4 * √(n : ℝ) / 25) :
    9 / 64 ≤ (binKernel n I).prob (fun J => √(n : ℝ) / 5 ≤ |gap J|) := by
  classical
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = √(n : ℝ) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hww : w ^ 2 = n := by rw [hw, Real.sq_sqrt hn0.le]
  rw [← hw] at hI ⊢
  -- the mean `m` of the next gap is at most `6 w / 25` in absolute value
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * ∑ v, Dynamics.avg (Y_maj I v) - n := ⟨_, rfl⟩
  have hmabs : |m| ≤ 6 * w / 25 := by
    have := abs_mean_le I
    rw [← hm] at this
    linarith
  have hm2 : m ^ 2 ≤ 36 * n / 625 := by
    have h := pow_le_pow_left₀ (abs_nonneg m) hmabs 2
    rw [sq_abs] at h
    nlinarith
  -- the variance `σ² = n p (1 - p) = (n² - m²) / (4n)` is at least `n/5`
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 3 * ((I.card : ℝ) / n) ^ 2 - 2 * ((I.card : ℝ) / n) ^ 3 :=
    ⟨_, rfl⟩
  have hsum : ∑ v, Dynamics.avg (Y_maj I v) = n * p := by
    simp only [avg_Y_maj, ← hp, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hvar : ∑ v, variance (Y_maj I v) = n * (p * (1 - p)) := by
    simp only [variance_of_zero_one (Y_maj_zero_one I _), avg_Y_maj, ← hp, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hid : 4 * n * (n * (p * (1 - p))) = n ^ 2 - m ^ 2 := by
    rw [hm, hsum]; ring
  have hσ : (n : ℝ) / 5 ≤ ∑ v, variance (Y_maj I v) := by
    rw [hvar]
    have h4n : 0 < 4 * (n : ℝ) := by positivity
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc h4n
    nlinarith
  -- Paley-Zygmund: `σ² ≤ 4 S²` with probability at least `9/64`
  have hPZ : 9 / 64 ≤ Dynamics.avg (fun r : Tgt3 n =>
      if ∑ i, variance (Y_maj I i) ≤ 4 * (∑ i, (Y_maj I i (r i) - Dynamics.avg (Y_maj I i))) ^ 2
      then (1 : ℝ) else 0) :=
    avg_pz_zero_one (Y_maj I) (fun i y => Y_maj_zero_one I i y) (by linarith)
  refine le_trans ?_ (Kernel.one_sub_avg_le_prob_ofStep ThreeMajority.step
    (fun J => w / 5 ≤ |gap J|) I (fun r => 1 -
      if ∑ i, variance (Y_maj I i) ≤ 4 * (∑ i, (Y_maj I i (r i) - Dynamics.avg (Y_maj I i))) ^ 2
      then (1 : ℝ) else 0) (fun r => by split_ifs <;> norm_num) ?_)
  · rw [Dynamics.avg_sub, Dynamics.avg_const]
    linarith
  · intro r hr
    split_ifs with hc
    · exfalso
      apply hr
      -- the next gap is `2S + m`, with `4S² ≥ σ² ≥ w²/5` and `|m| ≤ 6w/25`
      obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, (Y_maj I i (r i) - Dynamics.avg (Y_maj I i)) := ⟨_, rfl⟩
      rw [← hS] at hc
      have hg : gap (ThreeMajority.step I r) = 2 * S + m := by
        rw [gap_step, hS, hm, sum_sub_distrib]; ring
      change w / 5 ≤ |gap (ThreeMajority.step I r)|
      rw [hg]
      by_contra hlt
      push Not at hlt
      have htri : |2 * S| ≤ |2 * S + m| + |m| := by
        have := abs_add_le (2 * S + m) (-m)
        rwa [abs_neg, add_neg_cancel_right] at this
      have h2S : |2 * S| < 11 * w / 25 := by linarith
      have hsq : (2 * S) ^ 2 < (11 * w / 25) ^ 2 := by
        rw [← sq_abs]
        exact pow_lt_pow_left₀ h2S (abs_nonneg _) (by norm_num)
      nlinarith
    · norm_num

/-- **Growth above `√n`** (the drift of one round, with Hoeffding's inequality). If
`0 ≤ s ≤ n/2` for the gap `s`, then for every `λ ≥ 0` the next gap exceeds `11 s/8 - 2λ` except
with probability at most `exp (-2λ²/n)`. -/
theorem growth_far [NeZero n] (I : Finset (Fin n)) (h0 : 0 ≤ gap I) (h1 : gap I ≤ n / 2)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    1 - Real.exp (-(2 * lam ^ 2 / n))
      ≤ (binKernel n I).prob (fun J => 11 / 8 * gap I - 2 * lam < gap J) := by
  classical
  have hmean := mean_ge I h0 h1
  have hH := Dynamics.avg_hoeffding_lower (Y_maj I) (fun i y => Y_maj_zero_one I i y) hlam
  refine le_trans ?_ (Kernel.one_sub_avg_le_prob_ofStep ThreeMajority.step
    (fun J => 11 / 8 * gap I - 2 * lam < gap J) I (fun r =>
      if ∑ i, Y_maj I i (r i) + lam ≤ ∑ i, Dynamics.avg (Y_maj I i) then (1 : ℝ) else 0)
    (fun r => by split_ifs <;> norm_num) ?_)
  · have : Dynamics.avg (fun r : Tgt3 n =>
        if ∑ i, Y_maj I i (r i) + lam ≤ ∑ i, Dynamics.avg (Y_maj I i) then (1 : ℝ) else 0)
        ≤ Real.exp (-(2 * lam ^ 2 / n)) := hH
    linarith
  · intro r hr
    have hle : gap (ThreeMajority.step I r) ≤ 11 / 8 * gap I - 2 * lam := not_lt.mp hr
    rw [gap_step] at hle
    rw [if_pos (by linarith)]

/-! ### Symmetry breaking: the hypotheses of the hitting-time bound -/

/-- The absolute gap in units of `√n / 100`, rounded down: the observable `X` to which the
hitting-time bound is applied. -/
noncomputable def gapUnits (I : Finset (Fin n)) : ℕ := ⌊|gap I| / (√(n : ℝ) / 100)⌋₊

lemma gapUnits_compl (I : Finset (Fin n)) : gapUnits Iᶜ = gapUnits I := by
  simp only [gapUnits, gap_compl, abs_neg]

lemma unit_pos [NeZero n] : 0 < √(n : ℝ) / 100 := by
  have : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  positivity

lemma gapUnits_mul_le [NeZero n] (I : Finset (Fin n)) :
    (gapUnits I : ℝ) * (√(n : ℝ) / 100) ≤ |gap I| := by
  have := Nat.floor_le (div_nonneg (abs_nonneg (gap I)) (unit_pos (n := n)).le)
  rwa [le_div_iff₀ unit_pos] at this

lemma lt_gapUnits_add_one [NeZero n] (I : Finset (Fin n)) :
    |gap I| < ((gapUnits I : ℝ) + 1) * (√(n : ℝ) / 100) := by
  have := Nat.lt_floor_add_one (|gap I| / (√(n : ℝ) / 100))
  rwa [div_lt_iff₀ unit_pos] at this

lemma le_gapUnits [NeZero n] {k : ℕ} {I : Finset (Fin n)}
    (h : (k : ℝ) * (√(n : ℝ) / 100) ≤ |gap I|) : k ≤ gapUnits I :=
  Nat.le_floor (by rwa [le_div_iff₀ unit_pos])

/-- For `log n ≥ 40`: `n > 0` and `√n ≥ 20 log n + 1`, from `√n = e^{(log n)/2} ≥ (log n)⁴/384`. -/
lemma sqrt_ge_of_log (hL : 40 ≤ Real.log n) :
    (0 : ℝ) < n ∧ 20 * Real.log n + 1 ≤ √(n : ℝ) := by
  have hn : (0 : ℝ) < n := by
    by_contra h
    push Not at h
    have h0 : (n : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [h0, Real.log_zero] at hL
    linarith
  refine ⟨hn, ?_⟩
  have hw0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn
  have h := Real.pow_div_factorial_le_exp (x := Real.log n / 2) (by linarith) 4
  rw [← Real.log_sqrt hn.le, Real.exp_log hw0, Real.log_sqrt hn.le] at h
  norm_num [Nat.factorial] at h
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  rw [← hLdef] at h hL ⊢
  have hL3 : 64000 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at this
    linarith
  nlinarith

/-- Near balance (`1 ≤ X < 16`, where the gap is below `4√n/25`): with probability at least
`9/64` the next gap is at least `√n/5`, so `X` jumps to at least `20 ≥ 5X/4`. -/
lemma units_near [NeZero n] (hL : 40 ≤ Real.log n) (I : Finset (Fin n))
    (hI : gapUnits I < 16) :
    9 / 64 ≤ (binKernel n I).prob (fun J => 20 ≤ gapUnits J) := by
  obtain ⟨hn0, hw⟩ := sqrt_ge_of_log hL
  have hn5 : 5 ≤ n := by
    have h1 : (1 : ℝ) ≤ √(n : ℝ) := by linarith
    have h2 : (5 : ℝ) ≤ n := by
      have := Real.sq_sqrt hn0.le
      nlinarith
    exact_mod_cast h2
  have hhi := lt_gapUnits_add_one I
  have h16 : (gapUnits I : ℝ) + 1 ≤ 16 := by
    have : gapUnits I + 1 ≤ 16 := hI
    exact_mod_cast this
  have hw0 : 0 < √(n : ℝ) / 100 := unit_pos
  have hnear : |gap I| ≤ 4 * √(n : ℝ) / 25 := by nlinarith
  refine (jump_near_balance hn5 I hnear).trans (Distribution.prob_mono _ fun J hJ => ?_)
  exact le_gapUnits (by push_cast; linarith)

/-- Above `√n` (`16 ≤ X < 1000 log n`, gap `≥ 0`): by `growth_far` with `λ = X √n / 3200`,
`X` grows to at least `5X/4` except with probability `exp (-X²/5120000) ≤ exp (-X/320000)`. -/
lemma units_far [NeZero n] (hL : 40 ≤ Real.log n) (I : Finset (Fin n)) (hg : 0 ≤ gap I)
    (h16 : 16 ≤ gapUnits I) (hI : (gapUnits I : ℝ) < 1000 * Real.log n) :
    1 - Real.exp (-(1 / 320000 * (gapUnits I : ℝ)))
      ≤ (binKernel n I).prob (fun J => 5 / 4 * (gapUnits I : ℝ) ≤ gapUnits J) := by
  obtain ⟨hn0, hw⟩ := sqrt_ge_of_log hL
  have hlo := gapUnits_mul_le I
  have hhi := lt_gapUnits_add_one I
  obtain ⟨w, hw_def⟩ : ∃ w, w = √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = gapUnits I := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  have hww : w ^ 2 = n := by rw [hw_def, Real.sq_sqrt hn0.le]
  rw [← hw_def, ← hLdef] at hw
  rw [← hw_def, ← hX] at hlo hhi
  rw [← hX] at hI ⊢
  rw [← hLdef] at hI hL
  have hX16 : (16 : ℝ) ≤ X := by rw [hX]; exact_mod_cast h16
  have hw0 : 0 < w := by linarith
  rw [abs_of_nonneg hg] at hlo hhi
  -- `s < (X + 1) √n/100 ≤ (1000 log n + 1) √n/100 ≤ n/2`
  have hhalf : gap I ≤ n / 2 := by
    have h1 : (X + 1) * (w / 100) ≤ (1000 * L + 1) * (w / 100) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (1000 * L + 1) * (w / 100) ≤ w ^ 2 / 2 := by nlinarith
    rw [← hww]
    linarith
  have hlam : 0 ≤ X * (w / 100) / 32 := by positivity
  have hgf := growth_far I hg hhalf hlam
  have hexp : Real.exp (-(2 * (X * (w / 100) / 32) ^ 2 / n)) ≤ Real.exp (-(1 / 320000 * X)) := by
    apply Real.exp_le_exp.mpr
    rw [← hww]
    have e : 2 * (X * (w / 100) / 32) ^ 2 / w ^ 2 = X ^ 2 / 5120000 := by
      field_simp
      ring
    rw [e]
    nlinarith
  refine le_trans ?_ (hgf.trans (Distribution.prob_mono _ fun J hJ => ?_))
  · linarith
  · -- `|gap J| > 21 X/16 · √n/100`, so `X J + 1 > 21 X/16 ≥ 5X/4 + 1`
    have hJ' : 21 / 16 * X * (w / 100) < |gap J| := by
      have := le_abs_self (gap J)
      nlinarith
    have hJhi := lt_gapUnits_add_one J
    rw [← hw_def] at hJhi
    have hlt : 21 / 16 * X < (gapUnits J : ℝ) + 1 := by
      have h : (21 / 16 * X) * (w / 100) < ((gapUnits J : ℝ) + 1) * (w / 100) := by
        linarith [hJ'.trans hJhi]
      exact lt_of_mul_lt_mul_right h (by positivity)
    linarith

/-- The growth hypothesis of the hitting-time bound: below the target, `X` grows to at least
`min (5X/4) n` with probability at least `1 - exp (-X/320000)`. -/
lemma units_grow [NeZero n] (hL : 40 ≤ Real.log n) (I : Finset (Fin n))
    (hI : (gapUnits I : ℝ) < 1000 * Real.log n) :
    1 - Real.exp (-(1 / 320000 * (gapUnits I : ℝ)))
      ≤ (binKernel n I).prob (fun J => min (5 / 4 * (gapUnits I : ℝ)) n ≤ gapUnits J) := by
  refine le_trans ?_ (Distribution.prob_mono _ fun J (h : 5 / 4 * (gapUnits I : ℝ) ≤ gapUnits J) =>
    (min_le_left _ _).trans h)
  rcases Nat.lt_or_ge (gapUnits I) 1 with h0 | h1
  · rw [Nat.lt_one_iff.mp h0]
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, sub_self]
    exact Distribution.prob_nonneg _ _
  rcases Nat.lt_or_ge (gapUnits I) 16 with hs | hs
  · -- near balance
    have hX15 : (gapUnits I : ℝ) ≤ 15 := by exact_mod_cast Nat.lt_succ_iff.mp hs
    have hexp : 1 - Real.exp (-(1 / 320000 * (gapUnits I : ℝ))) ≤ 9 / 64 := by
      have := Real.add_one_le_exp (-(1 / 320000 * (gapUnits I : ℝ)))
      linarith
    refine hexp.trans ((units_near hL I hs).trans (Distribution.prob_mono _ fun J hJ => ?_))
    have : (20 : ℝ) ≤ gapUnits J := by exact_mod_cast hJ
    linarith
  · -- above `√n`: reduce to a nonnegative gap by exchanging the opinions
    rcases le_total 0 (gap I) with hg | hg
    · exact units_far hL I hg hs hI
    · have hc := units_far hL Iᶜ (by rw [gap_compl]; linarith) (by rwa [gapUnits_compl])
        (by rwa [gapUnits_compl])
      rw [prob_binKernel_compl] at hc
      simpa only [compl_compl, gapUnits_compl] using hc

/-- **Symmetry breaking.** There is `C > 0` such that, for `log n ≥ 40`, from any configuration
`I₀` the gap reaches `22 √(3 n log n)` in absolute value within any `t ≥ C log n` rounds with
probability at least `1 - 1/n`. -/
theorem majority3_symmetry_breaking : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n],
    40 ≤ Real.log n → ∀ (I₀ : Finset (Fin n)) (t : ℕ), C * Real.log n ≤ t →
      1 - 1 / (n : ℝ)
        ≤ (binKernel n).hitProb (fun I => 22 * √(3 * n * Real.log n) ≤ |gap I|) t I₀ := by
  /- The hitting-time bound of Doerr et al. (Claim 2.9) with `X = gapUnits`, `q = n`,
  `c₁ = 5/4`, `c₂ = 1/320000`, `c₃ = 9/64`, `c₄ = 1000`, `c₆ = 1`: `X` reaches `1000 log n`,
  that is `|s| ≥ 10 √n log n ≥ 22 √(3 n log n)`, within `C log n` rounds w.p. `1 - 1/n`. -/
  obtain ⟨C, hC, hdrift⟩ := Kernel.drift_hitting_log.{0} (c₁ := 5 / 4) (c₂ := 1 / 320000)
    (c₃ := 9 / 64) (c₄ := 1000) (c₆ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C, hC, fun n _ hL I₀ t ht => ?_⟩
  obtain ⟨hn0, hw⟩ := sqrt_ge_of_log hL
  have hww := Real.sq_sqrt hn0.le
  have hw0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  -- `X ≤ |s| / (√n/100) ≤ 100 √n ≤ n`
  have hX (I : Finset (Fin n)) : gapUnits I ≤ n := by
    have h1 := gapUnits_mul_le I
    have h2 := abs_gap_le I
    have h3 : (gapUnits I : ℝ) * (√(n : ℝ) / 100) ≤ n * (√(n : ℝ) / 100) := by nlinarith
    have h4 : (gapUnits I : ℝ) ≤ n := le_of_mul_le_mul_right h3 unit_pos
    exact_mod_cast h4
  have hzero (I : Finset (Fin n)) (h0 : gapUnits I = 0) :
      9 / 64 ≤ (binKernel n I).prob (fun J => 1 ≤ gapUnits J) :=
    (units_near hL I (by omega)).trans (Distribution.prob_mono _ fun J hJ => by omega)
  have hq : 1000 * Real.log n ≤ (n : ℝ) := by nlinarith
  have key := hdrift (binKernel n) gapUnits n hX (units_grow hL) hzero hq I₀ t ht
  rw [Real.rpow_neg_one, ← one_div] at key
  refine key.trans (hitProb_mono _ (fun I hI => ?_) t I₀)
  -- `|s| ≥ 1000 log n · √n/100 = 10 √n log n ≥ 22 √(3 n log n)`
  have h1 := gapUnits_mul_le I
  have h2 : 10 * Real.log n * √(n : ℝ) ≤ |gap I| := by nlinarith
  refine le_trans ?_ h2
  rw [← le_div_iff₀' (by norm_num : (0 : ℝ) < 22), Real.sqrt_le_left]
  · rw [div_pow, mul_pow, mul_pow, hww]
    have hnL : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn0.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hL hnL]
  · positivity

/-! ### Consensus absorbs; the vanishing-bias stage as a kernel event -/

lemma step_univ (r : Tgt3 n) : ThreeMajority.step univ r = univ := by
  ext v
  simp [ThreeMajority.mem_step, ThreeMajority.sampleCount, sampleCountOf]

lemma step_empty (r : Tgt3 n) : ThreeMajority.step ∅ r = ∅ := by
  rw [← compl_univ, step_compl, step_univ]

/-- Consensus on either opinion is absorbing. -/
lemma consensus_absorbing [NeZero n] (I : Finset (Fin n)) (hI : I = univ ∨ I = ∅) :
    (binKernel n I).prob (fun J => J = univ ∨ J = ∅) = 1 := by
  classical
  have h (r : Tgt3 n) : ThreeMajority.step I r = univ ∨ ThreeMajority.step I r = ∅ := by
    rcases hI with rfl | rfl
    · exact Or.inl (step_univ r)
    · exact Or.inr (step_empty r)
  rw [binKernel, Kernel.prob_ofStep]
  simp only [h, if_true]
  exact Dynamics.avg_const 1

/-- The occupation probability of consensus, as an expectation over rounds. -/
lemma event_consensus [NeZero n] (T : ℕ) (I : Finset (Fin n)) :
    (binKernel n).event (fun J => J = univ ∨ J = ∅) T I
      = expList (Tgt3 n) T (fun l =>
          if ThreeMajority.run I l = univ ∨ ThreeMajority.run I l = ∅ then (1 : ℝ) else 0) := by
  classical
  rw [binKernel, Kernel.event_ofStep]
  congr 1
  funext l
  rw [run_eq_foldl]
  congr

/-- **The vanishing-bias stage** (`majority3_vanishing_bias`, applied to `I` or to its
complement): from a gap at least `22 √(3 n log n)` in absolute value, consensus holds after
`10 · phases n 3 ≤ 390 log n` rounds with probability at least `1 - 429 log n / n`. -/
lemma event_consensus_of_gap [NeZero n] (hL : 40 ≤ Real.log n) (I : Finset (Fin n))
    (hI : 22 * √(3 * n * Real.log n) ≤ |gap I|) :
    1 - 429 * Real.log n / n
      ≤ (binKernel n).event (fun J => J = univ ∨ J = ∅) (10 * phases n 3) I := by
  classical
  rw [event_consensus]
  rcases le_total 0 (gap I) with hg | hg
  · rw [abs_of_nonneg hg] at hI
    refine (majority3_vanishing_bias hL I hI).2.trans (expList_le_expList fun l => ?_)
    split_ifs <;> simp_all
  · have hc : 22 * √(3 * n * Real.log n) ≤ (Iᶜ.card : ℝ) - (n - Iᶜ.card) := by
      change _ ≤ gap Iᶜ
      rw [gap_compl]
      rw [abs_of_nonpos hg] at hI
      exact hI
    refine (majority3_vanishing_bias hL Iᶜ hc).2.trans (expList_le_expList fun l => ?_)
    rw [run_compl]
    split_ifs with h1 h2 <;> simp_all [compl_eq_univ_iff]

/-- **Binary 3-Majority from any configuration.** There is `C > 0` such that, for `log n ≥ 40`,
from any configuration `I₀` (in particular from a perfectly balanced one), all nodes hold the same
opinion after any `T ≥ C log n` rounds with probability at least `1 - C log n / n`. -/
theorem majority3_any_start : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 40 ≤ Real.log n →
    ∀ (I₀ : Finset (Fin n)) (T : ℕ), C * Real.log n ≤ T →
      1 - C * Real.log n / n
        ≤ expList (Tgt3 n) T (fun l =>
            if ThreeMajority.run I₀ l = univ ∨ ThreeMajority.run I₀ l = ∅ then (1 : ℝ) else 0) := by
  /- Symmetry breaking within `t₁ = ⌈C₀ log n⌉` rounds w.p. `1 - 1/n`, then the vanishing-bias
  stage within `390 log n` rounds w.p. `1 - 429 log n / n`; consensus absorbs, so the remaining
  rounds keep it. -/
  obtain ⟨C₀, hC₀, hsb⟩ := majority3_symmetry_breaking
  refine ⟨C₀ + 430, by positivity, fun n hL I₀ T hT => ?_⟩
  obtain ⟨hn0, -⟩ := sqrt_ge_of_log hL
  haveI : NeZero n := ⟨by exact_mod_cast hn0.ne'⟩
  have hT₂ : ((10 * phases n 3 : ℕ) : ℝ) ≤ 390 * Real.log n := by
    have := phases_le hL (le_refl (3 : ℝ))
    push_cast
    linarith
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℕ, t₁ = ⌈C₀ * Real.log n⌉₊ := ⟨_, rfl⟩
  have ht₁le : C₀ * Real.log n ≤ t₁ := ht₁ ▸ Nat.le_ceil _
  have ht₁lt : (t₁ : ℝ) < C₀ * Real.log n + 1 := ht₁ ▸ Nat.ceil_lt_add_one (by positivity)
  -- hit the large-gap set, then absorb
  have hcomp := hitProb_sub_le_event (binKernel n) (consensus_absorbing)
    (by positivity : (0 : ℝ) ≤ 429 * Real.log n / n) (event_consensus_of_gap hL) t₁ I₀
  have hsb' := hsb n hL I₀ t₁ ht₁le
  -- more rounds keep consensus
  have hle : t₁ + 10 * phases n 3 ≤ T := by
    have : ((t₁ + 10 * phases n 3 : ℕ) : ℝ) ≤ T := by
      push_cast at hT₂ ⊢
      nlinarith
    exact_mod_cast this
  have hmono := Kernel.event_monotone (binKernel n) consensus_absorbing I₀ hle
  rw [← event_consensus]
  have hfin : 1 - (C₀ + 430) * Real.log n / n ≤ 1 - 1 / n - 429 * Real.log n / n := by
    rw [sub_sub, ← add_div, sub_le_sub_iff_left, div_le_div_iff_of_pos_right hn0]
    nlinarith
  simp only at hmono
  linarith

/-- **Binary 3-Majority from any configuration, with high probability.** There is `C > 0` such
that, for `log n ≥ C`, from any configuration `I₀` all nodes hold the same opinion after any
`T ≥ C log n` rounds with probability at least `1 - 1/n`. It runs `majority3_any_start` twice:
each block fails with probability at most `ε = C₀ log n / n` from every configuration, and
consensus absorbs, so both fail with probability at most `ε² ≤ 1/n`. -/
theorem majority3_any_start_whp : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), C ≤ Real.log n →
    ∀ (I₀ : Finset (Fin n)) (T : ℕ), C * Real.log n ≤ T →
      1 - 1 / (n : ℝ)
        ≤ expList (Tgt3 n) T (fun l =>
            if ThreeMajority.run I₀ l = univ ∨ ThreeMajority.run I₀ l = ∅ then (1 : ℝ) else 0) := by
  /- Two blocks of `majority3_any_start`, each failing with probability at most
  `ε = C₀ log n / n` from any configuration; consensus absorbs, so both fail with probability at
  most `ε² ≤ 1/n` (`event_amplify`). -/
  obtain ⟨C₀, hC₀, h⟩ := majority3_any_start
  refine ⟨7 * C₀ + 40, by positivity, fun n hL I₀ T hT => ?_⟩
  have hL40 : 40 ≤ Real.log n := by linarith
  obtain ⟨hn0, -⟩ := sqrt_ge_of_log hL40
  haveI : NeZero n := ⟨by exact_mod_cast hn0.ne'⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  rw [← hLdef] at hL hL40 hT
  have hL0 : 0 ≤ C₀ * L := by positivity
  -- the two blocks: `T₀ = ⌈C₀ log n⌉` and `T₁ = T - T₀ ≥ C₀ log n`
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℕ, T₀ = ⌈C₀ * L⌉₊ := ⟨_, rfl⟩
  have hT₀le : C₀ * L ≤ T₀ := hT₀ ▸ Nat.le_ceil _
  have hT₀lt : (T₀ : ℝ) < C₀ * L + 1 := hT₀ ▸ Nat.ceil_lt_add_one hL0
  have hT₀T : T₀ ≤ T := by
    have : (T₀ : ℝ) ≤ T := by nlinarith
    exact_mod_cast this
  have hT₁ : C₀ * L ≤ ((T - T₀ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hT₀T]
    nlinarith
  have hblock (b : Finset (Fin n)) (t : ℕ) (ht : C₀ * L ≤ t) :
      1 - C₀ * L / n ≤ (binKernel n).event (fun J => J = univ ∨ J = ∅) t b := by
    rw [event_consensus]
    have := h n (hLdef ▸ hL40) b t (hLdef ▸ ht)
    rwa [← hLdef] at this
  have hamp := event_amplify (binKernel n) consensus_absorbing (by positivity)
    (fun b => hblock b (T - T₀) hT₁) I₀ (hblock I₀ T₀ hT₀le)
  rw [Nat.add_sub_cancel' hT₀T, event_consensus] at hamp
  refine le_trans ?_ hamp
  -- `(C₀ log n / n)² ≤ 1/n`, as `n = e^{log n} ≥ (log n)⁴/24 ≥ C₀² (log n)²` for `log n ≥ 7 C₀`
  have hexp := Real.pow_div_factorial_le_exp (x := L) (by linarith) 4
  rw [hLdef, Real.exp_log hn0, ← hLdef] at hexp
  norm_num [Nat.factorial] at hexp
  have hC : C₀ ≤ L / 7 := by linarith
  have hC2 : (C₀ * L) ^ 2 ≤ n := by
    have h1 : C₀ * L ≤ L / 7 * L := mul_le_mul_of_nonneg_right hC (by linarith)
    have h2 : (C₀ * L) ^ 2 ≤ (L / 7 * L) ^ 2 := pow_le_pow_left₀ hL0 h1 2
    nlinarith
  have : C₀ * L / n * (C₀ * L / n) ≤ 1 / n := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hn0]
    nlinarith
  linarith

end Plurality
