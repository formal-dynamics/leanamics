import Median.BinaryMoves

/-! # The binary median dynamics: assembling the phases

`binary_consensus` below is the kernel form of `Median.consensus_whp`: if
`log n ≥ 128` and the `true` nodes outnumber the `false` ones by at least
`128 √(n log n)`, then all nodes hold `true` after `⌈128 log n⌉` rounds with
probability at least `1 - 128/n`.

The chain runs through nested phases (`Dynamics.Kernel.nested_phases`, the
paper's Lemma A.4), `A 1 ⊇ … ⊇ A T` with `T = T₁ + T₂ + 1` phases of `ℓ = 4`
rounds, per-round failure `ε = n⁻²` and per-move failure `ν = n^{-1/2}`
(whose fourth power is `n⁻²` again):

* **Growth** `A i = growthSet n ((5/4)^(i-1) Λ)` for `i ≤ T₁`, with the gap
  threshold `Λ = 128 √(n log n)` (`growth_move`); after
  `T₁ = ⌈log n / log (5/4)⌉₊ + 1` phases the threshold exceeds `n`, forcing
  the minority below `n/4` (`growthSet_sub_satSet`).
* **Saturation** `A (T₁ + 1 + j) = satSet n (max ((n/4)(7/8)^j) β)` for
  `j < T₂`, with `β = 512 log n` (`sat_move`); since
  `(8/7)^(T₂-1) ≥ (8/7) n`, after `T₂ = ⌈log n / log (8/7)⌉₊ + 2` phases the
  geometric part is at most `1/4`, so the threshold is `β`.
* **Consensus** `A T = consSet`: from `{m < β}`, one round reaches consensus
  except with probability `ν` (`mono_move`, Markov), and consensus absorbs.

`T ≤ 13 log n + 6`, so the `4T ≤ 52 log n + 24 ≤ ⌈128 log n⌉₊` rounds fit
(`log n ≥ 128`), and the failure budget is `T (4n⁻² + ν⁴) = 5T/n² ≤ 128/n`
(because `log n ≤ n`). Padding to the exact round count uses that the
all-`true` event absorbs (`Dynamics.Kernel.event_monotone`).
-/

namespace Median

open Finset Real Dynamics

/-- `n ≤ q ^ ⌈log n / log q⌉₊` for `q > 1`. -/
lemma le_pow_ceil {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 1 < q) :
    (n : ℝ) ≤ q ^ ⌈Real.log n / Real.log q⌉₊ := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_le_log_iff hn0 (by positivity), Real.log_pow]
  have := Nat.le_ceil (Real.log n / Real.log q)
  rwa [div_le_iff₀ hlq] at this

/-- The saturation threshold `(n/4)(7/8)^j`, floored at `β`, shrinks by `7/8`
per round while staying above `β`. -/
lemma sat_threshold_step (s β : ℝ) (hβ0 : 0 ≤ β) (j : ℕ) :
    max ((7 / 8 : ℝ) * max (s * ((7 / 8 : ℝ) ^ j)) β) β
      ≤ max (s * ((7 / 8 : ℝ) ^ (j + 1))) β := by
  have hs : (7 / 8 : ℝ) * (s * ((7 / 8 : ℝ) ^ j)) = s * ((7 / 8 : ℝ) ^ (j + 1)) := by
    rw [pow_succ]
    ring
  rcases le_total (s * ((7 / 8 : ℝ) ^ j)) β with h | h
  · have e : max (s * ((7 / 8 : ℝ) ^ j)) β = β := max_eq_right h
    have h78 : (7 / 8 : ℝ) * β ≤ β := by nlinarith
    refine max_le ?_ (le_max_right _ _)
    calc (7 / 8 : ℝ) * max (s * ((7 / 8 : ℝ) ^ j)) β
        = (7 / 8 : ℝ) * β := by rw [e]
      _ ≤ β := h78
      _ ≤ max (s * ((7 / 8 : ℝ) ^ (j + 1))) β := le_max_right _ _
  · have e : max (s * ((7 / 8 : ℝ) ^ j)) β = s * ((7 / 8 : ℝ) ^ j) := max_eq_left h
    refine max_le ?_ (le_max_right _ _)
    calc (7 / 8 : ℝ) * max (s * ((7 / 8 : ℝ) ^ j)) β
        = (7 / 8 : ℝ) * (s * ((7 / 8 : ℝ) ^ j)) := by rw [e]
      _ = s * ((7 / 8 : ℝ) ^ (j + 1)) := hs
      _ ≤ max (s * ((7 / 8 : ℝ) ^ (j + 1))) β := le_max_left _ _

/-- `a * c ≤ a` for `0 ≤ a` and `c ≤ 1`. -/
lemma mul_le_left_of_le_one {a c : ℝ} (ha : 0 ≤ a) (hc : c ≤ 1) :
    a * c ≤ a := by
  nlinarith [ha, hc]

/-- `c * a ≤ a` for `0 ≤ a` and `c ≤ 1`. -/
lemma mul_le_right_le_one {a c : ℝ} (ha : 0 ≤ a) (hc : c ≤ 1) :
    c * a ≤ a := by
  nlinarith [ha, hc]

/-- `a ≤ (5/4) * a` for `0 ≤ a`. -/
lemma le_mul_five_fourth {a : ℝ} (ha : 0 ≤ a) : a ≤ (5 / 4) * a := by
  nlinarith [ha, (show (1 : ℝ) ≤ 5 / 4 by norm_num)]

/-- `n < (5/4) * (X * Λ)` from `n ≤ X` and `1 < (5/4) * Λ`, for `n > 0`. -/
lemma lt_mul_left_of_lt {X Λ' n : ℝ} (hXn : n ≤ X) (hc1 : 1 < (5 / 4 : ℝ) * Λ')
    (_hc0 : (0 : ℝ) ≤ (5 / 4 : ℝ) * Λ') (hn0 : 0 < n) :
    n < (5 / 4 : ℝ) * (X * Λ') := by
  have hpos : (0 : ℝ) ≤ X := le_trans hn0.le hXn
  nlinarith [hXn, hc1, hn0, hpos]

/-- `log n ≤ n` once `2^20 log n ≤ n` (with `log n ≥ 0`). -/
lemma log_le_of_big {n : ℕ} (hbig : (2 ^ 20 : ℝ) * Real.log n ≤ (n : ℝ))
    (_hL0 : 0 ≤ Real.log n) : Real.log n ≤ (n : ℝ) := by
  nlinarith [hbig, (show (1 : ℝ) ≤ 2 ^ 20 by norm_num)]

/-- The failure budget: with `log n ≥ 128`, `log n ≤ n` and `T ≤ 13 log n + 6`,
the total failure `T (4n⁻² + n⁻²)` is at most `128/n`. -/
lemma five_phases_budget {T : ℝ} {n : ℕ} (hn0 : (0 : ℝ) < n) (hn1 : (1 : ℝ) ≤ n)
    (hT : T ≤ 13 * Real.log n + 6) (hLn : Real.log n ≤ (n : ℝ)) :
    T * (4 * (1 / (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2) ≤ 128 / (n : ℝ) := by
  have hcomb : T * (4 * (1 / (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2)
      = T * 5 / (n : ℝ) ^ 2 := by
    ring
  have hbound : T * 5 ≤ 128 * (n : ℝ) := by
    linarith
  rw [hcomb, div_le_div_iff₀ (by nlinarith [hn0] : (0 : ℝ) < (n : ℝ) ^ 2) hn0]
  nlinarith [hbound, hn0.le]

set_option maxHeartbeats 1000000 in
/-- **Binary consensus (kernel form).** If `log n ≥ 128` and the `true` nodes
outnumber the `false` ones by at least `128 √(n log n)`, then all nodes hold
`true` after `⌈128 log n⌉` rounds with probability at least `1 - 128/n`. -/
theorem binary_consensus {n : ℕ} [NeZero n] (hL : (128 : ℝ) ≤ Real.log n)
    (x : Config n Bool) (hx : 128 * √((n : ℝ) * Real.log n) ≤ gapR x) :
    1 - 128 / (n : ℝ) ≤ expList (Round n) ⌈128 * Real.log n⌉₊
      (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.log n := hL.trans' (by norm_num)
  have hβpos : (0 : ℝ) ≤ 512 * Real.log n := by positivity
  have hq1 : (1 : ℝ) < 5 / 4 := by norm_num
  have hq2 : (1 : ℝ) < 8 / 7 := by norm_num
  -- the gap threshold `Λ = 128 √(n log n)`
  have hΛ2 : (128 * √((n : ℝ) * Real.log n)) ^ 2
      = 16384 * (n : ℝ) * Real.log n := by
    have hnn : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn0.le hL0
    have h128 : ((128 : ℝ) ^ 2) = 16384 := by norm_num
    rw [mul_pow, Real.sq_sqrt hnn, h128]
    ring
  have hΛ85 : (4 : ℝ) / 5 < 128 * √((n : ℝ) * Real.log n) := by
    have h1 : (1 : ℝ) ≤ √((n : ℝ) * Real.log n) :=
      Real.one_le_sqrt.mpr (by nlinarith [hn1, hL, hL0])
    have h2 : (128 : ℝ) * 1 ≤ 128 * √((n : ℝ) * Real.log n) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 : (4 : ℝ) / 5 < 128 := by norm_num
    linarith
  -- `β = 512 log n` is below `n/4`, and the growth threshold squares right
  have hβn4 : 512 * Real.log n ≤ (n : ℝ) / 4 := by
    have h2048 : (2048 : ℝ) * Real.log n ≤ (n : ℝ) := by
      have hbig := big_log_le hL
      refine le_trans (mul_le_mul_of_nonneg_right (by norm_num) hL0) hbig
    linarith
  have hG2gen : ∀ i : ℕ, 1 ≤ i → 16384 * (n : ℝ) * Real.log n
      ≤ ((5 / 4 : ℝ) ^ (i - 1) * (128 * √((n : ℝ) * Real.log n))) ^ 2 := by
    intro i _hi
    have hX0 : (0 : ℝ) ≤ (5 / 4 : ℝ) ^ (i - 1) := pow_nonneg (by norm_num) _
    have hX : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ (i - 1) := one_le_pow₀ (le_of_lt hq1)
    have hsq : (1 : ℝ) ≤ ((5 / 4 : ℝ) ^ (i - 1)) ^ 2 := by nlinarith [hX, hX0]
    have hnn : (0 : ℝ) ≤ 16384 * (n : ℝ) * Real.log n := by positivity
    rw [mul_pow, hΛ2]
    nlinarith [hsq, hnn]
  -- the phase counts
  set T1 : ℕ := ⌈Real.log n / Real.log ((5 : ℝ) / 4)⌉₊ + 1 with hT1def
  set T2 : ℕ := ⌈Real.log n / Real.log ((8 : ℝ) / 7)⌉₊ + 2 with hT2def
  have hT1pos : 1 ≤ T1 := by rw [hT1def]; omega
  have hT2pos : 1 ≤ T2 := by rw [hT2def]; omega
  have hT1e : T1 - 1 = ⌈Real.log n / Real.log ((5 : ℝ) / 4)⌉₊ := by rw [hT1def]; omega
  have hT2e : T2 - 2 = ⌈Real.log n / Real.log ((8 : ℝ) / 7)⌉₊ := by rw [hT2def]; omega
  have hT1b : (T1 : ℝ) ≤ 5 * Real.log n + 2 := by
    rw [hT1def]
    have h1 : ((⌈Real.log n / Real.log ((5 : ℝ) / 4)⌉₊ : ℕ) : ℝ)
        < Real.log n / Real.log ((5 : ℝ) / 4) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hL0 (Real.log_pos hq1).le)
    have hdiv : Real.log n / Real.log ((5 : ℝ) / 4) ≤ 5 * Real.log n := by
      rw [div_le_iff₀ (Real.log_pos hq1)]
      have h51 : (1 : ℝ) ≤ 5 * Real.log ((5 : ℝ) / 4) := by
        linarith [log_five_fourth_ge]
      nlinarith [h51, hL0]
    push_cast
    linarith
  have hT2b : (T2 : ℝ) ≤ 8 * Real.log n + 3 := by
    rw [hT2def]
    have h1 : ((⌈Real.log n / Real.log ((8 : ℝ) / 7)⌉₊ : ℕ) : ℝ)
        < Real.log n / Real.log ((8 : ℝ) / 7) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hL0 (Real.log_pos hq2).le)
    have hdiv : Real.log n / Real.log ((8 : ℝ) / 7) ≤ 8 * Real.log n := by
      rw [div_le_iff₀ (Real.log_pos hq2)]
      have h81 : (1 : ℝ) ≤ 8 * Real.log ((8 : ℝ) / 7) := by
        linarith [log_eight_seventh_ge]
      nlinarith [h81, hL0]
    push_cast
    linarith
  have hpow1 : (n : ℝ) ≤ (5 / 4 : ℝ) ^ (T1 - 1) := by
    rw [hT1e]
    exact le_pow_ceil hn hq1
  have hpow2 : (n : ℝ) ≤ (8 / 7 : ℝ) ^ (T2 - 2) := by
    rw [hT2e]
    exact le_pow_ceil hn hq2
  -- after `T1` growth phases the gap threshold exceeds `n`
  have hc1 : (1 : ℝ) < (5 / 4) * (128 * √((n : ℝ) * Real.log n)) := by
    linarith [hΛ85]
  have hgrow : (n : ℝ) < (5 / 4) * ((5 / 4) ^ (T1 - 1)
      * (128 * √((n : ℝ) * Real.log n))) :=
    lt_mul_left_of_lt hpow1 hc1 (by positivity) hn0
  -- after `T2 - 1` saturation phases the threshold is `β`
  have hsmall : (n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (T2 - 1)) ≤ 512 * Real.log n := by
    have hA2' : (n : ℝ) * ((8 : ℝ) / 7) ≤ ((8 : ℝ) / 7) ^ (T2 - 1) := by
      rw [show T2 - 1 = (T2 - 2) + 1 from by omega, pow_succ]
      linarith [hpow2]
    have hinv : ((7 / 8 : ℝ) ^ (T2 - 1)) = 1 / (((8 : ℝ) / 7) ^ (T2 - 1)) := by
      rw [one_div, ← inv_pow]
      congr 1
      norm_num
    have hmono : ((7 / 8 : ℝ) ^ (T2 - 1)) ≤ 1 / ((n : ℝ) * ((8 : ℝ) / 7)) := by
      rw [hinv]
      exact one_div_le_one_div_of_le (by positivity) hA2'
    have hval : (n : ℝ) / 4 * (1 / ((n : ℝ) * ((8 : ℝ) / 7))) = (7 : ℝ) / 32 := by
      field_simp
      ring
    calc (n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (T2 - 1))
        ≤ (n : ℝ) / 4 * (1 / ((n : ℝ) * ((8 : ℝ) / 7))) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (7 : ℝ) / 32 := hval
      _ ≤ 512 * Real.log n := by linarith [hL]
  -- the nested phases
  let A : ℕ → Set (Config n Bool) := fun p =>
    if p ≤ T1 then growthSet n ((5 / 4 : ℝ) ^ (p - 1) * (128 * √((n : ℝ) * Real.log n)))
    else if p ≤ T1 + T2 then
      satSet n (max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (p - T1 - 1))) (512 * Real.log n))
    else consSet
  have hA1 : ∀ p, p ≤ T1 →
      A p = growthSet n ((5 / 4 : ℝ) ^ (p - 1)
        * (128 * √((n : ℝ) * Real.log n))) := fun _ hp => if_pos hp
  have hA2 : ∀ p, T1 < p → p ≤ T1 + T2 →
      A p = satSet n (max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (p - T1 - 1)))
        (512 * Real.log n)) := fun p h1 h2 => by
    simp only [A]
    rw [if_neg (by omega), if_pos h2]
  have hA3 : ∀ p, T1 + T2 < p → A p = consSet := fun p h => by
    simp only [A]
    rw [if_neg (by omega), if_neg (by omega)]
  have hnest : ∀ i, 1 ≤ i → i < T1 + T2 + 1 → A (i + 1) ⊆ A i := by
    intro i _hi1 _hiT
    by_cases h1 : i + 1 ≤ T1
    · rw [hA1 _ h1, hA1 _ (by omega), show i + 1 - 1 = (i - 1) + 1 from by omega]
      refine growthSet_sub n ?_
      rw [pow_succ]
      have hΛ0' : (0 : ℝ) ≤ (5 / 4 : ℝ) ^ (i - 1) * (128 * √((n : ℝ) * Real.log n)) :=
        mul_nonneg (pow_nonneg (by norm_num) _) (by positivity)
      linarith [le_mul_five_fourth hΛ0']
    by_cases h2 : i ≤ T1
    · rw [hA2 _ (by omega) (by omega), show (i + 1) - T1 - 1 = 0 from by omega,
        pow_zero, mul_one, hA1 _ h2]
      intro y hy
      have hmax : max ((n : ℝ) / 4) (512 * Real.log n) = (n : ℝ) / 4 :=
        max_eq_left hβn4
      rw [hmax] at hy
      exact mem_growthSet.mpr (Or.inl hy)
    by_cases h3 : i + 1 ≤ T1 + T2
    · rw [hA2 _ (by omega) h3, show (i + 1) - T1 - 1 = (i - T1 - 1) + 1 from by omega,
        hA2 _ (by omega) (by omega)]
      have hkey : max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ ((i - T1 - 1) + 1))) (512 * Real.log n)
          ≤ max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1))) (512 * Real.log n) := by
        refine max_le_iff.mpr ⟨?_, le_max_right _ _⟩
        have h1 : (n : ℝ) / 4 * ((7 / 8 : ℝ) ^ ((i - T1 - 1) + 1))
            ≤ (n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1)) := by
          rw [pow_succ]
          have hp : (0 : ℝ) ≤ (n : ℝ) * ((7 / 8 : ℝ) ^ (i - T1 - 1)) := by positivity
          linarith [hp]
        exact le_trans h1 (le_max_left _ _)
      exact satSet_sub n hkey
    · rw [hA3 _ (by omega), hA2 _ (by omega) (by omega)]
      intro y hy
      have hfr : falsesR y = 0 :=
        (eq_true_iff_falsesR_zero).mp (mem_consSet.mp hy)
      refine mem_satSet.mpr ?_
      rw [hfr]
      have hb : (0 : ℝ) < 512 * Real.log n := by linarith [hL]
      exact lt_of_lt_of_le hb (le_max_right _ _)
  have hε : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
  have hinv : 1 / (n : ℝ) ^ 2 ≤ exp (-(Real.log n / 2)) := inv_sq_le_exp hL
  have hstay : ∀ i, 1 ≤ i → i ≤ T1 + T2 + 1 → ∀ a ∈ A i,
      1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob (· ∈ A i) := by
    intro i hi1 _hiT a ha
    by_cases h1 : i ≤ T1
    · rw [hA1 _ h1] at ha ⊢
      have hmove' := growth_move hL (by positivity) (hG2gen i hi1) ha
      have hle : (5 / 4 : ℝ) ^ (i - 1) * (128 * √((n : ℝ) * Real.log n))
          ≤ (5 / 4) * ((5 / 4 : ℝ) ^ (i - 1)
            * (128 * √((n : ℝ) * Real.log n))) :=
        le_mul_five_fourth
          (mul_nonneg (pow_nonneg (by norm_num) _) (by positivity))
      exact le_trans hmove' (Distribution.prob_mono _ (growthSet_sub n hle))
    by_cases h2 : i ≤ T1 + T2
    · rw [hA2 _ (by omega) h2] at ha ⊢
      have ht0 : (0 : ℝ) ≤ max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1)))
          (512 * Real.log n) :=
        le_trans hβpos (le_max_right _ _)
      have htn : max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1))) (512 * Real.log n)
          ≤ (n : ℝ) / 4 := by
        refine max_le_iff.mpr ⟨?_, hβn4⟩
        exact mul_le_left_of_le_one (by positivity)
          (pow_le_one₀ (by norm_num) (by norm_num))
      have hmove' := sat_move hL ht0 htn ha
      have hstayle : max ((7 / 8 : ℝ)
          * max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1))) (512 * Real.log n))
          (512 * Real.log n)
          ≤ max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1))) (512 * Real.log n) := by
        refine max_le_iff.mpr ⟨?_, le_max_right _ _⟩
        exact mul_le_right_le_one ht0 (by norm_num : (7 / 8 : ℝ) ≤ 1)
      exact le_trans hmove' (Distribution.prob_mono _ (satSet_sub n hstayle))
    · rw [hA3 _ (by omega)] at ha ⊢
      rw [cons_absorb ha]
      linarith [hε]
  have hmove : ∀ i, 1 ≤ i → i < T1 + T2 + 1 → ∀ a ∈ A i,
      1 - exp (-(Real.log n / 2)) ≤ (Median.kernel n Bool a).prob (· ∈ A (i + 1)) := by
    intro i hi1 _hiT a ha
    by_cases h1 : i + 1 ≤ T1
    · rw [hA1 _ (by omega)] at ha
      rw [hA1 _ h1, show i + 1 - 1 = (i - 1) + 1 from by omega, pow_succ]
      have hmove' := growth_move hL (by positivity) (hG2gen i hi1) ha
      refine le_trans (by linarith [hinv]) (le_trans hmove' (Distribution.prob_mono _ ?_))
      exact growthSet_sub n (le_of_eq (by ring))
    by_cases h2 : i ≤ T1
    · rw [hA1 _ h2] at ha
      rw [hA2 _ (by omega) (by omega), show (i + 1) - T1 - 1 = 0 from by omega,
        pow_zero, mul_one]
      have hgrowI : (n : ℝ) < (5 / 4) * ((5 / 4) ^ (i - 1)
          * (128 * √((n : ℝ) * Real.log n))) := by
        have hi : i = T1 := by omega
        rw [hi]
        exact hgrow
      have hmove' := growth_move hL (by positivity) (hG2gen i hi1) ha
      refine le_trans (by linarith [hinv]) (le_trans hmove' (Distribution.prob_mono _ ?_))
      exact le_trans (growthSet_sub_satSet n hgrowI) (satSet_sub n (le_max_left _ _))
    by_cases h3 : i + 1 ≤ T1 + T2
    · rw [hA2 _ (by omega) h3, show (i + 1) - T1 - 1 = (i - T1 - 1) + 1 from by omega]
      rw [hA2 _ (by omega) (by omega)] at ha
      have ht0 : (0 : ℝ) ≤ max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1)))
          (512 * Real.log n) :=
        le_trans hβpos (le_max_right _ _)
      have htn : max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1))) (512 * Real.log n)
          ≤ (n : ℝ) / 4 := by
        refine max_le_iff.mpr ⟨?_, hβn4⟩
        exact mul_le_left_of_le_one (by positivity)
          (pow_le_one₀ (by norm_num) (by norm_num))
      have hmove' := sat_move hL ht0 htn ha
      refine le_trans (by linarith [hinv]) (le_trans hmove' (Distribution.prob_mono _ ?_))
      exact satSet_sub n (sat_threshold_step _ _ hβpos (i - T1 - 1))
    · rw [hA3 _ (by omega)]
      rw [hA2 _ (by omega) (by omega)] at ha
      have hsmallI : (n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1))
          ≤ 512 * Real.log n := by
        rw [show i - T1 - 1 = T2 - 1 from by omega]
        exact hsmall
      have hmax : max ((n : ℝ) / 4 * ((7 / 8 : ℝ) ^ (i - T1 - 1))) (512 * Real.log n)
          = 512 * Real.log n := max_eq_right hsmallI
      rw [hmax] at ha
      exact mono_move hL ha
  have hx1 : x ∈ A 1 := by
    rw [hA1 1 hT1pos, show (1 : ℕ) - 1 = 0 from rfl, pow_zero, one_mul]
    exact mem_growthSet.mpr (Or.inr hx)
  -- run the chain
  have hK := Dynamics.Kernel.nested_phases (Median.kernel n Bool) A (T := T1 + T2 + 1)
    (by omega) 4 (ε := 1 / (n : ℝ) ^ 2) (ν := exp (-(Real.log n / 2)))
    (by positivity) (by positivity) hnest hstay hmove x hx1
  rw [hA3 _ (by omega)] at hK
  have hν4 : (exp (-(Real.log n / 2))) ^ 4 = 1 / (n : ℝ) ^ 2 := exp_half_pow_four hn
  rw [hν4] at hK
  -- pad the number of rounds up to `⌈128 log n⌉₊`
  have h4T : 4 * (T1 + T2 + 1) ≤ ⌈128 * Real.log n⌉₊ := by
    have hTn : (T1 : ℝ) + (T2 : ℝ) + 1 ≤ 13 * Real.log n + 6 := by
      linarith [hT1b, hT2b]
    have h52 : (52 : ℝ) * Real.log n + 24 ≤ 128 * Real.log n := by linarith [hL]
    have h4T' : ((4 * (T1 + T2 + 1) : ℕ) : ℝ) ≤ 128 * Real.log n := by
      push_cast
      linarith [hTn, h52]
    exact Nat.cast_le.mp (le_trans h4T' (Nat.le_ceil _))
  have habs : ∀ a : Config n Bool, a ∈ consSet →
      (Median.kernel n Bool a).prob (· ∈ consSet) = 1 := fun a ha => cons_absorb ha
  have hpad := Kernel.event_monotone (Median.kernel n Bool) (P := fun y => y ∈ consSet) habs x h4T
  -- the failure budget
  have hLn : Real.log n ≤ (n : ℝ) := log_le_of_big (big_log_le hL) hL0
  have hTn : (T1 : ℝ) + (T2 : ℝ) + 1 ≤ 13 * Real.log n + 6 := by
    linarith [hT1b, hT2b]
  have hfin : ((T1 + T2 + 1 : ℕ) : ℝ) * (4 * (1 / (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2)
      ≤ 128 / (n : ℝ) := by
    push_cast
    exact five_phases_budget hn0 hn1 hTn hLn
  -- conclude
  have hK' : 1 - ((T1 + T2 + 1 : ℕ) : ℝ) * (4 * (1 / (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2)
      ≤ (Median.kernel n Bool).event (fun y => y = (fun _ => true))
        (4 * (T1 + T2 + 1)) x := hK
  have hpad' : (Median.kernel n Bool).event (fun y => y = (fun _ => true))
        (4 * (T1 + T2 + 1)) x
      ≤ (Median.kernel n Bool).event (fun y => y = (fun _ => true))
        ⌈128 * Real.log n⌉₊ x := hpad
  refine le_trans ?_ (le_of_eq (kernel_event_true _ x))
  linarith [hK', hpad', hfin]

end Median
