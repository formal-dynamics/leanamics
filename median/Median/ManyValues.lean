import Median.Basic
import Median.Binary

/-! # Many values: the middle value wins fast (median dynamics)

Doerr, Goldberg, Minder, Sauerwald and Scheideler (SPAA 2011; Theorem 21 of the full version)
show that from a uniformly random start with `m` values the median rule reaches consensus in
`O(log m + log log n)` rounds when `m` is odd, but needs `Θ(log n)` rounds when `m` is even.
With two values the dynamics is 2-Choices, and a balanced start needs `Θ(log n)` rounds; with
three equally supported values the middle one wins in `O(log log n)` rounds. This file pins the
deterministic core of the odd case:

* `binary_consensus_fast`: with two values, a gap `Δ ≥ C √(n log n)` gives consensus within
  `O(log (n/Δ) + log log n)` rounds (the gap grows geometrically until the minority is a constant
  fraction, which then shrinks quadratically, `m ↦ ≈ 3m²/n`);
* `median_consensus_fast`: with values in a linear order, a margin `Δ` on both sides of a value
  `v` gives consensus on `v` within `O(log (n/Δ) + log log n)` rounds;
* `odd_split_consensus`: `2k+1` values with equal support: the middle value wins within
  `O(log k + log log n)` rounds.
-/

namespace Median
open Finset Dynamics

/-- **Fast binary consensus from a large gap.** If the `true` nodes outnumber the `false` ones by
at least `Δ ≥ C √(n log n)`, all nodes hold `true` after `⌈C (log (n/Δ) + log log n)⌉` rounds with
probability at least `1 - C/n`. -/
theorem binary_consensus_fast : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n Bool) (Δ : ℝ), C * √(n * Real.log n) ≤ Δ →
      Δ ≤ (ones x : ℝ) - (n - ones x) →
      1 - C / n ≤ expList (Round n) ⌈C * (Real.log (n / Δ) + Real.log (Real.log n))⌉₊
        (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  -- The proof is self-contained (all helpers are local `have`s), organized as follows:
  -- (A) scalar facts; (B) chaining one-round moves and composing segments (Markov property);
  -- (C) the quadratic saturation move `quad_move`; (D) the four segments: growth from the gap
  -- `Δ`, linear saturation `n/4 → n/8`, quadratic saturation `n/8 → β = 512 log n`, consensus;
  -- (E) round counts, padding and failure budget.
  open Real in
  · refine ⟨128, by norm_num, ?_⟩
    intro n _ hL
    /- (A) scalar facts -/
    have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hL0 : 0 ≤ log n := hL.trans' (by norm_num)
    have hβ0 : (0 : ℝ) ≤ 512 * log n := by positivity
    have hβn8 : 512 * log n ≤ (n : ℝ) / 8 := by
      have hbig := big_log_le hL
      have h1 : (4096 : ℝ) * log n ≤ 2 ^ 20 * log n :=
        mul_le_mul_of_nonneg_right (by norm_num) hL0
      linarith
    have hε : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hl2' : (1 / 2 : ℝ) ≤ log 2 := by
      have h := sub_one_div_le_log' (show (0 : ℝ) < 2 by norm_num)
      norm_num at h
      exact h
    have hl21 : log (2 : ℝ) ≤ 1 := by
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    -- `w ≤ q ^ ⌈log w / log q⌉₊` for `w ≥ 1`, `q > 1`
    have hceil : ∀ {w q : ℝ}, 1 ≤ w → 1 < q → w ≤ q ^ ⌈log w / log q⌉₊ := by
      intro w q hw hq
      have hlq : 0 < log q := log_pos hq
      have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
      have hpow0 : 0 < q ^ ⌈log w / log q⌉₊ := pow_pos (lt_trans zero_lt_one hq) _
      rw [← log_le_log_iff hw0 hpow0, log_pow]
      have := Nat.le_ceil (log w / log q)
      rwa [div_le_iff₀ hlq] at this
    /- (B) chaining one-round moves, composing segments -/
    have hmono_set : ∀ {B C : Set (Config n Bool)}, B ⊆ C → ∀ (t : ℕ) (a : Config n Bool),
        (Median.kernel n Bool).event (· ∈ B) t a ≤ (Median.kernel n Bool).event (· ∈ C) t a := by
      intro B C h t a
      classical
      unfold Dynamics.Kernel.event
      refine (Median.kernel n Bool).iterate_mono t (fun b => ?_) a
      by_cases hb : b ∈ B
      · simp [hb, h hb]
      · by_cases hc : b ∈ C <;> simp [hb, hc]
    -- if every state of `B i` moves into `B (i+1)` w.p. `≥ 1 - ε`, then `B T` after `T` rounds
    -- w.p. `≥ 1 - T ε`
    have hchain : ∀ {ε : ℝ}, 0 ≤ ε → ∀ (T : ℕ) (B : ℕ → Set (Config n Bool)),
        (∀ i, ∀ a ∈ B i, 1 - ε ≤ (Median.kernel n Bool a).prob (· ∈ B (i + 1))) →
        ∀ a ∈ B 0, 1 - T * ε ≤ (Median.kernel n Bool).event (· ∈ B T) T a := by
      intro ε hε T
      classical
      induction T with
      | zero =>
        intro B _ a ha
        simp [Dynamics.Kernel.event, ha]
      | succ T ih =>
        intro B hB a ha
        have hIH := ih (fun i => B (i + 1)) (fun i b hb => hB (i + 1) b hb)
        have hpt : ∀ b, (if b ∈ B 1 then (1 : ℝ) else 0) - T * ε
            ≤ (Median.kernel n Bool).event (· ∈ B (T + 1)) T b := by
          intro b
          by_cases hb : b ∈ B 1
          · rw [if_pos hb]
            exact hIH b hb
          · rw [if_neg hb]
            have h0 := (Median.kernel n Bool).event_nonneg (· ∈ B (T + 1)) T b
            have h1 : 0 ≤ (T : ℝ) * ε := mul_nonneg (Nat.cast_nonneg T) hε
            linarith
        have hstep : (Median.kernel n Bool).event (· ∈ B (T + 1)) (T + 1) a
            = (Median.kernel n Bool a).expect ((Median.kernel n Bool).event (· ∈ B (T + 1)) T) :=
          rfl
        have hexp := (Median.kernel n Bool a).expect_mono hpt
        rw [Distribution.expect_sub, Distribution.expect_const] at hexp
        have hprob : (Median.kernel n Bool a).expect (fun b => if b ∈ B 1 then (1 : ℝ) else 0)
            = (Median.kernel n Bool a).prob (· ∈ B 1) := rfl
        have h1 := hB 0 a ha
        rw [hstep]
        push_cast
        linarith
    -- Markov property: compose two segments
    have hcomp : ∀ {B C : Set (Config n Bool)} {t₁ t₂ : ℕ} {δ₁ δ₂ : ℝ}, 0 ≤ δ₂ →
        ∀ {a : Config n Bool}, 1 - δ₁ ≤ (Median.kernel n Bool).event (· ∈ B) t₁ a →
        (∀ b ∈ B, 1 - δ₂ ≤ (Median.kernel n Bool).event (· ∈ C) t₂ b) →
        1 - (δ₁ + δ₂) ≤ (Median.kernel n Bool).event (· ∈ C) (t₁ + t₂) a := by
      intro B C t₁ t₂ δ₁ δ₂ hδ₂ a h₁ h₂
      classical
      have hsplit : (Median.kernel n Bool).event (· ∈ C) (t₁ + t₂) a
          = (Median.kernel n Bool).iterate t₁ ((Median.kernel n Bool).event (· ∈ C) t₂) a := by
        unfold Dynamics.Kernel.event
        rw [Dynamics.Kernel.iterate_add_time]
      have hpt : ∀ b, (if b ∈ B then (1 : ℝ) else 0) + (-δ₂)
          ≤ (Median.kernel n Bool).event (· ∈ C) t₂ b := by
        intro b
        by_cases hb : b ∈ B
        · rw [if_pos hb]
          linarith [h₂ b hb]
        · rw [if_neg hb]
          linarith [(Median.kernel n Bool).event_nonneg (· ∈ C) t₂ b]
      have hmono := (Median.kernel n Bool).iterate_mono t₁ hpt a
      rw [Dynamics.Kernel.iterate_add, Dynamics.Kernel.iterate_const] at hmono
      have hB : (Median.kernel n Bool).event (· ∈ B) t₁ a
          = (Median.kernel n Bool).iterate t₁ (fun b => if b ∈ B then (1 : ℝ) else 0) a := rfl
      simp only at hmono
      rw [hsplit]
      linarith
    /- (C) the quadratic saturation move: from a minority `m < t ≤ n/8`, one round gives
    `m' < max (4t²/n) (512 log n)` except w.p. `n⁻²` (Bernstein, `𝔼[m'] ≤ 3m²/n ≤ 3t²/n`) -/
    have hquad : ∀ {t : ℝ}, t ≤ (n : ℝ) / 8 → ∀ {y : Config n Bool}, falsesR y < t →
        1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool y).prob
          (· ∈ satSet n (max (4 * t ^ 2 / (n : ℝ)) (512 * log n))) := by
      intro t _ht8 y hy
      classical
      have hβ12 : 12 ≤ 512 * log n := by linarith only [hL]
      have hm : falsesR y ≤ t := le_of_lt hy
      have hE : ∑ v, avg (fcoord y v) ≤ 3 * t ^ 2 / (n : ℝ) := by
        have h1 := expfalses_le y
        have h2 : 3 * falsesR y ^ 2 / (n : ℝ) ≤ 3 * t ^ 2 / (n : ℝ) := by
          have hsq : falsesR y ^ 2 ≤ t ^ 2 :=
            pow_le_pow_left₀ (falsesR_nonneg y) hm 2
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hn0.le
        exact le_trans h1 h2
      have hE0 : 0 ≤ ∑ v, avg (fcoord y v) :=
        Finset.sum_nonneg fun v _ => avg_nonneg fun p => fcoord_nonneg y v p
      obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ∑ v, avg (fcoord y v) + 1 := ⟨_, rfl⟩
      have hσ0 : 0 < s := by rw [hsdef]; linarith only [hE0]
      have hvar : ∑ v, variance (fcoord y v) ≤ s := by
        rw [hsdef]
        have h1 : ∑ v, variance (fcoord y v) ≤ ∑ v, avg (fcoord y v) :=
          Finset.sum_le_sum fun v _ => variance_fcoord_le y v
        linarith only [h1]
      have hden_eq : ∀ d : ℝ, 0 ≤ d → 2 * s * (1 + d / (3 * s)) = 2 * s + 2 * d / 3 := by
        intro d _hd0
        have hsnz : s ≠ 0 := by
          rw [hsdef]
          linarith
        field_simp
      have hfin : exp (-(2 * log n)) = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn
      by_cases hcase : 4 * t ^ 2 / (n : ℝ) < 512 * log n
      · -- the `β` term dominates
        have hmax : max (4 * t ^ 2 / (n : ℝ)) (512 * log n) = 512 * log n :=
          max_eq_right (le_of_lt hcase)
        rw [hmax]
        obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = 512 * log n - ∑ v, avg (fcoord y v) := ⟨_, rfl⟩
        have hEβ : ∑ v, avg (fcoord y v) ≤ 3 / 4 * (512 * log n) := by
          have h2 : 3 * t ^ 2 / (n : ℝ) = 3 / 4 * (4 * t ^ 2 / (n : ℝ)) := by ring
          refine le_trans hE ?_
          rw [h2]
          exact mul_le_mul_of_nonneg_left (le_of_lt hcase) (by norm_num : (0 : ℝ) ≤ 3 / 4)
        have hd0 : 0 ≤ d := by rw [hddef]; linarith only [hEβ, hβ0]
        have hdle : d ≤ 512 * log n := by rw [hddef]; linarith only [hE0]
        have hs_le : s ≤ 3 / 4 * (512 * log n) + 1 := by rw [hsdef]; linarith only [hEβ]
        have hd4 : 512 * log n / 4 ≤ d := by rw [hddef]; linarith only [hEβ]
        have hterm' : 2 * s + 2 * d / 3 ≤ 7 / 3 * (512 * log n) := by
          linarith only [hs_le, hdle, hβ12]
        have hD : 0 < 7 / 3 * (512 * log n) := by positivity
        have hbad := falses_tail_bernstein y hd0 hσ0 hvar
        have hden : 2 * s * (1 + d / (3 * s)) ≤ 7 / 3 * (512 * log n) := by
          rw [hden_eq d hd0]
          exact hterm'
        have hcD : (2 * log n) * (7 / 3 * (512 * log n)) ≤ d ^ 2 := by
          have hsq : 512 * log n / 4 * (512 * log n / 4) ≤ d * d :=
            mul_self_le_mul_self (by positivity) hd4
          obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = log n * log n := ⟨_, rfl⟩
          have hw0 : 0 ≤ w := by rw [hwdef]; positivity
          have hL' : (2 * log n) * (7 / 3 * (512 * log n)) = 7168 / 3 * w := by
            rw [hwdef]; ring
          have hR : 512 * log n / 4 * (512 * log n / 4) = 16384 * w := by rw [hwdef]; ring
          rw [pow_two, hL']
          linarith only [hsq, hR, hw0]
        have h0 : ∀ r : Round n, 0 ≤
            (if ∑ v, avg (fcoord y v) + d ≤ falsesR (step y r) then (1 : ℝ) else 0) :=
          fun r => by split <;> norm_num
        have h1 : ∀ r : Round n, step y r ∉ satSet n (512 * log n) →
            1 ≤ (if ∑ v, avg (fcoord y v) + d
              ≤ falsesR (step y r) then (1 : ℝ) else 0) := by
          intro r hr
          have hr' : ¬ (falsesR (step y r) < 512 * log n) := hr
          have hadd : ∑ v, avg (fcoord y v) + d = 512 * log n := by rw [hddef]; ring
          rw [hadd, if_pos (le_of_not_gt hr')]
        have hstep : 1 - avg (fun r : Round n =>
            if ∑ v, avg (fcoord y v) + d ≤ falsesR (step y r) then (1 : ℝ) else 0)
            ≤ (Median.kernel n Bool y).prob (· ∈ satSet n (512 * log n)) :=
          prob_step_ge y _ _ h0 h1
        have hexp := bernstein_exp_le hσ0 hd0 hD hden hcD
        linarith only [hstep, hbad, hexp, hfin]
      · -- the quadratic term dominates
        obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = t ^ 2 / (n : ℝ) := ⟨_, rfl⟩
        have h4u : 4 * t ^ 2 / (n : ℝ) = 4 * u := by rw [hudef]; ring
        rw [h4u] at hcase ⊢
        have hmax : max (4 * u) (512 * log n) = 4 * u := max_eq_left (le_of_not_gt hcase)
        rw [hmax]
        have hc' := le_of_not_gt hcase
        have hu128 : 128 * log n ≤ u := by linarith only [hc']
        have hu0 : 0 < u := by linarith only [hu128, hL]
        have hu1 : 1 ≤ u := by linarith only [hu128, hL]
        have hE3 : ∑ v, avg (fcoord y v) ≤ 3 * u := by
          rw [hudef, ← mul_div_assoc]
          exact hE
        obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = 4 * u - ∑ v, avg (fcoord y v) := ⟨_, rfl⟩
        have hd0 : 0 ≤ d := by rw [hddef]; linarith only [hE3, hu0]
        have hd_u : u ≤ d := by rw [hddef]; linarith only [hE3]
        have hdle : d ≤ 4 * u := by rw [hddef]; linarith only [hE0]
        have hs_le : s ≤ 3 * u + 1 := by rw [hsdef]; linarith only [hE3]
        have hterm' : 2 * s + 2 * d / 3 ≤ 32 / 3 * u := by
          linarith only [hs_le, hdle, hu1]
        have hD : 0 < 32 / 3 * u := by positivity
        have hbad := falses_tail_bernstein y hd0 hσ0 hvar
        have hden : 2 * s * (1 + d / (3 * s)) ≤ 32 / 3 * u := by
          rw [hden_eq d hd0]
          exact hterm'
        have hcD : (2 * log n) * (32 / 3 * u) ≤ d ^ 2 := by
          have h1 : (64 / 3 : ℝ) * log n ≤ u := by linarith only [hu128, hL0]
          have hkey : (2 * log n) * ((32 / 3 : ℝ) * u) = ((64 / 3 : ℝ) * log n) * u := by ring
          rw [pow_two, hkey]
          have p1 := mul_le_mul_of_nonneg_right h1 hu0.le
          have p2 := mul_le_mul hd_u hd_u hu0.le hd0
          linarith only [p1, p2]
        have h0 : ∀ r : Round n, 0 ≤
            (if ∑ v, avg (fcoord y v) + d ≤ falsesR (step y r) then (1 : ℝ) else 0) :=
          fun r => by split <;> norm_num
        have h1 : ∀ r : Round n, step y r ∉ satSet n (4 * u) →
            1 ≤ (if ∑ v, avg (fcoord y v) + d
              ≤ falsesR (step y r) then (1 : ℝ) else 0) := by
          intro r hr
          have hr' : ¬ (falsesR (step y r) < 4 * u) := hr
          have hadd : ∑ v, avg (fcoord y v) + d = 4 * u := by rw [hddef]; ring
          rw [hadd, if_pos (le_of_not_gt hr')]
        have hstep : 1 - avg (fun r : Round n =>
            if ∑ v, avg (fcoord y v) + d ≤ falsesR (step y r) then (1 : ℝ) else 0)
            ≤ (Median.kernel n Bool y).prob (· ∈ satSet n (4 * u)) :=
          prob_step_ge y _ _ h0 h1
        have hexp := bernstein_exp_le hσ0 hd0 hD hden hcD
        linarith only [hstep, hbad, hexp, hfin]
    /- (D) the four segments -/
    -- linear saturation: `6` rounds from `n/4` to `n/8` (`(7/8)^6 ≤ 1/2`)
    have hlin : ∀ y : Config n Bool, falsesR y < (n : ℝ) / 4 →
        1 - 6 * (1 / (n : ℝ) ^ 2)
          ≤ (Median.kernel n Bool).event (· ∈ satSet n ((n : ℝ) / 8)) 6 y := by
      intro y hy
      have hmove : ∀ j, ∀ a ∈ satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ j) (512 * log n)),
          1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob
            (· ∈ satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ (j + 1)) (512 * log n))) := by
        intro j a ha
        have ht0 : 0 ≤ max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ j) (512 * log n) :=
          le_trans hβ0 (le_max_right _ _)
        have htn : max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ j) (512 * log n) ≤ (n : ℝ) / 4 :=
          max_le (mul_le_left_of_le_one (by positivity)
            (pow_le_one₀ (by norm_num) (by norm_num))) (by linarith)
        exact le_trans (sat_move hL ht0 htn ha)
          (prob_mono_set' _ (satSet_sub n (sat_threshold_step _ _ hβ0 j)))
      have hy0 : y ∈ satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ 0) (512 * log n)) := by
        rw [pow_zero, mul_one]
        exact lt_of_lt_of_le hy (le_max_left _ _)
      have hc := hchain hε 6
        (fun j => satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ j) (512 * log n))) hmove y hy0
      have hsub : satSet n (max ((n : ℝ) / 4 * (7 / 8 : ℝ) ^ 6) (512 * log n))
          ⊆ satSet n ((n : ℝ) / 8) := by
        apply satSet_sub
        refine max_le ?_ hβn8
        have h1 : (7 / 8 : ℝ) ^ 6 ≤ 1 / 2 := by norm_num
        have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (n : ℝ) / 4 by positivity)
        linarith
      have h := le_trans hc (hmono_set hsub 6 y)
      push_cast at h
      exact h
    -- quadratic saturation: thresholds `q_j = (n/4)(1/2)^(2^j)`, `q_0 = n/8`, `4 q_j²/n = q_(j+1)`
    have hq_succ : ∀ j : ℕ, 4 * ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ j)) ^ 2 / (n : ℝ)
        = (n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by
      intro j
      have e : (1 / 2 : ℝ) ^ (2 ^ (j + 1)) = ((1 / 2 : ℝ) ^ (2 ^ j)) ^ 2 := by
        rw [pow_succ, pow_mul]
      rw [e]
      field_simp
    have hq_le : ∀ j : ℕ, (n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ j) ≤ (n : ℝ) / 8 := by
      intro j
      have h1 : (1 / 2 : ℝ) ^ (2 ^ j) ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.one_le_two_pow)
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (n : ℝ) / 4 by positivity)
      linarith
    have hqstep : ∀ q : ℝ, max (4 * (max q (512 * log n)) ^ 2 / (n : ℝ)) (512 * log n)
        ≤ max (4 * q ^ 2 / (n : ℝ)) (512 * log n) := by
      intro q
      rcases le_total q (512 * log n) with h | h
      · rw [max_eq_right h]
        have h4 : 4 * (512 * log n) ^ 2 / (n : ℝ) ≤ 512 * log n := by
          rw [div_le_iff₀ hn0]
          have p1 := mul_le_mul_of_nonneg_left hβn8 hβ0
          have p2 := mul_nonneg hβ0 hn0.le
          linarith only [p1, p2]
        rw [max_eq_right h4]
        exact le_max_right _ _
      · rw [max_eq_left h]
    have hquadseg : ∀ T : ℕ, (n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ T) ≤ 512 * log n →
        ∀ y : Config n Bool, falsesR y < (n : ℝ) / 8 →
        1 - T * (1 / (n : ℝ) ^ 2)
          ≤ (Median.kernel n Bool).event (· ∈ satSet n (512 * log n)) T y := by
      intro T hT y hy
      have hmove : ∀ j, ∀ a ∈ satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ j)) (512 * log n)),
          1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob
            (· ∈ satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ (j + 1))) (512 * log n))) := by
        intro j a ha
        have ht8 : max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ j)) (512 * log n) ≤ (n : ℝ) / 8 :=
          max_le (hq_le j) hβn8
        have hstep := hqstep ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ j))
        rw [hq_succ j] at hstep
        exact le_trans (hquad ht8 ha) (prob_mono_set' _ (satSet_sub n hstep))
      have hy0 : y ∈ satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ 0)) (512 * log n)) := by
        have e : (n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ 0) = (n : ℝ) / 8 := by norm_num; ring
        rw [e]
        exact lt_of_lt_of_le hy (le_max_left _ _)
      have hc := hchain hε T
        (fun j => satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ j)) (512 * log n))) hmove y hy0
      have hsub : satSet n (max ((n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ T)) (512 * log n))
          ⊆ satSet n (512 * log n) := by
        rw [max_eq_right hT]
      exact le_trans hc (hmono_set hsub T y)
    -- consensus: two phases of four rounds (`nested_phases`), `mono_move` and absorption
    have hcons : ∀ y : Config n Bool, falsesR y < 512 * log n →
        1 - 10 * (1 / (n : ℝ) ^ 2) ≤ (Median.kernel n Bool).event (· ∈ consSet) 8 y := by
      intro y hy
      have hβn4 : 512 * log n ≤ (n : ℝ) / 4 := by linarith
      let A : ℕ → Set (Config n Bool) :=
        fun i => if i ≤ 1 then satSet n (512 * log n) else consSet
      have hA1 : A 1 = satSet n (512 * log n) := if_pos le_rfl
      have hA2 : A 2 = consSet := if_neg (by norm_num)
      have hnest : ∀ i, 1 ≤ i → i < 2 → A (i + 1) ⊆ A i := by
        intro i h1 h2
        obtain rfl : i = 1 := by omega
        rw [hA1, hA2]
        intro z hz
        have hfr : falsesR z = 0 := (eq_true_iff_falsesR_zero).mp (mem_consSet.mp hz)
        refine mem_satSet.mpr ?_
        rw [hfr]
        linarith
      have hstay : ∀ i, 1 ≤ i → i ≤ 2 → ∀ a ∈ A i,
          1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob (· ∈ A i) := by
        intro i h1 h2 a ha
        rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
        · rw [hA1] at ha ⊢
          have hstep : max ((7 / 8 : ℝ) * (512 * log n)) (512 * log n) ≤ 512 * log n :=
            max_le (by linarith) le_rfl
          exact le_trans (sat_move hL hβ0 hβn4 ha) (prob_mono_set' _ (satSet_sub n hstep))
        · rw [hA2] at ha ⊢
          rw [cons_absorb ha]
          linarith
      have hmove : ∀ i, 1 ≤ i → i < 2 → ∀ a ∈ A i,
          1 - exp (-(log n / 2)) ≤ (Median.kernel n Bool a).prob (· ∈ A (i + 1)) := by
        intro i h1 h2 a ha
        obtain rfl : i = 1 := by omega
        rw [hA1] at ha
        rw [hA2]
        exact mono_move hL ha
      have hy1 : y ∈ A 1 := by
        rw [hA1]
        exact hy
      have hK := Dynamics.Kernel.nested_phases (Median.kernel n Bool) A (T := 2) (by norm_num) 4
        (ε := 1 / (n : ℝ) ^ 2) (ν := exp (-(log n / 2))) hε (by positivity)
        hnest hstay hmove y hy1
      rw [hA2, exp_half_pow_four hn] at hK
      have e : (4 : ℕ) * 2 = 8 := rfl
      rw [e] at hK
      push_cast at hK
      linarith
    /- (E) round counts, padding and failure budget -/
    -- the quadratic rounds `T₃ = ⌈log (log n / log 2) / log 2⌉₊`
    have hW1 : 1 ≤ log n / log 2 := by
      rw [le_div_iff₀ hl2]
      linarith
    obtain ⟨T3, hT3⟩ : ∃ T3 : ℕ, T3 = ⌈log (log n / log 2) / log 2⌉₊ := ⟨_, rfl⟩
    have hq : (n : ℝ) / 4 * (1 / 2 : ℝ) ^ (2 ^ T3) ≤ 512 * log n := by
      have hJ := hceil hW1 (show (1 : ℝ) < 2 by norm_num)
      rw [← hT3, div_le_iff₀ hl2] at hJ
      have hpow : (n : ℝ) ≤ (2 : ℝ) ^ (2 ^ T3) := by
        rw [← log_le_log_iff hn0 (by positivity), Real.log_pow]
        push_cast
        exact hJ
      have e : (1 / 2 : ℝ) ^ (2 ^ T3) = 1 / (2 : ℝ) ^ (2 ^ T3) := by rw [div_pow, one_pow]
      rw [e]
      have h1 : 1 / (2 : ℝ) ^ (2 ^ T3) ≤ 1 / n := one_div_le_one_div_of_le hn0 hpow
      have h2 : (n : ℝ) / 4 * (1 / (2 : ℝ) ^ (2 ^ T3)) ≤ (n : ℝ) / 4 * (1 / n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : (n : ℝ) / 4 * (1 / n) = 1 / 4 := by field_simp
      linarith
    have hT3b : (T3 : ℝ) ≤ 2 * log (log n) + 3 := by
      have hlogW0 : 0 ≤ log (log n / log 2) := log_nonneg hW1
      have hW2 : log n / log 2 ≤ 2 * log n := by
        rw [div_le_iff₀ hl2]
        have p := mul_le_mul_of_nonneg_left hl2' hL0
        linarith only [p]
      have hlogW : log (log n / log 2) ≤ log 2 + log (log n) := by
        have h := Real.log_le_log (by linarith) hW2
        rwa [Real.log_mul (by norm_num) (by linarith)] at h
      have h1 : ((⌈log (log n / log 2) / log 2⌉₊ : ℕ) : ℝ)
          < log (log n / log 2) / log 2 + 1 :=
        Nat.ceil_lt_add_one (div_nonneg hlogW0 hl2.le)
      have h2 : log (log n / log 2) / log 2 ≤ 2 * log (log n / log 2) := by
        rw [div_le_iff₀ hl2]
        have p := mul_le_mul_of_nonneg_left hl2' hlogW0
        linarith only [p]
      rw [hT3]
      linarith
    intro x Δ hΔ hgap
    have hx : Δ ≤ gapR x := hgap
    -- growth: the gap threshold `(5/4)^i Δ` grows by `5/4` per round until it exceeds `n`
    have hgrowth : ∀ T : ℕ, (n : ℝ) < (5 / 4 : ℝ) ^ T * Δ →
        1 - T * (1 / (n : ℝ) ^ 2)
          ≤ (Median.kernel n Bool).event (· ∈ satSet n ((n : ℝ) / 4)) T x := by
      intro T hT
      have hΔ0 : 0 ≤ Δ := le_trans (by positivity) hΔ
      have hΔ2 : 16384 * (n : ℝ) * log n ≤ Δ ^ 2 := by
        have hnn : 0 ≤ (n : ℝ) * log n := mul_nonneg hn0.le hL0
        have h1 : (128 * √((n : ℝ) * log n)) ^ 2 = 16384 * (n : ℝ) * log n := by
          rw [mul_pow, Real.sq_sqrt hnn]
          ring
        rw [← h1]
        exact pow_le_pow_left₀ (by positivity) hΔ 2
      have hmove : ∀ i, ∀ a ∈ growthSet n ((5 / 4 : ℝ) ^ i * Δ),
          1 - 1 / (n : ℝ) ^ 2 ≤ (Median.kernel n Bool a).prob
            (· ∈ growthSet n ((5 / 4 : ℝ) ^ (i + 1) * Δ)) := by
        intro i a ha
        have hp1 : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ i := one_le_pow₀ (by norm_num)
        have hG0 : 0 ≤ (5 / 4 : ℝ) ^ i * Δ := mul_nonneg (by positivity) hΔ0
        have hG2 : 16384 * (n : ℝ) * log n ≤ ((5 / 4 : ℝ) ^ i * Δ) ^ 2 := by
          have h1 : Δ ≤ (5 / 4 : ℝ) ^ i * Δ := le_mul_of_one_le_left hΔ0 hp1
          exact hΔ2.trans (pow_le_pow_left₀ hΔ0 h1 2)
        have e : (5 / 4 : ℝ) ^ (i + 1) * Δ = 5 / 4 * ((5 / 4 : ℝ) ^ i * Δ) := by ring
        rw [e]
        exact growth_move hL hG0 hG2 ha
      have hx0 : x ∈ growthSet n ((5 / 4 : ℝ) ^ 0 * Δ) := by
        rw [pow_zero, one_mul]
        exact mem_growthSet.mpr (Or.inr hx)
      have hc := hchain hε T (fun i => growthSet n ((5 / 4 : ℝ) ^ i * Δ)) hmove x hx0
      exact le_trans hc (hmono_set (growthSet_sub_satSet n hT) T x)
    have hΔ1 : 1 ≤ Δ := by
      have h1 : (1 : ℝ) ≤ √((n : ℝ) * log n) := by
        refine Real.one_le_sqrt.mpr ?_
        have p := mul_le_mul hn1 hL (by norm_num) hn0.le
        linarith only [p]
      linarith only [h1, hΔ]
    have hΔ0 : 0 < Δ := by linarith only [hΔ1]
    have hΔn : Δ ≤ n := hx.trans (gapR_le x)
    have hw0 : 0 ≤ log (n / Δ) := log_nonneg ((one_le_div hΔ0).mpr hΔn)
    have hwn : log (n / Δ) ≤ log n :=
      Real.log_le_log (div_pos hn0 hΔ0) (div_le_self hn0.le hΔ1)
    have hLL : 1 ≤ log (log n) := by
      have he : exp 1 ≤ log n := by
        have := Real.exp_one_lt_d9
        linarith only [this, hL]
      have h := Real.log_le_log (exp_pos 1) he
      rwa [Real.log_exp] at h
    have hLLn : log (log n) ≤ log n := by
      have := Real.log_le_sub_one_of_pos (show 0 < log n by linarith only [hL])
      linarith only [this]
    -- the growth rounds `T₁ = ⌈log (n/Δ) / log (5/4)⌉₊ + 1`
    obtain ⟨T1, hT1⟩ : ∃ T1 : ℕ, T1 = ⌈log (n / Δ) / log (5 / 4 : ℝ)⌉₊ + 1 := ⟨_, rfl⟩
    have hg : (n : ℝ) < (5 / 4 : ℝ) ^ T1 * Δ := by
      have hw : 1 ≤ (n : ℝ) / Δ := (one_le_div hΔ0).mpr hΔn
      have h1 := hceil hw (show (1 : ℝ) < 5 / 4 by norm_num)
      have h2 : (n : ℝ) ≤ (5 / 4 : ℝ) ^ ⌈log (n / Δ) / log (5 / 4 : ℝ)⌉₊ * Δ := by
        rwa [div_le_iff₀ hΔ0] at h1
      have e : (5 / 4 : ℝ) ^ T1 * Δ
          = 5 / 4 * ((5 / 4 : ℝ) ^ ⌈log (n / Δ) / log (5 / 4 : ℝ)⌉₊ * Δ) := by
        rw [hT1, pow_succ]
        ring
      rw [e]
      linarith only [h2, hn0]
    have hT1b : (T1 : ℝ) ≤ 5 * log (n / Δ) + 2 := by
      have hq := log_five_fourth_ge
      have hlq : 0 < log (5 / 4 : ℝ) := by linarith only [hq]
      have h1 : ((⌈log (n / Δ) / log (5 / 4 : ℝ)⌉₊ : ℕ) : ℝ) < log (n / Δ) / log (5 / 4 : ℝ) + 1 :=
        Nat.ceil_lt_add_one (div_nonneg hw0 hlq.le)
      have h2 : log (n / Δ) / log (5 / 4 : ℝ) ≤ 5 * log (n / Δ) := by
        rw [div_le_iff₀ hlq]
        have p := mul_le_mul_of_nonneg_left hq hw0
        linarith only [p]
      rw [hT1]
      push_cast
      linarith only [h1, h2]
    -- compose the segments
    have h1 := hgrowth T1 hg
    have h2 := hcomp (by positivity) h1 (fun b hb => hlin b hb)
    have h3 := hcomp (by positivity) h2 (fun b hb => hquadseg T3 hq b hb)
    have h4 := hcomp (by positivity) h3 (fun b hb => hcons b hb)
    -- pad to the required number of rounds
    have hle : T1 + 6 + T3 + 8 ≤ ⌈128 * (log (n / Δ) + log (log n))⌉₊ := by
      have hR : ((T1 + 6 + T3 + 8 : ℕ) : ℝ) ≤ 128 * (log (n / Δ) + log (log n)) := by
        push_cast
        linarith only [hT1b, hT3b, hw0, hLL]
      exact Nat.cast_le.mp (le_trans hR (Nat.le_ceil _))
    have habs : ∀ a : Config n Bool, a ∈ consSet →
        (Median.kernel n Bool a).prob (· ∈ consSet) = 1 := fun a ha => cons_absorb ha
    have hpad := event_absorb_mono (K := Median.kernel n Bool)
      (P := fun y => y ∈ consSet) habs (T1 + 6 + T3 + 8) _ x hle
    -- the failure budget `(T₁ + T₃ + 16)/n² ≤ 128/n`
    have hbud : (T1 : ℝ) * (1 / (n : ℝ) ^ 2) + 6 * (1 / (n : ℝ) ^ 2)
        + (T3 : ℝ) * (1 / (n : ℝ) ^ 2) + 10 * (1 / (n : ℝ) ^ 2) ≤ 128 / (n : ℝ) := by
      have hS : (T1 : ℝ) + 6 + T3 + 10 ≤ 128 * n := by
        have := Real.log_le_sub_one_of_pos hn0
        linarith only [this, hT1b, hT3b, hwn, hLLn, hn1]
      have e : (T1 : ℝ) * (1 / (n : ℝ) ^ 2) + 6 * (1 / (n : ℝ) ^ 2)
          + (T3 : ℝ) * (1 / (n : ℝ) ^ 2) + 10 * (1 / (n : ℝ) ^ 2)
          = ((T1 : ℝ) + 6 + T3 + 10) / (n : ℝ) ^ 2 := by ring
      rw [e, div_le_div_iff₀ (by positivity) hn0]
      have p := mul_le_mul_of_nonneg_right hS hn0.le
      linarith only [p]
    have hK : 1 - ((T1 : ℝ) * (1 / (n : ℝ) ^ 2) + 6 * (1 / (n : ℝ) ^ 2)
        + (T3 : ℝ) * (1 / (n : ℝ) ^ 2) + 10 * (1 / (n : ℝ) ^ 2))
        ≤ (Median.kernel n Bool).event (fun y => y = (fun _ => true))
          ⌈128 * (log (n / Δ) + log (log n))⌉₊ x := by
      have h4' : 1 - ((T1 : ℝ) * (1 / (n : ℝ) ^ 2) + 6 * (1 / (n : ℝ) ^ 2)
          + (T3 : ℝ) * (1 / (n : ℝ) ^ 2) + 10 * (1 / (n : ℝ) ^ 2))
          ≤ (Median.kernel n Bool).event (fun y => y ∈ consSet) (T1 + 6 + T3 + 8) x := h4
      exact le_trans h4' hpad
    rw [← kernel_event_true]
    linarith only [hK, hbud]

variable {α : Type*} [LinearOrder α]

/-- **Consensus on a value with a margin on both sides.** If the nodes holding values `≥ v`
outnumber those holding values `< v`, and those holding values `≤ v` outnumber those holding
values `> v`, both by at least `Δ ≥ C √(n log n)`, then all nodes hold `v` after
`⌈C (log (n/Δ) + log log n)⌉` rounds with probability at least `1 - 2C/n`. -/
theorem median_consensus_fast : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n α) (v : α) (Δ : ℝ), C * √(n * Real.log n) ≤ Δ →
      Δ ≤ ((univ.filter fun u => v ≤ x u).card : ℝ) - (univ.filter fun u => x u < v).card →
      Δ ≤ ((univ.filter fun u => x u ≤ v).card : ℝ) - (univ.filter fun u => v < x u).card →
      1 - 2 * C / n ≤ expList (Round n) ⌈C * (Real.log (n / Δ) + Real.log (Real.log n))⌉₊
        (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) := by
  -- Reduction to two values: `u ↦ decide (v ≤ x u)` (monotone, `threshold_run`) and
  -- `u ↦ decide (x u ≤ v)` (antitone: the median of three commutes with antitone maps to `Bool`)
  -- both run as 2-Choices with gap at least `Δ`; when both reach all-`true`, all nodes hold `v`.
  obtain ⟨C, hC, hbin⟩ := binary_consensus_fast
  refine ⟨C, hC, ?_⟩
  intro n _ hL x v Δ hΔ h₁ h₂
  -- an antitone map to `Bool` commutes with the median rule
  have hmed_anti : ∀ {f : α → Bool}, Antitone f → ∀ a b c : α,
      f (med3 a b c) = med3 (f a) (f b) (f c) := by
    intro f hf a b c
    simp only [med3, hf.map_max, hf.map_min]
    generalize f a = p
    generalize f b = q
    generalize f c = r
    cases p <;> cases q <;> cases r <;> decide
  have hrun_anti : ∀ {f : α → Bool}, Antitone f → ∀ (y : Config n α) (l : List (Round n)),
      (fun u => f (run y l u)) = run (fun u => f (y u)) l := by
    intro f hf y l
    induction l generalizing y with
    | nil => rfl
    | cons r l ih =>
      show (fun u => f (run (step y r) l u)) = run (step (fun u => f (y u)) r) l
      have hs : (fun u => f (step y r u)) = step (fun u => f (y u)) r :=
        funext fun u => hmed_anti hf (y u) (y (r u).1) (y (r u).2)
      rw [ih (step y r), hs]
  have hanti : Antitone fun a : α => decide (a ≤ v) := by
    intro a b hab
    by_cases h : b ≤ v
    · simp [h, hab.trans h]
    · simp [h]
  -- the gaps of the two thresholds
  have hsplit : ∀ (p : Fin n → Prop) [DecidablePred p],
      ((univ.filter p).card : ℝ) + ((univ.filter fun u => ¬ p u).card : ℝ) = n := by
    intro p _
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) p
    rw [card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have hgap_up : Δ ≤ (ones (fun u => decide (v ≤ x u)) : ℝ)
      - (n - ones (fun u => decide (v ≤ x u))) := by
    have hones : ones (fun u => decide (v ≤ x u)) = (univ.filter fun u => v ≤ x u).card := by
      simp [ones]
    have hs := hsplit (fun u => v ≤ x u)
    have hneg : (univ.filter fun u => ¬ v ≤ x u) = univ.filter fun u => x u < v := by
      simp only [not_le]
    rw [hneg] at hs
    rw [hones]
    linarith
  have hgap_lo : Δ ≤ (ones (fun u => decide (x u ≤ v)) : ℝ)
      - (n - ones (fun u => decide (x u ≤ v))) := by
    have hones : ones (fun u => decide (x u ≤ v)) = (univ.filter fun u => x u ≤ v).card := by
      simp [ones]
    have hs := hsplit (fun u => x u ≤ v)
    have hneg : (univ.filter fun u => ¬ x u ≤ v) = univ.filter fun u => v < x u := by
      simp only [not_le]
    rw [hneg] at hs
    rw [hones]
    linarith
  have hup := hbin n hL (fun u => decide (v ≤ x u)) Δ hΔ hgap_up
  have hlo := hbin n hL (fun u => decide (x u ≤ v)) Δ hΔ hgap_lo
  -- both thresholds all-`true` means consensus on `v`
  have hpt : ∀ l : List (Round n),
      (if run (fun u => decide (v ≤ x u)) l = (fun _ => true) then (1 : ℝ) else 0)
        + (if run (fun u => decide (x u ≤ v)) l = (fun _ => true) then (1 : ℝ) else 0)
      ≤ (if run x l = (fun _ => v) then (1 : ℝ) else 0) + 1 := by
    intro l
    by_cases hp : run (fun u => decide (v ≤ x u)) l = (fun _ => true)
    · by_cases hm : run (fun u => decide (x u ≤ v)) l = (fun _ => true)
      · have hx : run x l = (fun _ => v) := by
          funext u
          have e1 := congrFun (threshold_run v x l) u
          have e2 := congrFun (hrun_anti hanti x l) u
          rw [hp] at e1
          rw [hm] at e2
          simp only [decide_eq_true_eq] at e1 e2
          exact le_antisymm e2 e1
        rw [if_pos hp, if_pos hm, if_pos hx]
      · rw [if_neg hm]
        split_ifs <;> norm_num
    · rw [if_neg hp]
      split_ifs <;> norm_num
  have hE := expList_le_expList (α := Round n) (T := ⌈C * (Real.log (n / Δ)
    + Real.log (Real.log n))⌉₊) hpt
  rw [expList_add, expList_add, expList_const] at hE
  have e : 2 * C / (n : ℝ) = C / n + C / n := by ring
  rw [e]
  have := le_trans (add_le_add hup hlo) hE
  linarith

/-- **An odd number of equally supported values: the middle one wins fast.** If the nodes hold
`2k+1` distinct values, each held by `n/(2k+1)` nodes, and `C (2k+1) √(n log n) ≤ n`, then the
middle value `v` (exactly `k` values below it) is held by all nodes after
`⌈C (log (2k+1) + log log n)⌉` rounds with probability at least `1 - C/n`. -/
theorem odd_split_consensus : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (x : Config n α) (k : ℕ), (univ.image x).card = 2 * k + 1 →
      (∀ a ∈ univ.image x, ((univ.filter fun u => x u = a).card : ℝ) = n / (2 * k + 1)) →
      C * (2 * k + 1) * √(n * Real.log n) ≤ n →
      ∀ v ∈ univ.image x, ((univ.image x).filter (· < v)).card = k →
        1 - C / n ≤ expList (Round n) ⌈C * (Real.log (2 * k + 1) + Real.log (Real.log n))⌉₊
          (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) := by
  -- Both margins around `v` equal `n/(2k+1)` (counting fiber by fiber over the image), so this is
  -- `median_consensus_fast` with `Δ = n/(2k+1)` (then `log (n/Δ) = log (2k+1)`) and `C' = 2C`;
  -- the extra rounds are harmless because consensus is absorbing.
  obtain ⟨C, hC, hmed⟩ := median_consensus_fast (α := α)
  refine ⟨2 * C, by positivity, ?_⟩
  intro n _ hL x k _hk hc hsize v hv hlt
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hL' : C ≤ Real.log n := by linarith
  have hk0 : (0 : ℝ) < 2 * k + 1 := by positivity
  -- counting: nodes with a value satisfying `P` number `#{values with P} · n/(2k+1)`
  have hfib : ∀ (P : α → Prop) [DecidablePred P], ((univ.filter fun u => P (x u)).card : ℝ)
      = ((univ.image x).filter P).card * (n / (2 * k + 1)) := by
    intro P _
    have h : (univ.filter fun u => P (x u)).card
        = ∑ b ∈ (univ.image x).filter P, (univ.filter fun u => x u = b).card := by
      rw [card_eq_sum_card_fiberwise (f := x) (t := (univ.image x).filter P)]
      · refine sum_congr rfl fun b hb => ?_
        have hPb : P b := (mem_filter.mp hb).2
        congr 1
        ext u
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨h ▸ hPb, h⟩
      · intro u hu
        have hPu : P (x u) := (mem_filter.mp hu).2
        exact mem_filter.mpr ⟨mem_image_of_mem x (mem_univ u), hPu⟩
    rw [h, Nat.cast_sum, sum_congr rfl fun b hb => hc b (mem_filter.mp hb).1, sum_const,
      nsmul_eq_mul]
  -- `k` values below `v`, and `v` itself
  have hle_card : ((univ.image x).filter (· ≤ v)).card = k + 1 := by
    have hins : (univ.image x).filter (· ≤ v) = insert v ((univ.image x).filter (· < v)) := by
      ext a
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨ha, hle⟩
        rcases hle.lt_or_eq with h | h
        · exact Or.inr ⟨ha, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨ha, h⟩)
        · exact ⟨hv, le_rfl⟩
        · exact ⟨ha, h.le⟩
    have hnot : v ∉ (univ.image x).filter (· < v) := by simp
    rw [hins, card_insert_of_notMem hnot, hlt]
  have hsplit : ∀ (p : Fin n → Prop) [DecidablePred p],
      ((univ.filter p).card : ℝ) + ((univ.filter fun u => ¬ p u).card : ℝ) = n := by
    intro p _
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) p
    rw [card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have hlt' := hfib (· < v)
  have hle' := hfib (· ≤ v)
  rw [hlt] at hlt'
  rw [hle_card] at hle'
  have hs1 := hsplit (fun u => x u < v)
  have hs2 := hsplit (fun u => x u ≤ v)
  have hneg1 : (univ.filter fun u => ¬ x u < v) = univ.filter fun u => v ≤ x u := by
    simp only [not_lt]
  have hneg2 : (univ.filter fun u => ¬ x u ≤ v) = univ.filter fun u => v < x u := by
    simp only [not_le]
  rw [hneg1] at hs1
  rw [hneg2] at hs2
  have hn : (n : ℝ) = (2 * k + 1) * (n / (2 * k + 1)) := by field_simp
  push_cast at hlt' hle'
  have m₁ : (n : ℝ) / (2 * k + 1)
      ≤ ((univ.filter fun u => v ≤ x u).card : ℝ) - (univ.filter fun u => x u < v).card := by
    linarith
  have m₂ : (n : ℝ) / (2 * k + 1)
      ≤ ((univ.filter fun u => x u ≤ v).card : ℝ) - (univ.filter fun u => v < x u).card := by
    linarith
  -- the margin is large enough
  have hΔ : C * √(n * Real.log n) ≤ n / (2 * k + 1) := by
    rw [le_div_iff₀ hk0]
    have hs := mul_nonneg hC.le (mul_nonneg hk0.le (Real.sqrt_nonneg ((n : ℝ) * Real.log n)))
    linarith only [hs, hsize]
  have h := hmed n hL' x v (n / (2 * k + 1)) hΔ m₁ m₂
  have hlog : Real.log (n / (n / (2 * k + 1))) = Real.log (2 * k + 1) := by
    congr 1
    field_simp
  rw [hlog] at h
  -- padding: the probability of consensus on `v` is nondecreasing in the number of rounds
  have hstep : ∀ T : ℕ,
      expList (Round n) T (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0)
        ≤ expList (Round n) (T + 1) (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) := by
    intro T
    rw [expList_append T 1]
    apply expList_le_expList
    intro l
    rw [expList_succ]
    simp only [expList_zero]
    by_cases hl : run x l = (fun _ => v)
    · have hcons : ∀ r : Round n, run x (l ++ [r]) = (fun _ => v) := by
        intro r
        have e : run x (l ++ [r]) = step (run x l) r := by
          simp [run, List.foldl_append]
        rw [e, hl]
        exact step_of_consensus _ ⟨v, fun _ => rfl⟩ r
      have hf : (fun r : Round n => if run x (l ++ [r]) = (fun _ => v) then (1 : ℝ) else 0)
          = fun _ => 1 := funext fun r => if_pos (hcons r)
      rw [if_pos hl, hf, avg_const]
    · rw [if_neg hl]
      exact avg_nonneg fun r => by split_ifs <;> norm_num
  have hmono : Monotone fun T : ℕ =>
      expList (Round n) T (fun l => if run x l = (fun _ => v) then (1 : ℝ) else 0) :=
    monotone_nat_of_le_succ hstep
  have hT : ⌈C * (Real.log (2 * k + 1) + Real.log (Real.log n))⌉₊
      ≤ ⌈2 * C * (Real.log (2 * k + 1) + Real.log (Real.log n))⌉₊ := by
    by_cases hy : 0 ≤ Real.log (2 * k + 1) + Real.log (Real.log n)
    · apply Nat.ceil_mono
      linarith only [mul_nonneg hC.le hy]
    · rw [Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_lt (not_le.mp hy)))]
      exact Nat.zero_le _
  exact le_trans h (hmono hT)

end Median
