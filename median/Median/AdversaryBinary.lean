import Median.AdversaryMoves

/-! # Adversary: almost stable consensus for two values

The proof of the binary case of `Median/Adversary.lean`, for a run `P` of 2-Choices perturbed by
at most `F ≤ √n/1024` recolourings per round, with `L = log n ≥ 2²⁰` and
`K = max (16 F) (1024 L)`:

* **escape** (`adv_escape`): after `⌈2¹⁹ L⌉` rounds, `|g| ≥ 128 √(nL)` except with probability
  `2/n²` (drift of `gapPot` against the adversary, `avg_gapPot_perturbed`, and Markov's
  inequality);
* **growth and saturation** (`adv_phase2`): from a gap `g ≥ 128 √(nL)`, a chain of moves, each
  failing with probability `n⁻²`: the gap grows by `9/8` per round up to `17n/32` (`⌈9L⌉`
  rounds, `adv_growth_move`), then the minority shrinks by `15/16` per round down to `K`
  (`⌈16L⌉` rounds, `adv_sat_move`), and then stays below `K`, which is almost consensus on
  `true` (a negative gap is handled by the flip symmetry);
* `adv_binary_window`: both phases fit into `⌈2²⁰ L⌉` rounds, followed by a window of `H` rounds,
  with failure probability at most `(2²⁰ L + H)/n²`.
-/

namespace Median
open Finset Real Dynamics

variable {n : ℕ}

/-! ### Scalar facts -/

/-- `log (9/8) ≥ 1/9`. -/
lemma log_nine_eighth_ge : 1 / 9 ≤ log ((9 : ℝ) / 8) := by
  calc (1 : ℝ) / 9 = 1 - (((9 : ℝ) / 8))⁻¹ := by norm_num
    _ ≤ log ((9 : ℝ) / 8) := Real.one_sub_inv_le_log_of_pos (by norm_num)

/-- `log (16/15) ≥ 1/16`. -/
lemma log_sixteen_fifteenth_ge : 1 / 16 ≤ log ((16 : ℝ) / 15) := by
  calc (1 : ℝ) / 16 = 1 - (((16 : ℝ) / 15))⁻¹ := by norm_num
    _ ≤ log ((16 : ℝ) / 15) := Real.one_sub_inv_le_log_of_pos (by norm_num)

/-- If `log x ≤ T log q`, then `x ≤ q ^ T`. -/
lemma le_pow_of_log_le {x q : ℝ} (hx : 0 < x) (hq : 0 < q) {T : ℕ} (h : log x ≤ T * log q) :
    x ≤ q ^ T := by
  rw [← exp_log hx, ← exp_log (pow_pos hq T), log_pow]
  exact exp_le_exp.mpr h

/-- **The error of the escape phase against the adversary.** With `L = log x ≥ 16384` and
`2¹⁹ L ≤ T ≤ 2¹⁹ L + 1`, for `p ≤ 1`:
`e^{√L/2} (e^{-T/131072} p + T e^{1/65536 - √x/512}) ≤ 2/x²`. -/
lemma adv_escape_error_le {x p : ℝ} {T : ℕ} (hx : 0 < x) (hL : 16384 ≤ log x)
    (hT1 : 524288 * log x ≤ T) (hT2 : (T : ℝ) ≤ 524288 * log x + 1) (hp1 : p ≤ 1) :
    exp (√(log x) / 2) * (exp (-(1 / 131072)) ^ T * p + T * exp (1 / 65536 - √x / 512))
      ≤ 2 / x ^ 2 := by
  have hx4 := log_pow_four_div_le hx (by linarith)
  have hexp : exp (log x) = x := exp_log hx
  obtain ⟨L, hLdef⟩ : ∃ L, L = log x := ⟨_, rfl⟩
  rw [← hLdef] at hL hT1 hT2 hx4 hexp ⊢
  have hL0 : 0 ≤ L := by linarith
  have hL3 : 16384 ^ 3 * L ≤ L ^ 4 := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hL 3) hL0
    linarith
  have hTx : (T : ℝ) ≤ x := by linarith
  have hsL : √L / 2 ≤ L := by
    have := mul_le_mul_of_nonneg_left (one_le_sqrt.mpr (by linarith : (1 : ℝ) ≤ L))
      (sqrt_nonneg L)
    linarith [mul_self_sqrt hL0]
  have hsx : L ^ 2 / 5 ≤ √x := le_sqrt_of_sq_le (by linarith [sq_nonneg (L ^ 2)])
  have hLL : 16384 * L ≤ L ^ 2 := by nlinarith
  -- the contraction term: `e^{√L/2} e^{-T/131072} p ≤ e^{-2L} = 1/x²`
  have hA : exp (√L / 2) * (exp (-(1 / 131072)) ^ T * p) ≤ 1 / x ^ 2 := by
    rw [← exp_nat_mul]
    calc exp (√L / 2) * (exp (T * -(1 / 131072)) * p)
        ≤ exp (√L / 2) * exp (T * -(1 / 131072)) :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (exp_pos _).le hp1) (exp_pos _).le
      _ = exp (√L / 2 + T * -(1 / 131072)) := (exp_add _ _).symm
      _ ≤ exp (-((2 : ℕ) * L)) := exp_le_exp.mpr (by push_cast; linarith)
      _ = 1 / x ^ 2 := by rw [exp_neg, exp_nat_mul, hexp, one_div]
  -- the error term: `e^{√L/2} ≤ x`, `T ≤ x` and `e^{1/65536 - √x/512} ≤ e^{-4L} = 1/x⁴`
  have hB : exp (√L / 2) * (T * exp (1 / 65536 - √x / 512)) ≤ 1 / x ^ 2 := by
    have he1 : exp (√L / 2) ≤ x := hexp ▸ exp_le_exp.mpr hsL
    have he4 : exp (1 / 65536 - √x / 512) ≤ 1 / x ^ 4 := by
      calc exp (1 / 65536 - √x / 512) ≤ exp (-((4 : ℕ) * L)) :=
            exp_le_exp.mpr (by push_cast; nlinarith)
        _ = 1 / x ^ 4 := by rw [exp_neg, exp_nat_mul, hexp, one_div]
    calc exp (√L / 2) * (T * exp (1 / 65536 - √x / 512))
        ≤ x * (x * (1 / x ^ 4)) :=
          mul_le_mul he1 (mul_le_mul hTx he4 (exp_pos _).le hx.le) (by positivity) hx.le
      _ = 1 / x ^ 2 := by field_simp
  rw [mul_add]
  calc _ ≤ 1 / x ^ 2 + 1 / x ^ 2 := add_le_add hA hB
    _ = 2 / x ^ 2 := by ring

variable [NeZero n]

/-! ### Escape from balance -/

/-- **Escape from balance against the adversary.** For `log n ≥ 16384` and `F ≤ √n/1024`,
after `⌈2¹⁹ log n⌉` rounds of a perturbed run the gap is at least `128 √(n log n)` in absolute
value, except with probability at most `2/n²`. -/
theorem adv_escape (hL : (16384 : ℝ) ≤ log n) {F : ℕ} (hF : 1024 * (F : ℝ) ≤ √(n : ℝ))
    {x : Config n Bool} {P : List (Round n) → Config n Bool} (hP : IsAdvRun F x P) :
    expList (Round n) ⌈524288 * log n⌉₊
        (fun l => failInd (128 * √((n : ℝ) * log n) ≤ |gapR (P l)|)) ≤ 2 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hn10 : (10 : ℝ) ≤ n := by linarith [add_one_le_exp (log n), exp_log hn0]
  obtain ⟨T, hT⟩ : ∃ T, T = ⌈524288 * log n⌉₊ := ⟨_, rfl⟩
  rw [← hT]
  -- Markov: below the threshold, the potential is at least `e^{-√(log n)/2}`
  have hind (y : Config n Bool) :
      failInd (128 * √((n : ℝ) * log n) ≤ |gapR y|) ≤ exp (√(log n) / 2) * gapPot y := by
    by_cases h : 128 * √((n : ℝ) * log n) ≤ |gapR y|
    · rw [failInd_of h]
      exact mul_nonneg (exp_pos _).le (gapPot_pos y).le
    · rw [failInd_of_not h]
      push Not at h
      calc (1 : ℝ) = exp (√(log n) / 2) * exp (-(√(log n) / 2)) := by
            rw [← exp_add]
            simp
        _ ≤ exp (√(log n) / 2) * gapPot y := by
            refine mul_le_mul_of_nonneg_left (exp_neg_le_gapPot ?_) (exp_pos _).le
            rw [sqrt_mul hn0.le] at h
            linarith
  have hdrift := expList_le_of_drift_perturbed step (fun z z' => hammingDist z' z ≤ F) gapPot
    (exp_pos _).le (exp_le_one_iff.mpr (by norm_num)) (exp_pos _).le
    (fun s g hg => avg_gapPot_perturbed hn10 hF s g hg) T x P hP.perturbed
  have hT1 : 524288 * log n ≤ T := by
    rw [hT]
    exact Nat.le_ceil _
  have hT2 : (T : ℝ) ≤ 524288 * log n + 1 := by
    rw [hT]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  calc expList (Round n) T (fun l => failInd (128 * √((n : ℝ) * log n) ≤ |gapR (P l)|))
      ≤ expList (Round n) T (fun l => exp (√(log n) / 2) * gapPot (P l)) :=
        expList_le_expList fun l => hind _
    _ = exp (√(log n) / 2) * expList (Round n) T (fun l => gapPot (P l)) :=
        expList_const_mul _ _ _
    _ ≤ exp (√(log n) / 2)
          * (exp (-(1 / 131072)) ^ T * gapPot x + T * exp (1 / 65536 - √(n : ℝ) / 512)) :=
        mul_le_mul_of_nonneg_left hdrift (exp_pos _).le
    _ ≤ 2 / (n : ℝ) ^ 2 := adv_escape_error_le hn0 hL hT1 hT2 (gapPot_le_one x)

/-! ### Growth and saturation -/

/-- The gap thresholds of the growth phase: `min ((9/8)^i G₀) (17n/32)`. -/
noncomputable def growthThr (n : ℕ) (G₀ : ℝ) (i : ℕ) : ℝ :=
  min ((9 / 8 : ℝ) ^ i * G₀) (17 * (n : ℝ) / 32)

/-- The minority thresholds of the saturation phase: `max ((15/16)^j n/4) K`. -/
noncomputable def satThr (n : ℕ) (K : ℝ) (j : ℕ) : ℝ := max ((15 / 16 : ℝ) ^ j * ((n : ℝ) / 4)) K

/-- The sets of the chain of moves: `Tg` growth sets, then saturation sets. -/
def advChain (n : ℕ) (G₀ K : ℝ) (Tg : ℕ) (i : ℕ) : Set (Config n Bool) :=
  if i < Tg then {y | growthThr n G₀ i ≤ gapR y} else {y | falsesR y < satThr n K (i - Tg)}

/-- **Growth and saturation against the adversary.** For `log n ≥ 128` and `F ≤ √n/1024`, a
perturbed run from a gap at least `128 √(n log n)` holds all but at most
`K = max (16 F) (1024 log n)` nodes at `true` at every time from `T₁` to `T₁ + H`, for any
`T₁ ≥ ⌈9 log n⌉ + ⌈16 log n⌉`, except with probability at most `(T₁ + H)/n²`. -/
theorem adv_phase2 (hL : (128 : ℝ) ≤ log n) {F : ℕ} (hF : 1024 * (F : ℝ) ≤ √(n : ℝ))
    {y : Config n Bool} (hy : 128 * √((n : ℝ) * log n) ≤ gapR y)
    {Q : List (Round n) → Config n Bool} (hQ : IsAdvRun F y Q) {T₁ : ℕ} (H : ℕ)
    (hT₁ : ⌈9 * log n⌉₊ + ⌈16 * log n⌉₊ ≤ T₁) :
    expList (Round n) (T₁ + H)
        (notAlmostStable (max (16 * (F : ℝ)) (1024 * log n)) T₁ H Q)
      ≤ (T₁ + H : ℕ) / (n : ℝ) ^ 2 := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ log n := by linarith
  have hbig := big_log_le hL
  have hs := sqrt_cast_pos (n := n)
  have hsn : √(n : ℝ) ≤ (n : ℝ) / 16 := by
    rw [sqrt_le_left (by positivity)]
    nlinarith
  obtain ⟨G₀, hG₀⟩ : ∃ G₀, G₀ = 128 * √((n : ℝ) * log n) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = max (16 * (F : ℝ)) (1024 * log n) := ⟨_, rfl⟩
  rw [← hG₀] at hy
  rw [← hK]
  obtain ⟨Tg, hTg⟩ : ∃ Tg, Tg = ⌈9 * log n⌉₊ := ⟨_, rfl⟩
  obtain ⟨Ts, hTs⟩ : ∃ Ts, Ts = ⌈16 * log n⌉₊ := ⟨_, rfl⟩
  rw [← hTg, ← hTs] at hT₁
  -- scalar facts
  have hG₀1 : 1 ≤ G₀ := by
    rw [hG₀]
    have : (1 : ℝ) ≤ √((n : ℝ) * log n) :=
      one_le_sqrt.mpr (by nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn])
    linarith
  have hG₀n : G₀ ≤ 17 * (n : ℝ) / 32 := by
    rw [hG₀]
    have : √((n : ℝ) * log n) ≤ 17 * (n : ℝ) / 4096 := by
      rw [sqrt_le_left (by positivity)]
      nlinarith
    linarith
  have hK16 : 16 * (F : ℝ) ≤ K := hK ▸ le_max_left _ _
  have hKL : 1024 * log n ≤ K := hK ▸ le_max_right _ _
  have hKn : K ≤ (n : ℝ) / 4 := by
    rw [hK]
    exact max_le (by nlinarith) (by linarith)
  have hTg1 : 1 ≤ Tg := by
    rw [hTg]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- `(9/8)^Tg ≥ n` and `(16/15)^Ts ≥ n`
  have hpowg : (n : ℝ) ≤ (9 / 8 : ℝ) ^ Tg := by
    refine le_pow_of_log_le hn0 (by norm_num) ?_
    have h1 : 9 * log n ≤ (Tg : ℝ) := hTg ▸ Nat.le_ceil _
    nlinarith [log_nine_eighth_ge]
  have hpows : (n : ℝ) ≤ (16 / 15 : ℝ) ^ Ts := by
    refine le_pow_of_log_le hn0 (by norm_num) ?_
    have h1 : 16 * log n ≤ (Ts : ℝ) := hTs ▸ Nat.le_ceil _
    nlinarith [log_sixteen_fifteenth_ge]
  -- the thresholds
  have hgr_ge (i : ℕ) : G₀ ≤ growthThr n G₀ i :=
    le_min (le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))) hG₀n
  have hgr_le (i : ℕ) : growthThr n G₀ i ≤ 17 * (n : ℝ) / 32 := min_le_right _ _
  have hgr_step (i : ℕ) :
      growthThr n G₀ (i + 1) ≤ min (9 / 8 * growthThr n G₀ i) (17 * (n : ℝ) / 32) := by
    refine le_min ?_ (min_le_right _ _)
    unfold growthThr
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 9 / 8), pow_succ']
    refine min_le_min (le_of_eq (by ring)) (by linarith)
  have hsat_ge (j : ℕ) : K ≤ satThr n K j := le_max_right _ _
  have hsat_le (j : ℕ) : satThr n K j ≤ (n : ℝ) / 4 :=
    max_le (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))) hKn
  have hsat_step (j : ℕ) : max (15 / 16 * satThr n K j) K ≤ satThr n K (j + 1) := by
    unfold satThr
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 15 / 16), pow_succ']
    refine max_le (max_le (le_max_of_le_left (le_of_eq (by ring)))
      (le_max_of_le_right (by linarith))) (le_max_right _ _)
  have hsat_end (j : ℕ) (hj : Ts ≤ j) : satThr n K j = K := by
    refine max_eq_right ?_
    have h1 : (15 / 16 : ℝ) ^ j ≤ (15 / 16 : ℝ) ^ Ts :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have h2 : (15 / 16 : ℝ) ^ Ts * (16 / 15 : ℝ) ^ Ts = 1 := by
      rw [← mul_pow]; norm_num
    have h3 : (15 / 16 : ℝ) ^ Ts * n ≤ 1 := by
      calc (15 / 16 : ℝ) ^ Ts * n ≤ (15 / 16 : ℝ) ^ Ts * (16 / 15 : ℝ) ^ Ts :=
            mul_le_mul_of_nonneg_left hpows (by positivity)
        _ = 1 := h2
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 15 / 16 by norm_num) j]
  -- the moves
  have hgap : ∀ z : Config n Bool, gapR z = (n : ℝ) - 2 * falsesR z := fun z => by
    have h1 := falses_plus_ones z
    have h2 := gapR_eq z
    linarith
  have hB : ∀ i, ∀ s ∈ advChain n G₀ K Tg i, ∀ g : Round n → Config n Bool,
      (∀ r, (fun z z' => hammingDist z' z ≤ F) (step s r) (g r)) →
      avg (fun r => failInd (g r ∈ advChain n G₀ K Tg (i + 1))) ≤ 1 / (n : ℝ) ^ 2 := by
    intro i s hs g hg
    by_cases hi : i < Tg
    · simp only [advChain, hi, if_true, Set.mem_setOf_eq] at hs
      have hmove := adv_growth_move hL hF (hG₀ ▸ hgr_ge i) (hgr_le i) hs g hg
      refine le_trans (avg_le_avg fun r => failInd_mono fun h => ?_) hmove
      by_cases hi1 : i + 1 < Tg
      · simp only [advChain, hi1, if_true, Set.mem_setOf_eq]
        exact le_trans (hgr_step i) h
      · have hi1' : i + 1 = Tg := by omega
        rw [hi1']
        simp only [advChain, lt_irrefl, if_false, Set.mem_setOf_eq, Nat.sub_self]
        -- at the end of the growth phase the gap is at least `17n/32`
        have hcap : 17 * (n : ℝ) / 32 ≤ 9 / 8 * growthThr n G₀ i := by
          unfold growthThr
          rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 9 / 8)]
          refine le_min ?_ (by linarith)
          rw [← mul_assoc, ← pow_succ', hi1']
          nlinarith
        rw [min_eq_right hcap] at h
        have := le_max_left ((15 / 16 : ℝ) ^ 0 * ((n : ℝ) / 4)) K
        unfold satThr
        rw [hgap] at h
        simp only [pow_zero, one_mul] at this ⊢
        linarith
    · simp only [advChain, hi, if_false, Set.mem_setOf_eq] at hs
      have hmove := adv_sat_move hL (hK ▸ hsat_ge (i - Tg)) (hsat_le (i - Tg)) hs g hg
      rw [← hK] at hmove
      refine le_trans (avg_le_avg fun r => failInd_mono fun h => ?_) hmove
      have hi1 : ¬ i + 1 < Tg := by omega
      simp only [advChain, hi1, if_false, Set.mem_setOf_eq]
      rw [show i + 1 - Tg = i - Tg + 1 by omega]
      exact lt_of_lt_of_le h (hsat_step _)
  have hy0 : y ∈ advChain n G₀ K Tg 0 := by
    simp only [advChain, show 0 < Tg by omega, if_true, Set.mem_setOf_eq]
    exact le_trans (min_le_left _ _) (by simpa using hy)
  have hpath := expList_path_perturbed step (fun z z' => hammingDist z' z ≤ F)
    (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2) (T₁ + H) (advChain n G₀ K Tg) hB y Q
    hQ.perturbed hy0
  refine le_trans (expList_le_expList fun l => ?_) (hpath.trans_eq (by ring))
  rw [notAlmostStable_eq]
  refine failInd_mono fun h => ⟨true, fun t ht1 ht2 => ?_⟩
  have hmem := h t ht2
  have htg : ¬ t < Tg := by omega
  simp only [advChain, htg, if_false, Set.mem_setOf_eq] at hmem
  rw [hsat_end _ (by omega)] at hmem
  unfold AlmostConsensus
  rw [card_ne_true]
  exact hmem.le

end Median
