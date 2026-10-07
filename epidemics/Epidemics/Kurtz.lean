import Epidemics.KurtzBound

/-! # Kurtz's law of large numbers for SIR, in discrete time (CRN-2)

For the uniformized SIR chain of `Epidemics.KurtzDefs` (`N` agents, infection weight `β`, recovery
weight `γ`, one step per unit `1 / ((β + γ) N)` of time), the scaled counts `(S, I, R) / N` stay,
with probability exponentially close to one in `N`, uniformly close on a finite horizon `[0, T]`
to the solution of the Kermack–McKendrick system of EPI-7 (`sirField β γ`), in the form of the
differential-equation method of N. Wormald (*The differential equation method for random graph
processes and greedy algorithms*, 1999, Theorem 5.1) and of T. G. Kurtz's law of large numbers
for density-dependent Markov chains (*Solutions of ordinary differential equations as limits of
pure jump Markov processes*, J. Appl. Probab. 7, 1970).

* `law_of_large_numbers`: constants `C, c, L` depending only on `β, γ, T` such that, for every
  `N`, every initial configuration `x₀`, every solution `(s, i, r)` on `[0, ∞)` started in the
  simplex and every `ε > 0`, the chain stays within `L · dist (scaled x₀) (s 0, i 0, r 0) + ε` of
  `(s, i, r)` at all steps `k ≤ T (β + γ) N`, compared at times `k / ((β + γ) N)`, except with
  probability at most `C exp(-c ε² N)`. When `scaled x₀ = (s 0, i 0, r 0)` (Wormald's choice of
  the initial value), the distance is just `ε`.
* `tendsto_deviationProb`: convergence in probability, uniformly on the horizon, to a fixed
  solution, when the scaled initial configurations converge to its initial point.

The intended proof: the drift identity and bounded increments (`Epidemics.KurtzDrift`) make the
deviation of the scaled counts from their compensator a martingale with increments `O(1 / N)`,
controlled by the maximal Azuma–Hoeffding inequality `expList_azuma`; on the good event, the
discrete Grönwall inequality (Mathlib's `discrete_gronwall`) bounds the distance to the solution,
the Euler discretization error being `O(1 / N)`.
-/

namespace Epidemics.Kurtz

open Dynamics KermackMcKendrick Filter Topology Finset Real

/-- **Kurtz's law of large numbers for SIR, in discrete time, with an exponential bound** (Wormald
1999, Theorem 5.1; Kurtz 1970). Let `β, γ > 0` and `T > 0`. There are constants `C, c > 0` and `L`
such that for every number of agents `N > 0`, every initial configuration `x₀`, every solution
`(s, i, r)` of the Kermack–McKendrick system `s' = -β s i`, `i' = β s i - γ i`, `r' = γ i` on
`[0, ∞)` whose initial point lies in the simplex, and every `ε > 0`: with probability at least
`1 - C exp(-c ε² N)`, at every step `k ≤ T (β + γ) N` the scaled counts of the chain are within
`L · dist (scaled x₀) (s 0, i 0, r 0) + ε` (sup distance) of `(s, i, r)` at time
`k / ((β + γ) N)`. -/
theorem law_of_large_numbers {β γ : ℕ} (hβ : 0 < β) (hγ : 0 < γ) {T : ℝ} (hT : 0 < T) :
    ∃ C c L : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 0 < N → ∀ (x₀ : Config N) (s i r : ℝ → ℝ),
        IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Set.Ici 0) →
        0 ≤ s 0 → 0 ≤ i 0 → 0 ≤ r 0 → s 0 + i 0 + r 0 = 1 →
        ∀ ε : ℝ, 0 < ε →
          deviationProb β γ x₀ (fun t ↦ (s t, i t, r t))
              (L * dist (scaled x₀) (s 0, i 0, r 0) + ε) ⌊T * (β + γ) * N⌋₊
            ≤ C * Real.exp (-(c * ε ^ 2 * N)) := by
  have hβ' : (0 : ℝ) < β := by exact_mod_cast hβ
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hB : (0 : ℝ) < β + γ := by positivity
  obtain ⟨Lip, hLipdef⟩ : ∃ Lip : ℝ, Lip = 2 * β + γ := ⟨_, rfl⟩
  have hLip : 0 < Lip := by rw [hLipdef]; positivity
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = exp (Lip * T) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; exact one_le_exp (by positivity)
  have hL : 0 < L := by linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (32 * L ^ 2 * T * (β + γ)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℝ, A₀ = 4 * c * L * T * Lip := ⟨_, rfl⟩
  have hA₀ : 0 ≤ A₀ := by rw [hA₀def]; positivity
  refine ⟨6 * exp A₀, c, L, by positivity, hc, ?_⟩
  intro N hN x₀ s i r hx hs hi hr hsum ε hε
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  haveI := round_nonempty (γ := γ) hN hβ
  obtain ⟨n, hn⟩ : ∃ n, n = ⌊T * (β + γ) * N⌋₊ := ⟨_, rfl⟩
  rw [← hn]
  have hnT : (n : ℝ) ≤ T * (β + γ) * N := by rw [hn]; exact Nat.floor_le (by positivity)
  obtain ⟨e₀, he₀⟩ : ∃ e₀, e₀ = dist (scaled x₀) (s 0, i 0, r 0) := ⟨_, rfl⟩
  rw [← he₀]
  have he₀0 : 0 ≤ e₀ := he₀ ▸ dist_nonneg
  have hball (t : ℝ) (ht : 0 ≤ t) : ‖(s t, i t, r t)‖ ≤ 1 :=
    sir_norm_le_one hx hγ' hs hi hr hsum ht
  have hRHS0 : 0 ≤ 6 * exp A₀ * exp (-(c * ε ^ 2 * N)) := by positivity
  have hle1 : deviationProb β γ x₀ (fun t ↦ (s t, i t, r t)) (L * e₀ + ε) n ≤ 1 :=
    expList_le_one fun l ↦ by split_ifs <;> norm_num
  -- an event that never happens has probability zero
  have hzero : (∀ l : List (Round N β γ), ¬ ∃ k ≤ n, L * e₀ + ε < dist
      (scaled ((l.take k).foldl (step β γ) x₀))
      (s (k / ((β + γ) * N)), i (k / ((β + γ) * N)), r (k / ((β + γ) * N)))) →
      deviationProb β γ x₀ (fun t ↦ (s t, i t, r t)) (L * e₀ + ε) n = 0 := by
    intro hnone
    unfold deviationProb
    have hz : (fun l : List (Round N β γ) ↦ if ∃ k ≤ n, L * e₀ + ε < dist
        (scaled ((l.take k).foldl (step β γ) x₀))
        ((fun t ↦ (s t, i t, r t)) ((k : ℝ) / ((β + γ) * N))) then (1 : ℝ) else 0)
        = fun _ ↦ 0 := funext fun l ↦ if_neg (hnone l)
    rw [hz, expList_zero_fun]
  -- case `ε ≥ 2`: both points lie in the unit ball
  by_cases hε2 : 2 ≤ ε
  · rw [hzero fun l ⟨k, hk, hlt⟩ ↦ by
      have h1 := dist_le_norm_add_norm (scaled ((l.take k).foldl (step β γ) x₀))
        (s (k / ((β + γ) * N)), i (k / ((β + γ) * N)), r (k / ((β + γ) * N)))
      have h2 := norm_scaled_le_one ((l.take k).foldl (step β γ) x₀)
      have h3 := hball (k / ((β + γ) * N)) (by positivity)
      nlinarith [mul_nonneg hL.le he₀0]]
    exact hRHS0
  push Not at hε2
  -- case `ε N < 2 L T Lip`: the bound is at least one
  by_cases hsmall : ε * N < 2 * L * T * Lip
  · refine hle1.trans ?_
    have hcε : c * ε ^ 2 * N ≤ A₀ := by
      have h1 : ε * (ε * N) ≤ 2 * (2 * L * T * Lip) :=
        mul_le_mul hε2.le hsmall.le (by positivity) (by norm_num)
      rw [hA₀def]
      nlinarith
    rw [mul_assoc, ← exp_add]
    have : 1 ≤ exp (A₀ + -(c * ε ^ 2 * N)) := one_le_exp (by linarith)
    linarith
  push Not at hsmall
  -- case `n = 0`: only the initial point is compared
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hzero fun l ⟨k, hk, hlt⟩ ↦ by
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [List.take_zero, List.foldl_nil, CharP.cast_eq_zero, zero_div] at hlt
      rw [← he₀] at hlt
      nlinarith [mul_le_mul_of_nonneg_right hL1 he₀0]]
    exact hRHS0
  -- main case: the martingale level `δ = ε / (2L)`
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (2 * L) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hθ : (e₀ + δ + T * (2 * β + γ) / N) * exp ((2 * β + γ) * T) ≤ L * e₀ + ε := by
    rw [← hLipdef, ← hLdef]
    have hTN : T * Lip / N ≤ ε / (2 * L) := by
      rw [div_le_div_iff₀ hN' (by positivity)]
      nlinarith
    have hδL : δ * L = ε / 2 := by rw [hδdef]; field_simp
    have hTL : T * Lip / N * L ≤ ε / 2 := by
      calc T * Lip / N * L ≤ ε / (2 * L) * L := mul_le_mul_of_nonneg_right hTN hL.le
        _ = ε / 2 := by field_simp
    nlinarith
  rw [he₀] at hθ
  have hmain := deviationProb_le_azuma hβ hγ hN hx hs hi hr hsum hδ.le hnT hθ
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hexp : exp (-(δ ^ 2 / (2 * n * (2 / N) ^ 2))) ≤ exp (-(c * ε ^ 2 * N)) := by
    rw [exp_le_exp, neg_le_neg_iff]
    have e1 : δ ^ 2 / (2 * n * (2 / N) ^ 2) = ε ^ 2 * N ^ 2 / (32 * L ^ 2 * n) := by
      rw [hδdef]
      field_simp
      ring
    have e2 : c * ε ^ 2 * N = ε ^ 2 * N ^ 2 / (32 * L ^ 2 * (T * (β + γ) * N)) := by
      rw [hcdef]
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hnT (by positivity))
  rw [← he₀] at hmain
  calc deviationProb β γ x₀ (fun t ↦ (s t, i t, r t)) (L * e₀ + ε) n
      ≤ 6 * exp (-(δ ^ 2 / (2 * n * (2 / N) ^ 2))) := hmain
    _ ≤ 6 * exp (-(c * ε ^ 2 * N)) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 6 * 1 * exp (-(c * ε ^ 2 * N)) := by rw [mul_one]
    _ ≤ 6 * exp A₀ * exp (-(c * ε ^ 2 * N)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_le_exp hA₀) (by norm_num))
          (exp_pos _).le

/-- **Kurtz's law of large numbers for SIR, in probability, uniformly on `[0, T]`** (Kurtz 1970;
roadmap row CRN-2). Let `(s, i, r)` be a solution on `[0, ∞)` of the Kermack–McKendrick system with
rates `β, γ > 0`, started in the simplex, and let `x₀ N` be configurations of `N` agents whose
scaled counts converge to `(s 0, i 0, r 0)`. Then for every `ε > 0`, the probability that the
chain started at `x₀ N` is farther than `ε` from `(s, i, r)` at some step `k ≤ T (β + γ) N`
(compared at time `k / ((β + γ) N)`) tends to `0` as `N → ∞`. -/
theorem tendsto_deviationProb {β γ : ℕ} (hβ : 0 < β) (hγ : 0 < γ) {T : ℝ} (hT : 0 < T)
    {s i r : ℝ → ℝ}
    (hsol : IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Set.Ici 0))
    (hs : 0 ≤ s 0) (hi : 0 ≤ i 0) (hr : 0 ≤ r 0) (hsum : s 0 + i 0 + r 0 = 1)
    (x₀ : (N : ℕ) → Config N) (hx₀ : Tendsto (fun N ↦ scaled (x₀ N)) atTop (𝓝 (s 0, i 0, r 0)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ ↦ deviationProb β γ (x₀ N) (fun t ↦ (s t, i t, r t)) ε
      ⌊T * (β + γ) * N⌋₊) atTop (𝓝 0) := by
  obtain ⟨C, c, L, hC, hc, hmain⟩ := law_of_large_numbers hβ hγ hT
  -- the initial error is eventually below `η`, with `|L| η ≤ ε / 2`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * (|L| + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hclose : ∀ᶠ N : ℕ in atTop, dist (scaled (x₀ N)) (s 0, i 0, r 0) < η :=
    hx₀.eventually (Metric.ball_mem_nhds _ hη)
  -- the exponential bound tends to `0`
  have hg : Tendsto (fun N : ℕ ↦ C * Real.exp (-(c * (ε / 2) ^ 2 * N))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ c * (ε / 2) ^ 2 * (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    rw [mul_zero] at h2
    exact h2
  refine squeeze_zero' (Eventually.of_forall fun N ↦ deviationProb_nonneg _ _ _ _) ?_ hg
  filter_upwards [hclose, eventually_gt_atTop 0] with N hN hNpos
  have hLd : L * dist (scaled (x₀ N)) (s 0, i 0, r 0) + ε / 2 ≤ ε := by
    have h1 : L * dist (scaled (x₀ N)) (s 0, i 0, r 0)
        ≤ |L| * dist (scaled (x₀ N)) (s 0, i 0, r 0) := by
      exact mul_le_mul_of_nonneg_right (le_abs_self L) dist_nonneg
    have h2 : |L| * dist (scaled (x₀ N)) (s 0, i 0, r 0) ≤ |L| * η :=
      mul_le_mul_of_nonneg_left hN.le (abs_nonneg L)
    have h3 : |L| * η ≤ ε / 2 := by
      rw [hηdef, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg L]
    linarith
  exact (deviationProb_anti _ _ hLd _).trans
    (hmain N hNpos (x₀ N) s i r hsol hs hi hr hsum (ε / 2) (by positivity))

end Epidemics.Kurtz
