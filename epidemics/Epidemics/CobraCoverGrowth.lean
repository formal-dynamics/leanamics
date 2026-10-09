import Epidemics.CobraCoverRound
import Dynamics.ChernoffAux

/-! # One round of BIPS: expected growth and concentration (EPI-4)

Cooper, Radzik, Rivera, PODC 2016 (arXiv:1602.05768), Section 3 (Lemma 1) and the one-round
facts used in Sections 4 and 5.

Given the infected set `A`, one BIPS round (`bipsStep v A`) infects the source `v` and,
independently, every other vertex `u` that samples a neighbour in `A` among its `k` samples, which
happens with probability `1 - (1 - d_A(u)/r)^k` on an `r`-regular graph. Hence:

* **Lemma 1** (`bips_expected_growth`): `E|A'| ≥ |A| (1 + (1 - λ²)(1 - |A|/n))` for `k ≥ 2`
  (the paper states `k = 2`; more samples only help, since `1 - (1 - p)^k ≥ 1 - (1 - p)²`).
* the moment generating function of `|A'|` is dominated by the Poisson one (`bips_mgf_le`), as
  for every sum of independent `{0,1}` variables (the computation (12) in the proof of Lemma 2);
* the multiplicative Chernoff lower tail (`bips_chernoff_lower`, used in (18) and in the proof of
  Lemma 4).

The deterministic facts `bipsStep_mono` (monotonicity in the infected set, the "standard coupling
argument" of Lemma 4), `bipsStep_univ` (the fully infected state is absorbing on a graph without
isolated vertices) and `source_mem_bipsStep` are proved here.
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

/-- The source is infected after every BIPS round. -/
lemma source_mem_bipsStep (v : V) (A : Finset V) (ρ : Choices G k) : v ∈ bipsStep v A ρ :=
  mem_insert_self _ _

/-- One BIPS round is monotone in the infected set (pathwise coupling: same samples). -/
lemma bipsStep_mono (v : V) {A B : Finset V} (h : A ⊆ B) (ρ : Choices G k) :
    bipsStep v A ρ ⊆ bipsStep v B ρ := by
  intro u hu
  rw [mem_bipsStep] at hu ⊢
  rcases hu with rfl | ⟨i, hi⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, h hi⟩

/-- If `k ≥ 1`, the fully infected state is absorbing. -/
lemma bipsStep_univ (v : V) (hk : 1 ≤ k) (ρ : Choices G k) : bipsStep v univ ρ = univ := by
  ext u
  simp only [mem_univ, iff_true, mem_bipsStep]
  exact Or.inr ⟨⟨0, hk⟩, trivial⟩

variable [DecidableRel G.Adj]

/-- For `p ∈ [0, 1]`, `2p - p² = 1 - (1 - p)² ≤ 1`. -/
private lemma two_sub_sq_le_one {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) : 2 * p - p ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (1 - p)]

/-- For `k ≥ 2` and `p ∈ [0, 1]`, `1 - (1 - p)^k ≥ 1 - (1 - p)² = 2p - p²`. -/
private lemma two_sub_sq_le_one_sub_pow {k : ℕ} (hk : 2 ≤ k) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : 2 * p - p ^ 2 ≤ 1 - (1 - p) ^ k := by
  have h1p0 : 0 ≤ 1 - p := by linarith
  have h1p1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ k ≤ (1 - p) ^ 2 := pow_le_pow_of_le_one h1p0 h1p1 hk
  have hsq : (1 - p) ^ 2 = 1 - (2 * p - p ^ 2) := by ring
  linarith

/-- **Lemma 1** (Section 3; inequalities (3) to (7)). On an `r`-regular graph (`r > 0`) with
`λ = lambdaG G r`, one round of BIPS with `k ≥ 2` samples per vertex from the infected set `A`
gives `E(|A_{t+1}| ∣ A_t = A) ≥ |A| (1 + (1 - λ²)(1 - |A|/n))`. The paper assumes `G` connected,
`λ < 1` and `k = 2`; the bound holds for every regular graph, every `k ≥ 2` and every set `A`
(it need not contain the source). -/
theorem bips_expected_growth {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (v : V) (A : Finset V) :
    (A.card : ℝ) * (1 + (1 - lambdaG G r ^ 2) * (1 - A.card / Fintype.card V)) ≤
      avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
  classical
  let P : V → ℝ := fun u => ((G.neighborFinset u ∩ A).card : ℝ) / r
  have hsumP : ∑ u, P u = (A.card : ℝ) := by
    simpa [P] using sum_neighbor_frac hreg hr A
  have hquad : ∑ u, (2 * P u - P u ^ 2) = 2 * (A.card : ℝ) - ∑ u, P u ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumP]
  have hterm (u : V) : 2 * P u - P u ^ 2 ≤
      if u = v then 1 else 1 - (1 - P u) ^ k := by
    have hmem := neighbor_frac_mem hreg hr u A
    have h0 : 0 ≤ P u := by simpa [P] using hmem.1
    have h1 : P u ≤ 1 := by simpa [P] using hmem.2
    by_cases huv : u = v
    · rw [if_pos huv]
      exact two_sub_sq_le_one h0 h1
    · rw [if_neg huv]
      exact two_sub_sq_le_one_sub_pow hk h0 h1
  have hId : (A.card : ℝ) * (1 + (1 - lambdaG G r ^ 2) *
        (1 - (A.card : ℝ) / Fintype.card V)) =
      2 * (A.card : ℝ) - (lambdaG G r ^ 2 * (A.card : ℝ) +
        (1 - lambdaG G r ^ 2) * (A.card : ℝ) ^ 2 / Fintype.card V) := by
    haveI : Nonempty V := ⟨v⟩
    have hn0 : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Fintype.card_pos)
    field_simp
    ring
  have hE : ∑ u, (if u = v then (1 : ℝ) else 1 - (1 - P u) ^ k) =
      avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
    rw [bips_expected_card]
    simp_rw [bips_infect_prob hreg hr v]
    simp [P]
  calc (A.card : ℝ) * (1 + (1 - lambdaG G r ^ 2) * (1 - A.card / Fintype.card V))
      = 2 * (A.card : ℝ) - (lambdaG G r ^ 2 * (A.card : ℝ) +
          (1 - lambdaG G r ^ 2) * (A.card : ℝ) ^ 2 / Fintype.card V) := hId
    _ ≤ 2 * (A.card : ℝ) - ∑ u, P u ^ 2 := by
        have hsq : ∑ u, P u ^ 2 ≤ lambdaG G r ^ 2 * (A.card : ℝ) +
            (1 - lambdaG G r ^ 2) * (A.card : ℝ) ^ 2 / Fintype.card V := by
          simpa [P] using sum_sq_neighbor_le hreg hr A
        linarith
    _ = ∑ u, (2 * P u - P u ^ 2) := hquad.symm
    _ ≤ ∑ u, (if u = v then 1 else 1 - (1 - P u) ^ k) :=
        Finset.sum_le_sum fun u _ => hterm u
    _ = avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := hE

/-- **One-round moment generating function** (computation (12) in the proof of Lemma 2): the
vertices are infected independently given `A`, so for every real `φ`,
`E(e^{-φ |A'|}) = ∏ᵤ (1 - (1 - e^{-φ}) P(u ∈ A')) ≤ exp(-(1 - e^{-φ}) E|A'|)`. -/
theorem bips_mgf_le (v : V) (A : Finset V) (φ : ℝ) :
    avg (fun ρ : Choices G k => Real.exp (-φ * (bipsStep v A ρ).card)) ≤
      Real.exp (-(1 - Real.exp (-φ)) *
        avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ))) := by
  classical
  by_cases hne : Nonempty (Choices G k)
  · haveI := hne
    let p : (u : V) → (Fin k → G.neighborSet u) → Prop :=
      fun u σ => u = v ∨ ∃ i, (σ i : V) ∈ A
    let f : (u : V) → (Fin k → G.neighborSet u) → ℝ :=
      fun u σ => Real.exp (-φ * if p u σ then (1 : ℝ) else 0)
    have hp_mem (ρ : Choices G k) (u : V) : (u ∈ bipsStep v A ρ) ↔ p u (ρ u) := by
      simp [p, mem_bipsStep]
    have hexp (ρ : Choices G k) :
        Real.exp (-φ * ((bipsStep v A ρ).card : ℝ)) = ∏ u, f u (ρ u) := by
      rw [bipsStep_card_eq_sum v A ρ, Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun u _ => ?_
      apply congrArg (fun t : ℝ => Real.exp (-φ * t))
      by_cases hmem : u ∈ bipsStep v A ρ
      · rw [if_pos hmem, if_pos ((hp_mem ρ u).1 hmem)]
      · rw [if_neg hmem, if_neg (fun h => hmem ((hp_mem ρ u).2 h))]
    have hfib (u : V) : Nonempty (Fin k → G.neighborSet u) :=
      Nonempty.map (fun ρ => ρ u) hne
    let prob : V → ℝ :=
      fun u => avg (fun ρ : Choices G k => if u ∈ bipsStep v A ρ then (1 : ℝ) else 0)
    have havg_u (u : V) : avg (f u) = 1 - (1 - Real.exp (-φ)) * prob u := by
      haveI := hfib u
      rw [show f u = fun σ => Real.exp (-φ * if p u σ then (1 : ℝ) else 0) from rfl,
        avg_exp_bernoulli φ (p u)]
      refine congrArg (fun t => 1 - (1 - Real.exp (-φ)) * t) ?_
      have hpoint (ρ : Choices G k) :
          (if u ∈ bipsStep v A ρ then (1 : ℝ) else 0) =
            if p u (ρ u) then 1 else 0 := by
        by_cases hmem : u ∈ bipsStep v A ρ
        · rw [if_pos hmem, if_pos ((hp_mem ρ u).1 hmem)]
        · rw [if_neg hmem, if_neg (fun h => hmem ((hp_mem ρ u).2 h))]
      have hdep := avg_choices_depends u (fun σ => if p u σ then (1 : ℝ) else 0) hne
      calc avg (fun σ => if p u σ then (1 : ℝ) else 0)
          = avg (fun ρ : Choices G k => if p u (ρ u) then (1 : ℝ) else 0) := hdep.symm
        _ = prob u := by
            simp_rw [← hpoint]
            rfl
    have hp0 (u : V) : 0 ≤ prob u :=
      avg_nonneg fun ρ => by by_cases h : u ∈ bipsStep v A ρ <;> simp [h]
    have hp1 (u : V) : prob u ≤ 1 := by
      have hle (ρ : Choices G k) :
          (if u ∈ bipsStep v A ρ then (1 : ℝ) else 0) ≤ 1 := by
        by_cases h : u ∈ bipsStep v A ρ <;> simp [h]
      calc prob u ≤ avg (fun _ : Choices G k => (1 : ℝ)) := avg_le_avg hle
        _ = 1 := avg_const 1
    set a : ℝ := 1 - Real.exp (-φ) with ha
    have ha_le : a ≤ 1 := by
      have : 0 ≤ Real.exp (-φ) := Real.exp_nonneg _
      linarith
    have hfac0 (u : V) : 0 ≤ 1 - a * prob u := by
      by_cases hapos : 0 ≤ a
      · have hmul : a * prob u ≤ a * 1 := mul_le_mul_of_nonneg_left (hp1 u) hapos
        rw [mul_one] at hmul
        linarith
      · push Not at hapos
        have : a * prob u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hapos.le (hp0 u)
        linarith
    have hfac_le (u : V) : 1 - a * prob u ≤ Real.exp (-(a * prob u)) := by
      linarith [Real.add_one_le_exp (-(a * prob u))]
    have hsum : ∑ u, prob u =
        avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
      simpa [prob] using (bips_expected_card v A).symm
    calc avg (fun ρ : Choices G k => Real.exp (-φ * ((bipsStep v A ρ).card : ℝ)))
        = ∏ u, avg (f u) := by simp_rw [hexp, avg_choices_prod]
      _ = ∏ u, (1 - a * prob u) := by simp_rw [havg_u]
      _ ≤ ∏ u, Real.exp (-(a * prob u)) :=
          Finset.prod_le_prod (fun u _ => hfac0 u) (fun u _ => hfac_le u)
      _ = Real.exp (-(a * ∑ u, prob u)) := by
          rw [← Real.exp_sum]
          congr 1
          rw [show ∑ u, -(a * prob u) = -(a * ∑ u, prob u) by
            rw [Finset.sum_neg_distrib, ← Finset.mul_sum]]
      _ = Real.exp (-(1 - Real.exp (-φ)) *
            avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ))) := by
          refine congrArg Real.exp ?_
          rw [hsum, ha]
          ring
  · haveI : IsEmpty (Choices G k) := not_nonempty_iff.mp hne
    rw [avg_eq_zero_of_isEmpty]
    exact (Real.exp_pos _).le

/-- **Chernoff lower tail for one BIPS round** (used in (18) of Lemma 3 and in the proof of
Lemma 4): if `μ ≤ E|A'|` and `0 < δ < 1`, then `P(|A'| ≤ (1 - δ) μ) ≤ exp(-δ² μ / 2)`. -/
theorem bips_chernoff_lower (v : V) (A : Finset V) {δ μ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμ : μ ≤ avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ))) :
    avg (fun ρ : Choices G k =>
        if ((bipsStep v A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
      Real.exp (-(δ ^ 2 * μ / 2)) := by
  let ind : Choices G k → ℝ :=
    fun ρ => if ((bipsStep v A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0
  by_cases hμ0 : μ ≤ 0
  · have hLHS : avg ind ≤ 1 := by
      by_cases hne : Nonempty (Choices G k)
      · haveI := hne
        have hle (ρ : Choices G k) : ind ρ ≤ 1 := by
          by_cases h : ((bipsStep v A ρ).card : ℝ) ≤ (1 - δ) * μ <;> simp [ind, h]
        calc avg ind ≤ avg (fun _ : Choices G k => (1 : ℝ)) := avg_le_avg hle
          _ = 1 := avg_const 1
      · haveI : IsEmpty (Choices G k) := not_nonempty_iff.mp hne
        rw [avg_eq_zero_of_isEmpty]
        exact zero_le_one
    have hRHS : (1 : ℝ) ≤ Real.exp (-(δ ^ 2 * μ / 2)) := by
      rw [Real.one_le_exp_iff]
      have hnum : δ ^ 2 * μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg δ) hμ0
      have hdiv : δ ^ 2 * μ / 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum (by norm_num)
      linarith
    exact hLHS.trans hRHS
  · push Not at hμ0
    have h1δ : 0 < 1 - δ := by linarith
    let φ : ℝ := -Real.log (1 - δ)
    have hφexp : Real.exp (-φ) = 1 - δ := by
      simp only [φ, neg_neg, Real.exp_log h1δ]
    have ha : 1 - Real.exp (-φ) = δ := by linarith
    have hφpos : 0 < φ := by
      have hlog : Real.log (1 - δ) < 0 := Real.log_neg h1δ (by linarith)
      simp only [φ]
      linarith
    have hpoint (ρ : Choices G k) : ind ρ ≤
        Real.exp (φ * ((1 - δ) * μ)) *
          Real.exp (-φ * ((bipsStep v A ρ).card : ℝ)) := by
      by_cases hle : ((bipsStep v A ρ).card : ℝ) ≤ (1 - δ) * μ
      · rw [show ind ρ = 1 by simp [ind, hle]]
        have hdiff : 0 ≤ (1 - δ) * μ - ((bipsStep v A ρ).card : ℝ) := by linarith
        have hexp1 : (1 : ℝ) ≤
            Real.exp (φ * ((1 - δ) * μ - ((bipsStep v A ρ).card : ℝ))) := by
          rw [Real.one_le_exp_iff]
          exact mul_nonneg hφpos.le hdiff
        have hsplit : φ * ((1 - δ) * μ - ((bipsStep v A ρ).card : ℝ)) =
            φ * ((1 - δ) * μ) + -φ * ((bipsStep v A ρ).card : ℝ) := by ring
        rw [hsplit, Real.exp_add] at hexp1
        exact hexp1
      · rw [show ind ρ = 0 by simp [ind, hle]]
        positivity
    have hE : μ ≤ avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := hμ
    calc avg ind
        ≤ avg (fun ρ : Choices G k => Real.exp (φ * ((1 - δ) * μ)) *
            Real.exp (-φ * ((bipsStep v A ρ).card : ℝ))) := avg_le_avg hpoint
      _ = Real.exp (φ * ((1 - δ) * μ)) *
            avg (fun ρ : Choices G k => Real.exp (-φ * ((bipsStep v A ρ).card : ℝ))) :=
          avg_const_mul _ _
      _ ≤ Real.exp (φ * ((1 - δ) * μ)) *
            Real.exp (-(1 - Real.exp (-φ)) *
              avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ))) := by
          exact mul_le_mul_of_nonneg_left (bips_mgf_le v A φ) (Real.exp_pos _).le
      _ = Real.exp (φ * ((1 - δ) * μ)) *
            Real.exp (-δ * avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ))) := by
          rw [ha]
      _ ≤ Real.exp (φ * ((1 - δ) * μ)) * Real.exp (-δ * μ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonpos_left hE (by linarith : -δ ≤ 0))
      _ = Real.exp (φ * ((1 - δ) * μ) - δ * μ) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ Real.exp (-(δ ^ 2 * μ / 2)) := by
          refine Real.exp_le_exp.mpr ?_
          have hlog := neg_sub_one_sub_mul_log_le hδ0.le hδ1
          have hcoef : φ * (1 - δ) - δ ≤ -(δ ^ 2 / 2) := by
            have hcomm : -Real.log (1 - δ) * (1 - δ) - δ =
                -δ - (1 - δ) * Real.log (1 - δ) := by ring
            simp only [φ]
            linarith
          have hmul := mul_le_mul_of_nonneg_left hcoef hμ0.le
          calc φ * ((1 - δ) * μ) - δ * μ
              = μ * (φ * (1 - δ) - δ) := by ring
            _ ≤ μ * -(δ ^ 2 / 2) := hmul
            _ = -(δ ^ 2 * μ / 2) := by ring

end Epidemics
