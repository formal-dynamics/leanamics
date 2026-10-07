import Dynamics.ChernoffAux

/-!
# Chernoff bounds for independent, non-identical Bernoulli trials

Roadmap target FND-3. Source: M. Mitzenmacher and E. Upfal, *Probability and Computing*,
Cambridge University Press, 2005, Section 4.2.1: Theorem 4.4, bound (4.1) (upper tail),
Theorem 4.5, bounds (4.4) and (4.5) (lower tail), and Exercise 4.7 (the mean `μ = 𝔼X` may
be replaced by any `μ_H ≥ μ` in the upper tail and any `μ_L ≤ μ` in the lower tail).

Let `X = ∑ᵢ Xᵢ` be a sum of independent `{0,1}`-valued trials with `P(Xᵢ = 1) = pᵢ` and
`μ = ∑ᵢ pᵢ`. For `μ_L ≤ μ ≤ μ_H`:

* `P(X ≥ (1 + δ) μ_H) ≤ (e^δ / (1 + δ)^(1 + δ))^μ_H ≤ exp (-δ² μ_H / (2 + δ))` for `δ > 0`;
* `P(X ≤ (1 - δ) μ_L) ≤ (e^(-δ) / (1 - δ)^(1 - δ))^μ_L ≤ exp (-δ² μ_L / 2)` for
  `0 < δ < 1`.

Taking `μ_H = μ` or `μ_L = μ` gives the bounds for the exact mean. Each bound is stated in
three settings, all on the finite product space `ι → α` (no measure theory):

* **general**: `ω` is drawn from the independent product `Distribution.independent P` of a
  family `P : ι → Distribution α`, and `Xᵢ = Y i (ω i)` for observables `Y i : α → {0,1}`,
  so that `pᵢ = (P i).expect (Y i)`;
* **Bernoulli coins**: `ω : ι → Bool` has independent coordinates `ω i ~ bernoulli (p i)`
  and `X` counts the heads among the coins of a finite set `S` (`S = univ` is the textbook
  statement);
* **uniform rounds**: `ω : ι → γ` is uniform (one independent uniform draw per agent, as in
  `Dynamics.Concentration`), probabilities are `avg` of indicators and `pᵢ = avg (Y i)`.
  This is the form produced by `Kernel.prob_ofStep` for one round of a dynamics.
-/

namespace Dynamics

open Finset Real

namespace Distribution

/-- A biased coin: `true` with probability `p`. -/
noncomputable def bernoulli (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distribution Bool where
  weight b := if b then p else 1 - p
  nonneg b := by cases b <;> simp [h0, h1]
  sum_one := by simp

/-! ### Independent `{0,1}`-valued observables on a product distribution -/

/-- **Chernoff upper tail**, ratio form (Mitzenmacher–Upfal, Theorem 4.4, bound (4.1), with
an upper bound `μH` on the mean as in Exercise 4.7): if `ω ~ independent P`, every `Y i` is
`{0,1}`-valued and `∑ᵢ 𝔼[Y i] ≤ μH`, then for `δ > 0`,
`P(∑ᵢ Y i (ω i) ≥ (1 + δ) μH) ≤ (e^δ / (1 + δ)^(1 + δ))^μH`. -/
theorem chernoff_upper_ratio {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → Distribution α) (Y : ι → α → ℝ) (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1)
    {δ μH : ℝ} (hδ : 0 < δ) (hμH : ∑ i, (P i).expect (Y i) ≤ μH) :
    (independent P).prob (fun ω => (1 + δ) * μH ≤ ∑ i, Y i (ω i))
      ≤ (exp δ / (1 + δ) ^ (1 + δ)) ^ μH := by
  have h1 : 0 < 1 + δ := by linarith
  have h := prob_ge_le_exp P Y hY (log_nonneg (by linarith : (1 : ℝ) ≤ 1 + δ)) hμH ((1 + δ) * μH)
  rw [exp_log h1] at h
  rw [exp_div_rpow_self_rpow h1]
  refine h.trans_eq (congrArg exp ?_)
  ring

/-- **Chernoff upper tail** (Mitzenmacher–Upfal, Theorem 4.4 and Exercise 4.7, in the
closed form obtained from (4.1) by `log (1 + δ) ≥ 2δ / (2 + δ)`): if `ω ~ independent P`,
every `Y i` is `{0,1}`-valued and `∑ᵢ 𝔼[Y i] ≤ μH`, then for `δ > 0`,
`P(∑ᵢ Y i (ω i) ≥ (1 + δ) μH) ≤ exp (-δ² μH / (2 + δ))`. -/
theorem chernoff_upper {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → Distribution α) (Y : ι → α → ℝ) (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1)
    {δ μH : ℝ} (hδ : 0 < δ) (hμH : ∑ i, (P i).expect (Y i) ≤ μH) :
    (independent P).prob (fun ω => (1 + δ) * μH ≤ ∑ i, Y i (ω i))
      ≤ exp (-(δ ^ 2 * μH / (2 + δ))) := by
  have hμ0 : 0 ≤ μH := (sum_expect_nonneg P Y hY).trans hμH
  refine (chernoff_upper_ratio P Y hY hδ hμH).trans ?_
  rw [exp_div_rpow_self_rpow (by linarith)]
  refine exp_le_exp.mpr ?_
  have h := mul_le_mul_of_nonneg_left (sub_one_add_mul_log_le hδ.le) hμ0
  have e : μH * -(δ ^ 2 / (2 + δ)) = -(δ ^ 2 * μH / (2 + δ)) := by ring
  linarith

/-- **Chernoff lower tail**, ratio form (Mitzenmacher–Upfal, Theorem 4.5, bound (4.4), with
a lower bound `μL` on the mean as in Exercise 4.7): if `ω ~ independent P`, every `Y i` is
`{0,1}`-valued and `μL ≤ ∑ᵢ 𝔼[Y i]`, then for `0 < δ < 1`,
`P(∑ᵢ Y i (ω i) ≤ (1 - δ) μL) ≤ (e^(-δ) / (1 - δ)^(1 - δ))^μL`. -/
theorem chernoff_lower_ratio {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → Distribution α) (Y : ι → α → ℝ) (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1)
    {δ μL : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμL : μL ≤ ∑ i, (P i).expect (Y i)) :
    (independent P).prob (fun ω => ∑ i, Y i (ω i) ≤ (1 - δ) * μL)
      ≤ (exp (-δ) / (1 - δ) ^ (1 - δ)) ^ μL := by
  have h1 : 0 < 1 - δ := by linarith
  have h := prob_le_le_exp P Y hY (log_nonpos h1.le (by linarith)) hμL ((1 - δ) * μL)
  rw [exp_log h1] at h
  rw [exp_div_rpow_self_rpow h1]
  refine h.trans_eq (congrArg exp ?_)
  ring

/-- **Chernoff lower tail** (Mitzenmacher–Upfal, Theorem 4.5, bound (4.5), with a lower
bound `μL` on the mean as in Exercise 4.7): if `ω ~ independent P`, every `Y i` is
`{0,1}`-valued and `μL ≤ ∑ᵢ 𝔼[Y i]`, then for `0 < δ < 1`,
`P(∑ᵢ Y i (ω i) ≤ (1 - δ) μL) ≤ exp (-δ² μL / 2)`. -/
theorem chernoff_lower {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → Distribution α) (Y : ι → α → ℝ) (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1)
    {δ μL : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμL : μL ≤ ∑ i, (P i).expect (Y i)) :
    (independent P).prob (fun ω => ∑ i, Y i (ω i) ≤ (1 - δ) * μL)
      ≤ exp (-(δ ^ 2 * μL / 2)) := by
  rcases le_or_gt 0 μL with hμ0 | hμ0
  · refine (chernoff_lower_ratio P Y hY hδ0 hδ1 hμL).trans ?_
    rw [exp_div_rpow_self_rpow (by linarith)]
    refine exp_le_exp.mpr ?_
    have h := mul_le_mul_of_nonneg_left (neg_sub_one_sub_mul_log_le hδ0.le hδ1) hμ0
    have e : μL * -(δ ^ 2 / 2) = -(δ ^ 2 * μL / 2) := by ring
    linarith
  · -- `μL < 0`: the bound exceeds `1`
    have h : δ ^ 2 * μL ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg δ) hμ0.le
    refine (prob_le_one _ _).trans ?_
    linarith [add_one_le_exp (-(δ ^ 2 * μL / 2))]

/-! ### Independent Bernoulli coins -/

/-- Expectation under a biased coin. -/
lemma bernoulli_expect (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Bool → ℝ) :
    (bernoulli p h0 h1).expect f = p * f true + (1 - p) * f false := by
  simp [expect, bernoulli]

/-- The number of heads among the coins of `S` has mean `∑_{i ∈ S} pᵢ`. -/
lemma sum_bernoulli_expect {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι) :
    ∑ i, (bernoulli (p i) (hp0 i) (hp1 i)).expect
        (fun b => if i ∈ S then (if b = true then (1 : ℝ) else 0) else 0) = ∑ i ∈ S, p i := by
  rw [← Fintype.sum_ite_mem S p]
  refine sum_congr rfl fun i _ => ?_
  rw [bernoulli_expect]
  by_cases hi : i ∈ S <;> simp [hi]

/-- **Chernoff upper tail for Bernoulli(`pᵢ`) coins**, ratio form (Mitzenmacher–Upfal,
Theorem 4.4, bound (4.1), and Exercise 4.7): for independent coins `ω i ~ bernoulli (p i)`,
a finite set `S` of coins with `∑_{i ∈ S} pᵢ ≤ μH` and `δ > 0`, the number of heads in `S`
satisfies `P(#heads ≥ (1 + δ) μH) ≤ (e^δ / (1 + δ)^(1 + δ))^μH`. -/
theorem bernoulli_chernoff_upper_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι)
    {δ μH : ℝ} (hδ : 0 < δ) (hμH : ∑ i ∈ S, p i ≤ μH) :
    (independent fun i => bernoulli (p i) (hp0 i) (hp1 i)).prob
        (fun ω => (1 + δ) * μH ≤ ((S.filter fun i => ω i = true).card : ℝ))
      ≤ (exp δ / (1 + δ) ^ (1 + δ)) ^ μH := by
  have h := chernoff_upper_ratio (fun i => bernoulli (p i) (hp0 i) (hp1 i))
    (fun i b => if i ∈ S then (if b = true then (1 : ℝ) else 0) else 0)
    (fun i b => by split_ifs <;> simp) hδ ((sum_bernoulli_expect p hp0 hp1 S).trans_le hμH)
  simpa only [sum_ite_mem_ite_eq_card] using h

/-- **Chernoff upper tail for Bernoulli(`pᵢ`) coins** (Mitzenmacher–Upfal, Theorem 4.4 and
Exercise 4.7, closed form via `log (1 + δ) ≥ 2δ / (2 + δ)`): for independent coins
`ω i ~ bernoulli (p i)`, a finite set `S` of coins with `∑_{i ∈ S} pᵢ ≤ μH` and `δ > 0`,
`P(#heads in S ≥ (1 + δ) μH) ≤ exp (-δ² μH / (2 + δ))`. -/
theorem bernoulli_chernoff_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι)
    {δ μH : ℝ} (hδ : 0 < δ) (hμH : ∑ i ∈ S, p i ≤ μH) :
    (independent fun i => bernoulli (p i) (hp0 i) (hp1 i)).prob
        (fun ω => (1 + δ) * μH ≤ ((S.filter fun i => ω i = true).card : ℝ))
      ≤ exp (-(δ ^ 2 * μH / (2 + δ))) := by
  have h := chernoff_upper (fun i => bernoulli (p i) (hp0 i) (hp1 i))
    (fun i b => if i ∈ S then (if b = true then (1 : ℝ) else 0) else 0)
    (fun i b => by split_ifs <;> simp) hδ ((sum_bernoulli_expect p hp0 hp1 S).trans_le hμH)
  simpa only [sum_ite_mem_ite_eq_card] using h

/-- **Chernoff lower tail for Bernoulli(`pᵢ`) coins**, ratio form (Mitzenmacher–Upfal,
Theorem 4.5, bound (4.4), and Exercise 4.7): for independent coins `ω i ~ bernoulli (p i)`,
a finite set `S` of coins with `μL ≤ ∑_{i ∈ S} pᵢ` and `0 < δ < 1`,
`P(#heads in S ≤ (1 - δ) μL) ≤ (e^(-δ) / (1 - δ)^(1 - δ))^μL`. -/
theorem bernoulli_chernoff_lower_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι)
    {δ μL : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμL : μL ≤ ∑ i ∈ S, p i) :
    (independent fun i => bernoulli (p i) (hp0 i) (hp1 i)).prob
        (fun ω => ((S.filter fun i => ω i = true).card : ℝ) ≤ (1 - δ) * μL)
      ≤ (exp (-δ) / (1 - δ) ^ (1 - δ)) ^ μL := by
  have h := chernoff_lower_ratio (fun i => bernoulli (p i) (hp0 i) (hp1 i))
    (fun i b => if i ∈ S then (if b = true then (1 : ℝ) else 0) else 0)
    (fun i b => by split_ifs <;> simp) hδ0 hδ1
    (hμL.trans_eq (sum_bernoulli_expect p hp0 hp1 S).symm)
  simpa only [sum_ite_mem_ite_eq_card] using h

/-- **Chernoff lower tail for Bernoulli(`pᵢ`) coins** (Mitzenmacher–Upfal, Theorem 4.5,
bound (4.5), and Exercise 4.7): for independent coins `ω i ~ bernoulli (p i)`, a finite set
`S` of coins with `μL ≤ ∑_{i ∈ S} pᵢ` and `0 < δ < 1`,
`P(#heads in S ≤ (1 - δ) μL) ≤ exp (-δ² μL / 2)`. -/
theorem bernoulli_chernoff_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι)
    {δ μL : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμL : μL ≤ ∑ i ∈ S, p i) :
    (independent fun i => bernoulli (p i) (hp0 i) (hp1 i)).prob
        (fun ω => ((S.filter fun i => ω i = true).card : ℝ) ≤ (1 - δ) * μL)
      ≤ exp (-(δ ^ 2 * μL / 2)) := by
  have h := chernoff_lower (fun i => bernoulli (p i) (hp0 i) (hp1 i))
    (fun i b => if i ∈ S then (if b = true then (1 : ℝ) else 0) else 0)
    (fun i b => by split_ifs <;> simp) hδ0 hδ1
    (hμL.trans_eq (sum_bernoulli_expect p hp0 hp1 S).symm)
  simpa only [sum_ite_mem_ite_eq_card] using h

end Distribution

/-! ### Uniform rounds -/

/-- **Chernoff upper tail for one uniform round**, ratio form (Mitzenmacher–Upfal,
Theorem 4.4, bound (4.1), and Exercise 4.7): if `ω : ι → γ` is uniform, every `Y i` is
`{0,1}`-valued and `∑ᵢ avg (Y i) ≤ μH`, then for `δ > 0`,
`P(∑ᵢ Y i (ω i) ≥ (1 + δ) μH) ≤ (e^δ / (1 + δ)^(1 + δ))^μH`. -/
theorem avg_chernoff_upper_ratio {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (Y : ι → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {δ μH : ℝ} (hδ : 0 < δ) (hμH : ∑ i, avg (Y i) ≤ μH) :
    avg (fun ω : ι → γ => if (1 + δ) * μH ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ (exp δ / (1 + δ) ^ (1 + δ)) ^ μH := by
  have h1 : 0 < 1 + δ := by linarith
  exact avg_indicator_le_of_independent _
    (rpow_pos_of_pos (div_pos (exp_pos δ) (rpow_pos_of_pos h1 _)) _).le fun P hP =>
      Distribution.chernoff_upper_ratio P Y hY hδ (by simpa only [hP] using hμH)

/-- **Chernoff upper tail for one uniform round** (Mitzenmacher–Upfal, Theorem 4.4 and
Exercise 4.7, closed form via `log (1 + δ) ≥ 2δ / (2 + δ)`): if `ω : ι → γ` is uniform,
every `Y i` is `{0,1}`-valued and `∑ᵢ avg (Y i) ≤ μH`, then for `δ > 0`,
`P(∑ᵢ Y i (ω i) ≥ (1 + δ) μH) ≤ exp (-δ² μH / (2 + δ))`. -/
theorem avg_chernoff_upper {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (Y : ι → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {δ μH : ℝ} (hδ : 0 < δ) (hμH : ∑ i, avg (Y i) ≤ μH) :
    avg (fun ω : ι → γ => if (1 + δ) * μH ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ exp (-(δ ^ 2 * μH / (2 + δ))) := by
  exact avg_indicator_le_of_independent _ (exp_pos _).le fun P hP =>
    Distribution.chernoff_upper P Y hY hδ (by simpa only [hP] using hμH)

/-- **Chernoff lower tail for one uniform round**, ratio form (Mitzenmacher–Upfal,
Theorem 4.5, bound (4.4), and Exercise 4.7): if `ω : ι → γ` is uniform, every `Y i` is
`{0,1}`-valued and `μL ≤ ∑ᵢ avg (Y i)`, then for `0 < δ < 1`,
`P(∑ᵢ Y i (ω i) ≤ (1 - δ) μL) ≤ (e^(-δ) / (1 - δ)^(1 - δ))^μL`. -/
theorem avg_chernoff_lower_ratio {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (Y : ι → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {δ μL : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμL : μL ≤ ∑ i, avg (Y i)) :
    avg (fun ω : ι → γ => if ∑ i, Y i (ω i) ≤ (1 - δ) * μL then (1 : ℝ) else 0)
      ≤ (exp (-δ) / (1 - δ) ^ (1 - δ)) ^ μL := by
  have h1 : 0 < 1 - δ := by linarith
  exact avg_indicator_le_of_independent _
    (rpow_pos_of_pos (div_pos (exp_pos (-δ)) (rpow_pos_of_pos h1 _)) _).le fun P hP =>
      Distribution.chernoff_lower_ratio P Y hY hδ0 hδ1 (by simpa only [hP] using hμL)

/-- **Chernoff lower tail for one uniform round** (Mitzenmacher–Upfal, Theorem 4.5,
bound (4.5), and Exercise 4.7): if `ω : ι → γ` is uniform, every `Y i` is `{0,1}`-valued
and `μL ≤ ∑ᵢ avg (Y i)`, then for `0 < δ < 1`,
`P(∑ᵢ Y i (ω i) ≤ (1 - δ) μL) ≤ exp (-δ² μL / 2)`. -/
theorem avg_chernoff_lower {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (Y : ι → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {δ μL : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμL : μL ≤ ∑ i, avg (Y i)) :
    avg (fun ω : ι → γ => if ∑ i, Y i (ω i) ≤ (1 - δ) * μL then (1 : ℝ) else 0)
      ≤ exp (-(δ ^ 2 * μL / 2)) := by
  exact avg_indicator_le_of_independent _ (exp_pos _).le fun P hP =>
    Distribution.chernoff_lower P Y hY hδ0 hδ1 (by simpa only [hP] using hμL)

end Dynamics
