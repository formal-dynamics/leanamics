import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Dynamics.Bridge
import Dynamics.Concentration

/-!
# Bridge from `Distribution` to Mathlib's `PMF` and measures

The finite layer of this library (`Distribution`, `expect`, `prob`, `independent`) is kept and
identified with Mathlib's measure-theoretic probability, so that Mathlib's theorems apply to it.
The sample type `α` carries any measurable structure in which singletons are measurable (on a
finite type every set is then measurable); `⊤` is the canonical choice.

* `Distribution.toPMF`: the probability mass function of a distribution, with `toPMF_apply`,
  `toReal_toPMF_apply`, and the compatibilities `toPMF_uniform` (`PMF.uniformOfFintype`),
  `toPMF_point` (`PMF.pure`) and `toPMF_map` (`PMF.map`);
* `Distribution.expect_eq_integral`: `p.expect f = ∫ a, f a ∂p.toPMF.toMeasure`, and
  `Distribution.prob_eq_toMeasure`: `p.prob s = (p.toPMF.toMeasure {a | s a}).toReal`;
* `Distribution.toMeasure_independent`: the measure of the independent product is
  `Measure.pi` of the coordinate measures, hence `Distribution.iIndepFun_independent`: the
  coordinates `x ↦ Y i (x i)` are independent random variables in Mathlib's sense (`iIndepFun`);
* `Distribution.hoeffding`: **Hoeffding's inequality** for independent bounded coordinates with
  arbitrary (non-identical) weights, derived from Mathlib's
  `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` through the bridge.
  It recovers the `{0,1}` uniform case `avg_hoeffding` (checked at the end of this file).
-/

namespace Dynamics

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Distribution

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-! ### The probability mass function -/

/-- The probability mass function of a finite distribution: the weights, as extended
nonnegative reals. -/
noncomputable def toPMF (p : Distribution α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p.weight a)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => p.nonneg a, p.sum_one, ENNReal.ofReal_one]

lemma toPMF_apply (p : Distribution α) (a : α) : p.toPMF a = ENNReal.ofReal (p.weight a) := rfl

/-- The weights are recovered from the mass function. -/
@[simp] lemma toReal_toPMF_apply (p : Distribution α) (a : α) :
    (p.toPMF a).toReal = p.weight a :=
  ENNReal.toReal_ofReal (p.nonneg a)

/-- The uniform distribution is Mathlib's `PMF.uniformOfFintype`. -/
lemma toPMF_uniform [Nonempty α] : (uniform α).toPMF = PMF.uniformOfFintype α := by
  ext a
  rw [toPMF_apply, PMF.uniformOfFintype_apply]
  simp [uniform, ENNReal.ofReal_inv_of_pos (card_cast_pos (α := α))]

/-- A point mass is Mathlib's `PMF.pure`. -/
lemma toPMF_point [DecidableEq α] (a : α) : (point a).toPMF = PMF.pure a := by
  ext b
  rw [toPMF_apply, PMF.pure_apply]
  simp only [point]
  split <;> simp_all

/-- Transport along a function is Mathlib's `PMF.map`. -/
lemma toPMF_map [DecidableEq β] (p : Distribution α) (f : α → β) :
    (p.map f).toPMF = p.toPMF.map f := by
  ext b
  rw [toPMF_apply, PMF.map_apply, tsum_fintype]
  simp only [map]
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ => by split; exact p.nonneg a; rfl]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : f a = b
  · simp [h, toPMF_apply]
  · simp [h, Ne.symm h]

/-! ### Expectation and probability -/

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Expectation is the Lebesgue integral** against the induced measure. -/
theorem expect_eq_integral (p : Distribution α) (f : α → ℝ) :
    p.expect f = ∫ a, f a ∂p.toPMF.toMeasure := by
  simp [expect, PMF.integral_eq_sum]

/-- The measure of a singleton is its weight. -/
lemma toMeasure_singleton (p : Distribution α) (a : α) :
    p.toPMF.toMeasure {a} = ENNReal.ofReal (p.weight a) :=
  PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)

/-- **Probability is the measure of the event**. -/
theorem prob_eq_toMeasure (p : Distribution α) (s : α → Prop) :
    p.prob s = (p.toPMF.toMeasure {a | s a}).toReal := by
  classical
  rw [prob_eq_expect, expect_eq_integral, ← measureReal_def,
    ← integral_indicator_one (MeasurableSet.of_discrete)]
  rfl

/-! ### Independence -/

variable [DecidableEq ι]

/-- **The independent product is the product measure**: the measure induced by
`independent p` is `Measure.pi` of the coordinate measures. -/
theorem toMeasure_independent (p : ι → Distribution α) :
    (independent p).toPMF.toMeasure = Measure.pi fun i => (p i).toPMF.toMeasure := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [Measure.pi_singleton, toMeasure_singleton]
  simp_rw [toMeasure_singleton]
  exact ENNReal.ofReal_prod_of_nonneg fun i _ => (p i).nonneg (x i)

/-- **Coordinates of the independent product are independent** in Mathlib's sense: for any
observables `Y i`, the random variables `x ↦ Y i (x i)` are `iIndepFun` under the measure
induced by `independent p`. -/
theorem iIndepFun_independent {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (p : ι → Distribution α) (Y : (i : ι) → α → β i) :
    iIndepFun (fun i (x : ι → α) => Y i (x i)) (independent p).toPMF.toMeasure := by
  rw [toMeasure_independent]
  exact iIndepFun_pi fun i => Measurable.of_discrete.aemeasurable

end Distribution

/-! ### Hoeffding's inequality through the bridge -/

namespace Distribution

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

/-- **Hoeffding's inequality** for independent bounded coordinates, from Mathlib's
`HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` and Hoeffding's lemma
`hasSubgaussianMGF_of_mem_Icc`:
if `Y i` takes values in `[a i, b i]`, then under `independent p`,
`P(∑ Yᵢ ≥ ∑ 𝔼Yᵢ + λ) ≤ exp(-2λ² / ∑ (bᵢ - aᵢ)²)`. The coordinate laws `p i` may differ. -/
theorem hoeffding (p : ι → Distribution α) (Y : ι → α → ℝ) {a b : ι → ℝ}
    (hY : ∀ i x, Y i x ∈ Set.Icc (a i) (b i)) {lam : ℝ} (hlam : 0 ≤ lam) :
    (independent p).prob (fun x => ∑ i, (p i).expect (Y i) + lam ≤ ∑ i, Y i (x i)) ≤
      Real.exp (-(2 * lam ^ 2 / ∑ i, (b i - a i) ^ 2)) := by
  letI : MeasurableSpace α := ⊤
  set μ := (independent p).toPMF.toMeasure
  -- the centred coordinates `Xᵢ = Yᵢ(xᵢ) - 𝔼Yᵢ`, independent and sub-Gaussian
  have hmean (i : ι) : μ[fun x : ι → α => Y i (x i)] = (p i).expect (Y i) := by
    rw [← expect_eq_integral, independent_expect_eval]
  have hind : iIndepFun (fun i (x : ι → α) => Y i (x i) - (p i).expect (Y i)) μ :=
    iIndepFun_independent p fun i y => Y i y - (p i).expect (Y i)
  have hsub (i : ι) : HasSubgaussianMGF (fun x : ι → α => Y i (x i) - (p i).expect (Y i))
      ((‖b i - a i‖₊ / 2) ^ 2) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun x : ι → α => Y i (x i))
      Measurable.of_discrete.aemeasurable (ae_of_all _ fun x => hY i (x i))
    simpa only [hmean] using h
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s := univ)
    (fun i _ => hsub i) hlam
  -- rewrite the event and the variance proxy
  have hev : {x : ι → α | lam ≤ ∑ i ∈ univ, (Y i (x i) - (p i).expect (Y i))} =
      {x | ∑ i, (p i).expect (Y i) + lam ≤ ∑ i, Y i (x i)} := by
    ext x
    simp only [Set.mem_setOf_eq, sum_sub_distrib]
    constructor <;> intro h <;> linarith
  have hc : (2 * ((∑ i ∈ univ, (‖b i - a i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) =
      (∑ i, (b i - a i) ^ 2) / 2 := by
    push_cast
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [hev, hc] at hH
  rw [prob_eq_toMeasure, ← measureReal_def]
  refine hH.trans_eq ?_
  rw [div_div_eq_mul_div]
  congr 1
  ring

end Distribution

/-- **Cross-check**: `avg_hoeffding` (proved directly in `Dynamics.Concentration`) is the case of
`Distribution.hoeffding` with uniform coordinates and `[a, b] = [0, 1]`. -/
example {γ : Type*} [Fintype γ] [Nonempty γ] {n : ℕ} (Y : Fin n → γ → ℝ)
    (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun ω : Fin n → γ =>
        if (∑ i, avg (Y i)) + lam ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ Real.exp (-(2 * lam ^ 2 / n)) := by
  have h := Distribution.hoeffding (fun _ : Fin n => Distribution.uniform γ) Y
    (a := fun _ => 0) (b := fun _ => 1)
    (fun i x => by rcases hY i x with h | h <;> simp [h]) hlam
  simp only [Distribution.uniform_expect, sub_zero, one_pow, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rwa [Distribution.prob_eq_expect, Distribution.independent_uniform_expect] at h

end Dynamics
