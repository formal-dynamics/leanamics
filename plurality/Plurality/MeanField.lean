import Plurality.AnyStart
import Dynamics.Bridge
import Dynamics.MajorityMap

/-!
# Binary 3-Majority: mean field, and conformist transmission on counts

Binary 3-Majority on the complete graph with self-loops (`binKernel n`: in every round each of the
`n` nodes samples three nodes uniformly at random, with replacement and possibly itself, and adopts
the majority opinion of its samples) maps the fraction `x` of nodes holding opinion `1` to
`3x² - 2x³` in expectation (`binKernel_meanField`, `ThreeMajority.avg_card_step` stated as a
`Dynamics.Kernel.MeanField`). This map is `Dynamics.majorityMap`, which is Galam's map with groups
of three (`Dynamics.galamMap_eq`) and conformist transmission with `D = 1`
(`Dynamics.conformistMap_one`).

Conformist transmission (Boyd and Richerson 1985) in a population of `n` with non-overlapping
generations, in which every new individual samples its three models with replacement from the
whole previous generation, is a chain on the number of carriers of a variant: from `k` carriers,
the three models of a new individual include a number of carriers of law `Bin(3, k/n)`, so each new
individual acquires the variant independently with probability `p + D p (1 - p)(2p - 1)`, `p = k/n`
(`Dynamics.conformistMap_eq_expect`), and the next generation has `Bin(n, p + D p (1 - p)(2p - 1))`
carriers (`conformistCountKernel`). Its mean-field map is Boyd and Richerson's recursion
(`conformistCountKernel_meanField`). With `D = 1`, binary 3-Majority lumps to it under the number of
nodes holding opinion `1` (`binKernel_lumps`): the two are the same chain on counts (row
`three-majority` of the cross-field dictionary).
-/

namespace Plurality

open Finset Dynamics
open ThreeMajority (Tgt3 Y_maj sampleCountOf)

variable {n : ℕ}

/-! ### The mean-field map of binary 3-Majority -/

/-- **The mean-field map of binary 3-Majority is the majority map.** One round maps the fraction
`x = |I|/n` of nodes holding opinion `1` to `3x² - 2x³` in expectation. -/
theorem binKernel_meanField (n : ℕ) [NeZero n] :
    (binKernel n).MeanField (fun I (_ : Unit) => (I.card : ℝ) / n)
      fun u _ => majorityMap (u ()) := by
  intro I _
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h := ThreeMajority.avg_card_step (Nat.one_le_iff_ne_zero.2 (NeZero.ne n)) I
  rw [ThreeMajority.avg_ind_eq] at h
  simp only [binKernel, Kernel.apply_ofStep, div_eq_mul_inv, mul_comm _ (n : ℝ)⁻¹,
    Dynamics.avg_const_mul]
  rw [show Dynamics.avg (fun r : Tgt3 n => ((ThreeMajority.step I r).card : ℝ)) =
    ThreeMajority.avg (fun r : Tgt3 n => ((ThreeMajority.step I r).card : ℝ)) from rfl, h]
  unfold majorityMap
  field_simp

/-! ### Conformist transmission on counts -/

lemma count_div_nonneg (n : ℕ) (k : Fin (n + 1)) : 0 ≤ (k : ℝ) / n := by positivity

lemma count_div_le_one (n : ℕ) (k : Fin (n + 1)) : (k : ℝ) / n ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Fin.is_le k) (Nat.cast_nonneg n)

/-- **Conformist transmission on counts** (Boyd and Richerson 1985, in its individual-based form).
In a population of `n` with non-overlapping generations, every new individual samples three models
with replacement from the whole previous generation and acquires a variant held by `j` of them
with probability `Dynamics.conformistTable D j`. From `k` carriers of the variant, the next
generation has `Bin(n, p + D p (1 - p)(2p - 1))` carriers, `p = k/n`. -/
noncomputable def conformistCountKernel (n : ℕ) (D : ℝ) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    Kernel (Fin (n + 1)) := fun k =>
  Distribution.binomial n (conformistMap D ((k : ℝ) / n))
    (conformistMap_nonneg hD0 hD1 (count_div_nonneg n k) (count_div_le_one n k))
    (conformistMap_le_one hD0 hD1 (count_div_nonneg n k) (count_div_le_one n k))

/-- **The mean-field map of conformist transmission is Boyd and Richerson's recursion**: one
generation maps the frequency `p` of the variant to `p + D p (1 - p)(2p - 1)` in expectation. -/
theorem conformistCountKernel_meanField {n : ℕ} (hn : 1 ≤ n) {D : ℝ} (hD0 : 0 ≤ D)
    (hD1 : D ≤ 1) :
    (conformistCountKernel n D hD0 hD1).MeanField (fun k (_ : Unit) => (k : ℝ) / n)
      fun u _ => conformistMap D (u ()) := by
  intro k _
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  simp only [Kernel.apply, conformistCountKernel, div_eq_mul_inv, mul_comm _ (n : ℝ)⁻¹,
    Distribution.expect_mul, Distribution.binomial_expect_val]
  field_simp

/-- The number of nodes in `I`, in `{0, …, n}`. -/
def cardFin (I : Finset (Fin n)) : Fin (n + 1) :=
  ⟨I.card, Nat.lt_succ_of_le ((card_le_univ I).trans_eq (Fintype.card_fin n))⟩

/-- A round of 3-Majority draws the sample triples of the `n` nodes independently and
uniformly. -/
theorem uniform_tgt3_eq_independent (n : ℕ) [NeZero n] :
    Distribution.uniform (Tgt3 n) =
      Distribution.independent fun _ : Fin n => Distribution.uniform (Fin n × Fin n × Fin n) :=
  Distribution.ext_expect fun g => by
    rw [Distribution.uniform_expect]
    exact (Distribution.independent_uniform_expect g).symm

/-- **Binary 3-Majority is conformist transmission with `D = 1` on counts.** Under binary
3-Majority on `K_n` with self-loops, the number of nodes holding opinion `1` is the chain of
conformist transmission with `D = 1`, in which every new individual samples three models with
replacement from the whole previous generation: one round from a configuration with `k` such
nodes leads to `Bin(n, 3p² - 2p³)` of them, `p = k/n`. -/
theorem binKernel_lumps (n : ℕ) [NeZero n] :
    Kernel.Lumps cardFin (binKernel n) (conformistCountKernel n 1 zero_le_one le_rfl) := by
  intro I
  have hq : (Distribution.uniform (Fin n × Fin n × Fin n)).prob
      (fun s => 2 ≤ sampleCountOf I s) = conformistMap 1 ((cardFin I : ℕ) / n) := by
    rw [Distribution.prob_eq_expect, Distribution.uniform_expect, conformistMap_one]
    exact avg_Y_maj I ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  calc (binKernel n I).map cardFin
      = ((Distribution.independent fun _ : Fin n =>
            Distribution.uniform (Fin n × Fin n × Fin n)).map
          fun r v => decide (2 ≤ sampleCountOf I (r v))).map
          fun ω => Fin.cast (congrArg (· + 1) (Fintype.card_fin n))
            (countFin fun v => ω v = true) := by
        change ((Distribution.uniform (Tgt3 n)).map (ThreeMajority.step I)).map cardFin = _
        rw [uniform_tgt3_eq_independent, Distribution.map_map, Distribution.map_map]
        congr 1
        funext r
        exact Fin.ext (by
          simp [cardFin, ThreeMajority.step, ThreeMajority.sampleCount, countFin_val])
    _ = (Distribution.independent fun _ : Fin n => Distribution.bernoulli _
          ((Distribution.uniform (Fin n × Fin n × Fin n)).prob_nonneg
            fun s => 2 ≤ sampleCountOf I s)
          ((Distribution.uniform (Fin n × Fin n × Fin n)).prob_le_one
            fun s => 2 ≤ sampleCountOf I s)).map
          fun ω => Fin.cast (congrArg (· + 1) (Fintype.card_fin n))
            (countFin fun v => ω v = true) := by
        rw [Distribution.independent_map_pi _ fun _ s => decide (2 ≤ sampleCountOf I s)]
        simp only [Distribution.map_decide_eq_bernoulli]
    _ = conformistCountKernel n 1 zero_le_one le_rfl (cardFin I) := by
        rw [Distribution.independent_bernoulli_map_card (Fintype.card_fin n)]
        simp only [conformistCountKernel, hq]

end Plurality
