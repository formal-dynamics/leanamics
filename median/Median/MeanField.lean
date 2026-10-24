import Median.TwoChoicesDefs
import Dynamics.MajorityMap

/-! # Synchronous 2-Choices and the binary median rule: the mean-field map

With two values, one synchronous round of the median rule (`Median.kernel n Bool`), which is
2-Choices with two colours (`TwoChoices.kernel_bool`), maps the fraction `p` of nodes holding
`true` to `3p² - 2p³` in expectation (`kernel_meanField`: `expected_ones` stated as a
`Dynamics.Kernel.MeanField`). This is the majority map
`Dynamics.majorityMap`, the mean-field map of binary 3-Majority (`Plurality.binKernel_meanField`):
the two dynamics share their mean-field map, but not their chains, since a node keeps its own
opinion unless its two samples agree, while under 3-Majority it ignores its own opinion (from two
nodes, one holding `true`, one round leaves exactly one `true` with probability `5/8` under
2-Choices and `1/2` under 3-Majority; row `two-choices` of the cross-field dictionary).
-/

namespace Median
open Dynamics

/-- **The mean-field map of the binary median rule is the majority map.** One synchronous round
maps the fraction `p` of nodes holding `true` to `3p² - 2p³` in expectation. -/
theorem kernel_meanField (n : ℕ) [NeZero n] :
    (kernel n Bool).MeanField (fun x (_ : Unit) => (ones x : ℝ) / n)
      fun u _ => majorityMap (u ()) := by
  intro x _
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp only [kernel, Kernel.apply_ofStep, div_eq_mul_inv, mul_comm _ (n : ℝ)⁻¹, avg_const_mul]
  rw [expected_ones x]
  unfold majorityMap
  field_simp

namespace TwoChoices

/-- With two colours, 2-Choices is the median rule, as a kernel. -/
theorem kernel_bool (n : ℕ) [NeZero n] : kernel n Bool = Median.kernel n Bool := by
  have h : (step : Config n Bool → Round n → Config n Bool) = Median.step :=
    funext fun x => funext fun r => step_bool x r
  simp only [kernel, Median.kernel, h]

end TwoChoices
end Median
