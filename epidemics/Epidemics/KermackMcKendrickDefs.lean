import Mathlib

/-! # The Kermack–McKendrick SIR model: definitions (EPI-7)

The deterministic SIR epidemic of Kermack and McKendrick (Proc. R. Soc. A 115, 1927), in the
normalized form of Hethcote (*The mathematics of infectious diseases*, SIAM Review 42, 2000,
system (2.2)): the fractions `s, i, r` of susceptible, infected and recovered individuals evolve by

  `s' = -β s i`,  `i' = β s i - γ i`,  `r' = γ i`,

with contact rate `β > 0` and recovery rate `γ > 0`. The basic reproduction number (Hethcote's
contact number `σ`) is `R₀ = β / γ`.

A solution is taken as a hypothesis (it is not constructed): `IsSolution β γ s i r` says that
`t ↦ (s t, i t, r t)` is an integral curve of the vector field `sirField β γ` on `[0, ∞)`, in the
sense of Mathlib's `IsIntegralCurveOn` (derivatives within `[0, ∞)`, so one-sided at `0`), and that
it starts from `s(0), i(0) > 0`, `r(0) = 0` and `s(0) + i(0) + r(0) = 1`.
-/

namespace Epidemics.KermackMcKendrick

/-- The basic reproduction number `R₀ = β / γ` (Hethcote's contact number `σ = β / γ`). -/
noncomputable def R₀ (β γ : ℝ) : ℝ := β / γ

/-- The Kermack–McKendrick vector field `(s, i, r) ↦ (-β s i, β s i - γ i, γ i)` on `ℝ × ℝ × ℝ`
(Hethcote 2000, system (2.2), with `r' = γ i`). -/
def sirField (β γ : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-(β * x.1 * x.2.1), β * x.1 * x.2.1 - γ * x.2.1, γ * x.2.1)

/-- The standing hypotheses of the Kermack–McKendrick SIR model (Hethcote 2000, §2.3, with
`r(0) = 0`): positive rates `β, γ`; `t ↦ (s t, i t, r t)` solves `s' = -β s i`, `i' = β s i - γ i`,
`r' = γ i` on `[0, ∞)` (an integral curve of `sirField β γ` on `Set.Ici 0`, with one-sided
derivatives at `0`); and the initial state has `s(0), i(0) > 0`, `r(0) = 0`,
`s(0) + i(0) + r(0) = 1`. -/
structure IsSolution (β γ : ℝ) (s i r : ℝ → ℝ) : Prop where
  /-- The contact rate is positive. -/
  beta_pos : 0 < β
  /-- The recovery rate is positive. -/
  gamma_pos : 0 < γ
  /-- `(s, i, r)` solves the SIR system on `[0, ∞)`. -/
  isIntegralCurveOn :
    IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Set.Ici 0)
  /-- Some individuals are initially susceptible. -/
  s_zero_pos : 0 < s 0
  /-- Some individuals are initially infected. -/
  i_zero_pos : 0 < i 0
  /-- Nobody has initially recovered. -/
  r_zero : r 0 = 0
  /-- The three fractions initially sum to one. -/
  sum_zero : s 0 + i 0 + r 0 = 1

end Epidemics.KermackMcKendrick
