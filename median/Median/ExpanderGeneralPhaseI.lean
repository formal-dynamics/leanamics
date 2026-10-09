import Median.ExpanderGeneralDefs

/-! # Phase I: a small imbalance grows until the minority is a small fraction

The paper's Lemma 2 and Corollary 2 (Cooper, Elsässer and Radzik, ICALP 2014,
arXiv:1404.7479, Section 4). Throughout, `n = |V|`, `A = majority a x`, `B = minority a x`,
`ν = (A − B)/n` (`imbalance`) and `η = α n / √(A B)` (`phaseEta`). The common hypotheses of
the one-round lemmas are those of the proof of Lemma 2: `0 < c ≤ 1/2`, `0 < α ≤ c^{3/2}/36`,
the mixing hypothesis `MixingProp G d α c`, and `c n ≤ B ≤ A`.

* `expected_gain_ge`: `𝔼 Δ_{BA} ≥ (A² B / n²)(1 − 2η)` (the paper's (hjre21)-(be56sw)).
* `expected_loss_le`: `𝔼 Δ_{AB} ≤ (A B² / n²)(1 + 15η)` (the paper's (eq-upperOnDAB)).
* `gain_tail`: `P(Δ_{BA} ≤ (A² B / n²)(1 − 3η)) ≤ e^{−α² c n / 6}` (the paper's (eq-fger)).
* `loss_tail`: `P(Δ_{AB} ≥ (A B² / n²)(1 + 17η)) ≤ e^{−α² c² n / 2}` (the paper's (eq-fger2)).
* `phaseI_step`: with probability at least `1 − e^{−α² c n / 6} − e^{−α² c² n / 2}`, the new
  imbalance is at least `ν + ν (1 − ν²)/2 − 12 α / √(1 − ν²)` (the paper's (ncnwd-Appx)).
* `growth_small`, `growth_large`: the deterministic consequences `ν' ≥ (5/4) ν` for
  `120 α ≤ ν ≤ 1/2`, and `1 − ν' ≤ (3/4)(1 − ν)` for `1/2 ≤ ν ≤ 1 − 2c`.
* `phaseI`: the paper's Lemma 2, with `K = 120` and an explicit number of rounds: if
  `ν₀ ≥ 120 α`, then within `phaseIRounds ν₀ c` rounds the minority drops to at most `c n`,
  except with probability `phaseIRounds ν₀ c · (e^{−α² c n / 6} + e^{−α² c² n / 2})`.
* `phaseI_expander`: the paper's Corollary 2, `phaseI` for a graph with `λ_G ≤ α`.
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### One round: expectations of the two flows -/

/-- **Expected gain of the majority** (the paper's (hjre21)-(be56sw) in the proof of Lemma 2):
`𝔼 Δ_{BA} = ∑_{v ∈ B} (d_v^A / d)² ≥ E(A, B)² / (B d²) ≥ (A² B / n²)(1 − 2η)`. -/
theorem expected_gain_ge {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2
        * (1 - 2 * phaseEta α a x)
      ≤ avg (fun r : GraphRound G => (gainCount a x (graphStep G x r) : ℝ)) := by
  sorry

/-- **Expected loss of the majority** (the paper's (eq-upperOnDAB) in the proof of Lemma 2):
`𝔼 Δ_{AB} = ∑_{v ∈ A} (d_v^B / d)² ≤ (A B² / n²)(1 + 15η)`. -/
theorem expected_loss_le {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    avg (fun r : GraphRound G => (lossCount a x (graphStep G x r) : ℝ))
      ≤ (majority a x : ℝ) * (minority a x : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2
        * (1 + 15 * phaseEta α a x) := by
  sorry

/-! ### One round: concentration -/

/-- **Lower tail of the gain** (the paper's (eq-fger)):
`P(Δ_{BA} ≤ (A² B / n²)(1 − 3η)) ≤ e^{−α² c n / 6}`. -/
theorem gain_tail {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    avg (fun r : GraphRound G =>
        if (gainCount a x (graphStep G x r) : ℝ)
            ≤ (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2
              * (1 - 3 * phaseEta α a x) then (1 : ℝ) else 0)
      ≤ exp (-(α ^ 2 * c * Fintype.card V / 6)) := by
  sorry

/-- **Upper tail of the loss** (the paper's (eq-fger2)):
`P(Δ_{AB} ≥ (A B² / n²)(1 + 17η)) ≤ e^{−α² c² n / 2}`. -/
theorem loss_tail {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    avg (fun r : GraphRound G =>
        if (majority a x : ℝ) * (minority a x : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2
              * (1 + 17 * phaseEta α a x)
            ≤ (lossCount a x (graphStep G x r) : ℝ) then (1 : ℝ) else 0)
      ≤ exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2)) := by
  sorry

/-- **One round of Phase I** (the paper's (bchwc) and (ncnwd-Appx)): with probability at least
`1 − e^{−α² c n / 6} − e^{−α² c² n / 2}`, the new imbalance `ν'` satisfies
`ν' ≥ ν + ν (1 − ν²)/2 − 12 α / √(1 − ν²)`. -/
theorem phaseI_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    1 - exp (-(α ^ 2 * c * Fintype.card V / 6)) - exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2))
      ≤ avg (fun r : GraphRound G =>
          if imbalance a x + imbalance a x * (1 - imbalance a x ^ 2) / 2
                - 12 * α / √(1 - imbalance a x ^ 2)
              ≤ imbalance a (graphStep G x r) then (1 : ℝ) else 0) := by
  sorry

/-! ### The deterministic recursion -/

/-- While `120 α ≤ ν ≤ 1/2`, the recursion (ncnwd-Appx) gives `ν' ≥ (5/4) ν`. -/
theorem growth_small {α ν ν' : ℝ} (hα : 0 ≤ α) (h1 : 120 * α ≤ ν) (h2 : ν ≤ 1 / 2)
    (h : ν + ν * (1 - ν ^ 2) / 2 - 12 * α / √(1 - ν ^ 2) ≤ ν') : 5 / 4 * ν ≤ ν' := by
  have hν0 : 0 ≤ ν := by linarith
  have hs : 4 / 5 ≤ √(1 - ν ^ 2) := by
    rw [show (4 / 5 : ℝ) = √((4 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hpos : 0 < √(1 - ν ^ 2) := by linarith
  have h3 : 12 * α / √(1 - ν ^ 2) ≤ 15 * α := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have h4 : 3 / 8 * ν ≤ ν * (1 - ν ^ 2) / 2 := by nlinarith
  linarith

/-- While `1/2 ≤ ν ≤ 1 − 2c` and `α ≤ c^{3/2}/36`, the recursion (ncnwd-Appx) gives
`δ' ≤ (3/4) δ` for `δ = 1 − ν` (the paper's (ncnwd-Appx334x)). -/
theorem growth_large {c α ν ν' : ℝ} (hc : 0 < c) (hα0 : 0 ≤ α) (hα : α ≤ c * √c / 36)
    (h1 : 1 / 2 ≤ ν) (h2 : ν ≤ 1 - 2 * c)
    (h : ν + ν * (1 - ν ^ 2) / 2 - 12 * α / √(1 - ν ^ 2) ≤ ν') :
    1 - ν' ≤ 3 / 4 * (1 - ν) := by
  have hsc : 0 ≤ √c := Real.sqrt_nonneg c
  have h3 : √3 * √c ≤ √(1 - ν ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h43 : 4 / 3 ≤ √3 := by
    rw [show (4 / 3 : ℝ) = √((4 / 3) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hcpos : 0 < √c := Real.sqrt_pos.mpr hc
  have hpos : 0 < √(1 - ν ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have h5 : 48 * α ≤ c * √(1 - ν ^ 2) := by nlinarith
  have h6 : 12 * α / √(1 - ν ^ 2) ≤ c / 4 := by
    rw [div_le_iff₀ hpos]
    linarith
  have h7 : 3 / 8 * (1 - ν) ≤ ν * (1 - ν ^ 2) / 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ν by linarith) (show 0 ≤ ν * (1 + ν) - 3 / 4 by nlinarith)]
  linarith

/-! ### Lemma 2 and Corollary 2 -/

/-- **Lemma 2** (Phase I, with `K = 120`): on a `d`-regular graph satisfying the mixing
hypothesis `MixingProp G d α c` with `0 < c ≤ 1/2` and `0 < α ≤ c^{3/2}/36`, if the initial
imbalance is `ν₀ ≥ 120 α`, then within `T₁ = phaseIRounds ν₀ c` rounds the minority drops to at
most `c n` (at some time `t ≤ T₁`), except with probability at most
`T₁ (e^{−α² c n / 6} + e^{−α² c² n / 2})`. -/
theorem phaseI {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool) (hν : 120 * α ≤ imbalance a x) :
    1 - (phaseIRounds (imbalance a x) c : ℝ)
        * (exp (-(α ^ 2 * c * Fintype.card V / 6)) + exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2)))
      ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) c)
          (fun l => if ∃ t ≤ phaseIRounds (imbalance a x) c,
              (minority a (graphRun G x (l.take t)) : ℝ) ≤ c * Fintype.card V
            then (1 : ℝ) else 0) := by
  sorry

/-- **Corollary 2** (Phase I on expanders): `phaseI` for a `d`-regular graph with `λ_G ≤ α`,
through the expander mixing lemma (`mixingProp_of_lambdaG`). -/
theorem phaseI_expander {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hlam : lambdaG G d ≤ α) (a : Bool) (x : V → Bool) (hν : 120 * α ≤ imbalance a x) :
    1 - (phaseIRounds (imbalance a x) c : ℝ)
        * (exp (-(α ^ 2 * c * Fintype.card V / 6)) + exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2)))
      ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) c)
          (fun l => if ∃ t ≤ phaseIRounds (imbalance a x) c,
              (minority a (graphRun G x (l.take t)) : ℝ) ≤ c * Fintype.card V
            then (1 : ℝ) else 0) :=
  phaseI G hd hreg hc0 hc hα0 hα (mixingProp_of_lambdaG G hreg hlam c) a x hν

end Median.ExpanderGeneral
