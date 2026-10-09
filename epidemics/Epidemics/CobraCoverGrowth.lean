import Epidemics.CobraCoverSpectral

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

/-- **Lemma 1** (Section 3; inequalities (3) to (7)). On an `r`-regular graph (`r > 0`) with
`λ = lambdaG G r`, one round of BIPS with `k ≥ 2` samples per vertex from the infected set `A`
gives `E(|A_{t+1}| ∣ A_t = A) ≥ |A| (1 + (1 - λ²)(1 - |A|/n))`. The paper assumes `G` connected,
`λ < 1` and `k = 2`; the bound holds for every regular graph, every `k ≥ 2` and every set `A`
(it need not contain the source). -/
theorem bips_expected_growth {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (v : V) (A : Finset V) :
    (A.card : ℝ) * (1 + (1 - lambdaG G r ^ 2) * (1 - A.card / Fintype.card V)) ≤
      avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) := by
  sorry

/-- **One-round moment generating function** (computation (12) in the proof of Lemma 2): the
vertices are infected independently given `A`, so for every real `φ`,
`E(e^{-φ |A'|}) = ∏ᵤ (1 - (1 - e^{-φ}) P(u ∈ A')) ≤ exp(-(1 - e^{-φ}) E|A'|)`. -/
theorem bips_mgf_le (v : V) (A : Finset V) (φ : ℝ) :
    avg (fun ρ : Choices G k => Real.exp (-φ * (bipsStep v A ρ).card)) ≤
      Real.exp (-(1 - Real.exp (-φ)) *
        avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ))) := by
  sorry

/-- **Chernoff lower tail for one BIPS round** (used in (18) of Lemma 3 and in the proof of
Lemma 4): if `μ ≤ E|A'|` and `0 < δ < 1`, then `P(|A'| ≤ (1 - δ) μ) ≤ exp(-δ² μ / 2)`. -/
theorem bips_chernoff_lower (v : V) (A : Finset V) {δ μ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμ : μ ≤ avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ))) :
    avg (fun ρ : Choices G k =>
        if ((bipsStep v A ρ).card : ℝ) ≤ (1 - δ) * μ then (1 : ℝ) else 0) ≤
      Real.exp (-(δ ^ 2 * μ / 2)) := by
  sorry

end Epidemics
