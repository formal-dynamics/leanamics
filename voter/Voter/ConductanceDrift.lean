import Voter.ConductanceDriftAux

/-! # The potential drop of the lazy voter (BGKM16, Lemma 2.1)

Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic
networks*, ICALP 2016, arXiv:1603.01895 (BGKM16). For two opinions, the volume of either opinion
is a martingale of the lazy voter, so it cannot measure progress; the concave potential
`Ψ = √vol(minority side)` drops in expectation by `∑_{u ∈ s_t} λ_u d_u / (32 Ψ³)` per round
(`potential_drift`). Bounding `∑_{u ∈ s_t} λ_u d_u ≥ d_min · φ · vol(s_t)` by the definition of
the conductance gives the drop `d_min φ / (32 Ψ)` (`potential_drift_conductance`), the form used
by the drift lemma `Dynamics.Kernel.drift_absorption` (BGKM16, Lemma 2.2).
-/

namespace Voter
open Dynamics Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Lemma 2.1 of BGKM16** (two opinions, one round of the lazy voter on `G`). If the minority
side `s_t` of the configuration `s` is nonempty, then
`𝔼[Ψ(S_{t+1}) | S_t = s_t] ≤ Ψ(s_t) - ∑_{u ∈ s_t} λ_u d_u / (32 Ψ(s_t)³)`.
The paper prints the sum over all vertices `u ∈ V`; its proof bounds the sum over `s_t`, which is
what the proof of Lemma 2.2 uses. The printed form needs this minor correction (it does not hold
on the star `K_{1,15}`, see `FORMALIZATION_DIFFERENCES.md`, §5.1). -/
theorem potential_drift (hd : ∀ v, 0 < G.degree v) (s : Config V Bool)
    (hs : (minority G s).Nonempty) :
    (transition (lazyNeighbor G hd)).apply (potential G) s ≤
      potential G s - (∑ u ∈ minority G s, (discordant G s u : ℝ) * G.degree u) /
        (32 * potential G s ^ 3) := by
  obtain ⟨b, hb⟩ := exists_minority_eq G s
  have hP0 : (0 : ℝ) < vol G (univ.filter fun u => s u = b) := by
    rw [hb] at hs
    exact_mod_cast vol_pos hd hs
  have hpot : potential G s = Real.sqrt (vol G (univ.filter fun u => s u = b)) := by
    rw [potential, hb]
  rw [transition_apply]
  unfold round
  set μ := Distribution.independent (lazyNeighbor G hd)
  -- the potential after the round is at most `√` of the new volume of opinion `b`
  have h1 : μ.expect (fun r => potential G (step s r)) ≤ μ.expect (fun r =>
      Real.sqrt (vol G (univ.filter fun u => s u = b) + ∑ u, volChange G s b u (r u))) :=
    μ.expect_mono fun r => by
      rw [← vol_class_step]
      exact potential_le_sqrt_class G (step s r) b
  -- replacement (Lemma A.1) and the Taylor bound
  have h2 := expect_sqrt_le_comp G hd s b
  have h3 : μ.expect (fun r =>
      Real.sqrt (vol G (univ.filter fun u => s u = b) + ∑ u, compVar G s b u (r u))) ≤
      μ.expect (fun r => Real.sqrt (vol G (univ.filter fun u => s u = b)) *
        (1 + (∑ u, compVar G s b u (r u)) / (2 * vol G (univ.filter fun u => s u = b)) -
          (∑ u, compVar G s b u (r u)) ^ 2 / (8 * (vol G (univ.filter fun u => s u = b) : ℝ) ^ 2) +
          (∑ u, compVar G s b u (r u)) ^ 3 /
            (16 * (vol G (univ.filter fun u => s u = b) : ℝ) ^ 3))) :=
    μ.expect_mono fun r => sqrt_add_le_taylor hP0 (by linarith [compSum_ge G s b r])
  rw [expect_taylor] at h3
  have h4 := drift_arith hP0 (expect_compSum G hd s b) (expect_compSum_sq_ge G hd s b)
    (expect_compSum_cube_le G hd s b)
  rw [hpot, hb]
  exact h1.trans (h2.trans (h3.trans h4))

/-- **The drift in terms of the conductance** (BGKM16, the inequality displayed at the start of
the proof of Lemma 2.2, for a static graph). If the minority side `s_t` of `s` is nonempty, then
`𝔼[Ψ(S_{t+1}) | S_t = s_t] ≤ Ψ(s_t) - d_min φ / (32 Ψ(s_t))`, where `d_min` is the minimum degree
and `φ` the conductance of `G`. -/
theorem potential_drift_conductance (hd : ∀ v, 0 < G.degree v) (s : Config V Bool)
    (hs : (minority G s).Nonempty) :
    (transition (lazyNeighbor G hd)).apply (potential G) s ≤
      potential G s - G.minDegree * conductance G / (32 * potential G s) := by
  refine (potential_drift G hd s hs).trans ?_
  obtain ⟨b, hb⟩ := exists_minority_eq G s
  -- `d_min φ vol(s_t) ≤ d_min |cut(s_t)| ≤ ∑_{u ∈ s_t} λ_u d_u`
  have hcut := conductance_mul_vol_le G (minority G s) (vol_pos hd hs)
    (vol_minority_le_edges G s)
  have hcs : ((G.interedges (minority G s) (minority G s)ᶜ).card : ℝ) =
      ∑ u ∈ minority G s, (discordant G s u : ℝ) := by
    rw [hb]
    exact_mod_cast card_interedges_class G s b
  have hsum : (G.minDegree : ℝ) * (conductance G * vol G (minority G s)) ≤
      ∑ u ∈ minority G s, (discordant G s u : ℝ) * G.degree u := by
    calc (G.minDegree : ℝ) * (conductance G * vol G (minority G s))
        ≤ G.minDegree * ((G.interedges (minority G s) (minority G s)ᶜ).card : ℝ) :=
          mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg _)
      _ = ∑ u ∈ minority G s, (G.minDegree : ℝ) * discordant G s u := by rw [hcs, mul_sum]
      _ ≤ ∑ u ∈ minority G s, (discordant G s u : ℝ) * G.degree u := by
          refine sum_le_sum fun u _ => ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast G.minDegree_le_degree u)
            (Nat.cast_nonneg _)
  -- divide by `32 Ψ³`, using `Ψ² = vol(s_t)`
  have hΨ : 0 < potential G s := (potential_pos_iff G hd s).mpr hs
  have hsq := potential_sq G s
  have hle : (G.minDegree : ℝ) * conductance G / (32 * potential G s) ≤
      (∑ u ∈ minority G s, (discordant G s u : ℝ) * G.degree u) / (32 * potential G s ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h32 : 0 ≤ 32 * potential G s := by positivity
    have := mul_le_mul_of_nonneg_left hsum h32
    rw [← hsq] at this
    nlinarith [this]
  linarith

end Voter
