import Epidemics.SmallWorldSubcritical

/-! # Subcritical percolation on one-dimensional small-world graphs (EPI-6)

L. Becchetti, A. Clementi, R. Denni, F. Pasquale, L. Trevisan, I. Ziccardi, *Percolation and
epidemic processes in one-dimensional small-world networks*, arXiv:2103.16398 [BCDPTZ22],
Theorems 2.1 and 2.2, claim 2.

Bond percolation with parameter `p` on a random one-dimensional small-world graph (definitions in
`Epidemics.SmallWorldDefs`), probabilities being taken over both the graph and the percolation:

* `SWG(n, c/n)`, threshold `p* = swgThreshold c = (√(c² + 6c + 1) − c − 1) / (2c)`:
  `swg_subcritical` (Theorem 2.1, claim 2: below `p* − ε`, all components have `O(log n)`
  nodes), from Lemma C.1 (`swg_components_small`);
* `3-SWG(n)`, threshold `1/2`: `swg3_subcritical` (Theorem 2.2, claim 2), a consequence of
  Theorem 2.3 (EPI-2's `prob_components_small`) since `3-SWG(n)` has maximum degree `3`.

The paper's "with high probability" (`≥ 1 - n^{-Ω(1)}`) is made quantitative as "with probability
at least `1 - C / n`", the rate its proofs give; `O_ε(log n)` is `β log n` (natural logarithm)
with constants depending only on `c` and `ε`, uniformly in `p`. The edge probability of the
bridges `q = c / n` is written `q * n = c` (as `p * n = 1 + ε` in EPI-3).
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

/-- **Subcritical `SWG(n, c/n)`** ([BCDPTZ22] Theorem 2.1, claim 2, proved in Appendix C,
Lemma C.1): for every `c > 0` and `ε > 0` there are `β` and `C` such that, for `n ≥ 3`, bridge
probability `q = c / n` and percolation probability `p < p* − ε`, with probability at least
`1 - C / n` over the graph `swg n b` (`b ~ coins q`) and the percolation `ω ~ coins p`, every
connected component of `perc (swg n b) ω` has at most `β log n` nodes. Here
`β = 64 / δ²` with `δ = 1 - p₀ - c p₀ (1 + p₀)`, `p₀ = p* - ε`, and `C = 2`. -/
theorem swg_subcritical (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ β C : ℝ, ∀ n : ℕ, 3 ≤ n →
      ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1), q * n = c →
      ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1), p < swgThreshold c - ε →
        1 - C / n ≤ (coins q hq0 hq1).expect fun b => (coins p hp0 hp1).prob fun ω =>
          ∀ K : (perc (swg n b) ω).ConnectedComponent,
            (K.supp.ncard : ℝ) ≤ β * Real.log n := by
  set p₀ := swgThreshold c - ε
  refine ⟨64 / (1 - p₀ - c * p₀ * (1 + p₀)) ^ 2, 2,
    fun n hn q hq0 hq1 hqn p hp0 hp1 hp => ?_⟩
  have hp₀0 : 0 ≤ p₀ := by linarith
  have hp₀1 : p₀ ≤ 1 := by linarith [swgThreshold_lt_one hc]
  have hδ : 0 < 1 - p₀ - c * p₀ * (1 + p₀) := by
    have := (lt_swgThreshold_iff hc hp₀0).mp (by linarith)
    linarith
  exact swg_components_small hp₀0 hp₀1 hδ hc.le (by omega) hq0 hq1 hqn hp0 hp1 hp.le

/-- **Subcritical `3-SWG(n)`** ([BCDPTZ22] Theorem 2.2, claim 2, a consequence of Theorem 2.3):
for every `ε > 0` there are `β` and `C` such that, for even `n ≥ 4` and percolation probability
`p < 1/2 − ε`, with probability at least `1 - C / n` over the uniformly random perfect matching
`M` and the percolation `ω ~ coins p`, every connected component of `perc (swg3 n M) ω` has at
most `β log n` nodes. -/
theorem swg3_subcritical (ε : ℝ) (hε : 0 < ε) :
    ∃ β C : ℝ, ∀ n : ℕ, 4 ≤ n → ∀ hn : Even n,
      ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1), p < 1 / 2 - ε →
        1 - C / n ≤ (uniformMatching n hn).expect fun M => (coins p hp0 hp1).prob fun ω =>
          ∀ K : (perc (swg3 n M) ω).ConnectedComponent,
            (K.supp.ncard : ℝ) ≤ β * Real.log n := by
  refine ⟨10 / (2 * ε) ^ 2, 1, fun n _ hn p hp0 hp1 hp => ?_⟩
  rcases lt_or_ge ε (1 / 2) with hε2 | hε2
  · rw [← Distribution.expect_const (uniformMatching n hn) (1 - 1 / n)]
    refine Distribution.expect_mono _ fun M => ?_
    have hM := prob_components_small (swg3 n M) (swg3_degree_le n M) hp0 hp1
      (by positivity : (0 : ℝ) < 2 * ε) (by linarith) (by push_cast; linarith)
    rwa [Fintype.card_fin] at hM
  · exact absurd hp0 (by linarith)

end Epidemics
