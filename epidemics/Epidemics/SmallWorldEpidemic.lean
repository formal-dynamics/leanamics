import Epidemics.SmallWorld

/-! # Subcritical Reed–Frost epidemics on one-dimensional small-world graphs (EPI-6)

L. Becchetti, A. Clementi, R. Denni, F. Pasquale, L. Trevisan, I. Ziccardi, *Percolation and
epidemic processes in one-dimensional small-world networks*, arXiv:2103.16398 [BCDPTZ22],
Theorems 2.4 and 2.5, claim 2.

The Reed–Frost epidemic with transmission probability `p` on a sampled graph `G`, started from a
set `I₀` of sources, is `run G ω I₀` with one coin per edge, `ω ~ coins p` (EPI-1). Below the
threshold the percolation graph has only components of `O(log n)` nodes (`swg_subcritical`,
`swg3_subcritical`), so, by the deterministic lemmas of EPI-2 (`card_recovered_le`,
`infected_eq_empty_of_ncard_le`), the epidemic is over within `O(log n)` rounds after infecting
`O(|I₀| log n)` nodes, as observed in the paper (Appendix C):

* `SWG(n, c/n)`: `swg_reedFrost_subcritical` (Theorem 2.4, claim 2: below `p* − ε`);
* `3-SWG(n)`: `swg3_reedFrost_subcritical` (Theorem 2.5, claim 2, with the threshold `1/2` of
  Theorem 2.2; the paper's v3 repeats the `SWG(n, c/n)` threshold there).
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

/-- Small components stop the epidemic (deterministic, from EPI-2): if every connected
component of the percolation graph has at most `B` nodes, then the Reed–Frost epidemic from `I₀`
is over at some time `t ≤ B` and infects at most `B |I₀|` nodes in total. -/
theorem reedFrost_of_components_le {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V) {B : ℝ}
    (h : ∀ K : (perc G ω).ConnectedComponent, (K.supp.ncard : ℝ) ≤ B) :
    (∃ t : ℕ, (t : ℝ) ≤ B ∧ (run G ω I₀ t).infected = ∅) ∧
      ((run G ω I₀ (Fintype.card V)).recovered.card : ℝ) ≤ B * I₀.card := by
  have hB : 0 ≤ B := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact (Nat.cast_nonneg _).trans (h ((perc G ω).connectedComponentMk v))
  refine ⟨⟨⌊B⌋₊, Nat.floor_le hB, infected_eq_empty_of_ncard_le G ω I₀ fun u => ?_⟩, ?_⟩
  · exact Nat.le_floor (h _)
  · rw [mul_comm]
    exact card_recovered_le G ω I₀ fun u => h _

/-- **Subcritical Reed–Frost on `SWG(n, c/n)`** ([BCDPTZ22] Theorem 2.4, claim 2; Appendix C):
for every `c > 0` and `ε > 0` there are `β` and `C` such that, for `n ≥ 3`, bridge probability
`q = c / n`, transmission probability `p < p* − ε` and any set `I₀` of sources, with probability
at least `1 - C / n` the Reed–Frost epidemic from `I₀` is over (no infectious node) at some time
`t ≤ β log n`, and at most `β |I₀| log n` nodes are recovered at the end. -/
theorem swg_reedFrost_subcritical (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ β C : ℝ, ∀ n : ℕ, 3 ≤ n →
      ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1), q * n = c →
      ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1), p < swgThreshold c - ε →
      ∀ I₀ : Finset (Fin n),
        1 - C / n ≤ (coins q hq0 hq1).expect fun b => (coins p hp0 hp1).prob fun ω =>
          (∃ t : ℕ, (t : ℝ) ≤ β * Real.log n ∧ (run (swg n b) ω I₀ t).infected = ∅) ∧
            ((run (swg n b) ω I₀ n).recovered.card : ℝ) ≤ β * I₀.card * Real.log n := by
  obtain ⟨β, C, h⟩ := swg_subcritical c hc ε hε
  refine ⟨β, C, fun n hn q hq0 hq1 hq p hp0 hp1 hp I₀ => ?_⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine (h n hn q hq0 hq1 hq p hp0 hp1 hp).trans
    (Distribution.expect_mono _ fun b => Distribution.prob_mono _ fun ω hω => ?_)
  obtain ⟨h1, h2⟩ := reedFrost_of_components_le (swg n b) ω I₀ hω
  rw [Fintype.card_fin] at h2
  exact ⟨h1, h2.trans_eq (by ring)⟩

/-- **Subcritical Reed–Frost on `3-SWG(n)`** ([BCDPTZ22] Theorem 2.5, claim 2, with the
threshold `1/2` of Theorem 2.2; Appendix E): for every `ε > 0` there are `β` and `C` such that,
for even `n ≥ 4`, transmission probability `p < 1/2 − ε` and any set `I₀` of sources, with
probability at least `1 - C / n` the Reed–Frost epidemic from `I₀` is over at some time
`t ≤ β log n`, and at most `β |I₀| log n` nodes are recovered at the end. -/
theorem swg3_reedFrost_subcritical (ε : ℝ) (hε : 0 < ε) :
    ∃ β C : ℝ, ∀ n : ℕ, 4 ≤ n → ∀ hn : Even n,
      ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1), p < 1 / 2 - ε →
      ∀ I₀ : Finset (Fin n),
        1 - C / n ≤ (uniformMatching n hn).expect fun M => (coins p hp0 hp1).prob fun ω =>
          (∃ t : ℕ, (t : ℝ) ≤ β * Real.log n ∧ (run (swg3 n M) ω I₀ t).infected = ∅) ∧
            ((run (swg3 n M) ω I₀ n).recovered.card : ℝ) ≤ β * I₀.card * Real.log n := by
  obtain ⟨β, C, h⟩ := swg3_subcritical ε hε
  refine ⟨β, C, fun n hn4 hn p hp0 hp1 hp I₀ => ?_⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine (h n hn4 hn p hp0 hp1 hp).trans
    (Distribution.expect_mono _ fun M => Distribution.prob_mono _ fun ω hω => ?_)
  obtain ⟨h1, h2⟩ := reedFrost_of_components_le (swg3 n M) ω I₀ hω
  rw [Fintype.card_fin] at h2
  exact ⟨h1, h2.trans_eq (by ring)⟩

end Epidemics
