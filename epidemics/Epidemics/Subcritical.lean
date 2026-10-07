import Epidemics.ReedFrost
import Epidemics.SubcriticalWhp

/-! # Subcritical percolation and small outbreaks (EPI-2)

Becchetti, Clementi, Denni, Pasquale, Trevisan, Ziccardi, *Percolation and epidemic processes in
one-dimensional small-world networks* ([BCDPTZ22], arXiv:2103.16398), Theorem 2.3 and its proof,
Theorem E.1.

Let the degrees of a finite graph `G` be at most `d`, and percolate `G` with independent
Bernoulli(`p`) coins (`coins`, from EPI-1), where `p (d - 1) ≤ 1 - ε`. Explore the cluster of a
vertex `s` (its connected component in `perc G ω`) one vertex at a time. The first `t` steps
examine at most `t (d - 1) + 1` edges, each for the first time, and the cluster has more than `t`
vertices only if at least `t` of them are open. By the principle of deferred decisions, the
cluster size is dominated by a binomial tail, which a Chernoff bound turns into
`exp (ε - ε² t / 2)`; a union bound over `s` gives clusters of at most `(10 / ε²) log n` vertices
with probability at least `1 - 1/n`.

Corollaries:
* by the pathwise Reed–Frost ⇔ percolation coupling (EPI-1), a Reed–Frost epidemic with
  `R₀ = p (d - 1) ≤ 1 - ε` infects at most `|I₀| (10 / ε²) log n` nodes and is over within
  `(10 / ε²) log n` rounds, with probability at least `1 - 1/n`;
* every component of the Erdős–Rényi graph `G(n, c/n)` with `c ≤ 1 - ε` (bond percolation on the
  complete graph) has at most `(10 / ε²) log n` vertices, with probability at least `1 - 1/n`.

Component sizes are measured as in Mathlib, by `K.supp.ncard`.
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Deferred decisions** (the proof of [BCDPTZ22, Theorem E.1]): if the degrees of `G` are at
most `d`, the cluster of `s` in the percolated graph has more than `t` vertices with probability at
most that of at least `t` successes in `t (d - 1) + 1` independent Bernoulli(`p`) trials. -/
theorem prob_cluster_gt_le_binomial (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdeg : ∀ v, G.degree v ≤ d) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (s : V) (t : ℕ) :
    (coins p h0 h1).prob (fun ω => t < ((perc G ω).connectedComponentMk s).supp.ncard) ≤
      (Distribution.independent fun _ : Fin (t * (d - 1) + 1) => bernoulli p h0 h1).prob
        (fun ξ => t ≤ (univ.filter fun i => ξ i = true).card) := by
  exact prob_cluster_gt_le_binTail h0 h1 hdeg s t

/-- **Theorem E.1, first part** ([BCDPTZ22]): if the degrees of `G` are at most `d` and
`p (d - 1) ≤ 1 - ε` with `0 < ε < 1`, the cluster of any vertex `s` in the percolated graph has
more than `t` vertices with probability at most `exp (ε - ε² t / 2)`. -/
theorem prob_cluster_gt_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdeg : ∀ v, G.degree v ≤ d) {p ε : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hp : p * ((d : ℝ) - 1) ≤ 1 - ε) (s : V) (t : ℕ) :
    (coins p h0 h1).prob (fun ω => t < ((perc G ω).connectedComponentMk s).supp.ncard) ≤
      Real.exp (ε - ε ^ 2 * t / 2) := by
  exact (prob_cluster_gt_le_binomial G hdeg h0 h1 s t).trans (binomial_tail_le h0 h1 hε hε1 hp t)

/-- **Theorem 2.3** ([BCDPTZ22]; Theorem E.1, second part): if the degrees of `G` are at most `d`
and `p (d - 1) ≤ 1 - ε` with `0 < ε < 1`, then with probability at least `1 - 1/n` every connected
component of the percolated graph has at most `(10 / ε²) log n` vertices, where `n = |V|`. -/
theorem prob_components_small (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdeg : ∀ v, G.degree v ≤ d) {p ε : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hp : p * ((d : ℝ) - 1) ≤ 1 - ε) :
    1 - 1 / (Fintype.card V : ℝ) ≤
      (coins p h0 h1).prob fun ω => ∀ K : (perc G ω).ConnectedComponent,
        (K.supp.ncard : ℝ) ≤ 10 / ε ^ 2 * Real.log (Fintype.card V) := by
  have hL : 0 ≤ 10 / ε ^ 2 * Real.log (Fintype.card V) :=
    mul_nonneg (by positivity) (Real.log_natCast_nonneg _)
  have hwhp := prob_components_le_of_tail G h0 h1 hL fun s =>
    prob_cluster_gt_le G hdeg h0 h1 hε hε1 hp s _
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hn | hn
  · obtain h | h : Fintype.card V = 0 ∨ Fintype.card V = 1 := by omega
    · -- no vertex: `1 - 1/0 = 1`, and there is no component
      refine le_trans (le_of_eq ?_) hwhp
      rw [h]
      simp
    · -- one vertex: the bound is `0`
      calc 1 - 1 / (Fintype.card V : ℝ) = 0 := by rw [h]; norm_num
        _ ≤ _ := Distribution.prob_nonneg _ _
  · exact le_trans (by linarith [card_mul_exp_le hn hε hε1]) hwhp

/-- **Subcritical Reed–Frost** (the bounded-degree statement whose formal version [BCDPTZ22]
omits after Theorem 2.5; compare claim 2 of Theorems 2.4 and 2.5): if the degrees of `G` are at
most `d` and the reproduction number `R₀ = p (d - 1)` is at most `1 - ε` with `0 < ε < 1`, then
with probability at least `1 - 1/n` the epidemic started from `I₀` infects at most
`|I₀| (10 / ε²) log n` nodes in total, and nobody is infected in round `⌊(10 / ε²) log n⌋`: the
epidemic is over by then. -/
theorem reedFrost_subcritical (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdeg : ∀ v, G.degree v ≤ d) {p ε : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hR₀ : p * ((d : ℝ) - 1) ≤ 1 - ε) (I₀ : Finset V) :
    1 - 1 / (Fintype.card V : ℝ) ≤
      (coins p h0 h1).prob fun ω =>
        ((run G ω I₀ (Fintype.card V)).recovered.card : ℝ) ≤
            I₀.card * (10 / ε ^ 2 * Real.log (Fintype.card V)) ∧
          (run G ω I₀ ⌊10 / ε ^ 2 * Real.log (Fintype.card V)⌋₊).infected = ∅ := by
  refine (prob_components_small G hdeg h0 h1 hε hε1 hR₀).trans
    (prob_mono _ fun ω hω => ⟨?_, ?_⟩)
  · exact card_recovered_le G ω I₀ fun u => hω _
  · exact infected_eq_empty_of_ncard_le G ω I₀ fun u => Nat.le_floor (hω _)

/-- **Subcritical Erdős–Rényi graphs** (Theorem 2.3 for the complete graph): if `c ≤ 1 - ε` with
`0 < ε < 1`, then with probability at least `1 - 1/n` every connected component of `G(n, c/n)`
has at most `(10 / ε²) log n` vertices. -/
theorem erdosRenyi_subcritical {c ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hc : c ≤ 1 - ε)
    (h0 : 0 ≤ c / Fintype.card V) (h1 : c / Fintype.card V ≤ 1) :
    1 - 1 / (Fintype.card V : ℝ) ≤
      (coins (V := V) (c / Fintype.card V) h0 h1).prob fun ω =>
        ∀ K : (perc (⊤ : SimpleGraph V) ω).ConnectedComponent,
          (K.supp.ncard : ℝ) ≤ 10 / ε ^ 2 * Real.log (Fintype.card V) := by
  have hdeg (v : V) : (⊤ : SimpleGraph V).degree v ≤ Fintype.card V - 1 :=
    (complete_graph_degree v).le
  refine prob_components_small ⊤ hdeg h0 h1 hε hε1 ?_
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · rw [hn]
    simp only [Nat.cast_zero, div_zero, zero_mul]
    linarith
  · have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    rw [Nat.cast_sub hn, Nat.cast_one]
    calc c / Fintype.card V * ((Fintype.card V : ℝ) - 1 - 1)
        ≤ c / Fintype.card V * Fintype.card V := mul_le_mul_of_nonneg_left (by linarith) h0
      _ = c := div_mul_cancel₀ c hnR.ne'
      _ ≤ 1 - ε := hc

end Epidemics
