import Epidemics.SmallWorldExplore

/-! # The percolated `SWG(n, q)` as one percolation of the complete graph (EPI-6)

Bond percolation with parameter `p` on `SWG(n, q)` ([BCDPTZ22] Definition 1.1) involves two
independent families of coins: the bridge coins `b ~ coins q` and the percolation coins
`ω ~ coins p`. A pair `{u, v}` is an edge of the percolation graph `perc (swg n b) ω` if and only
if `ω {u, v}` is open and `{u, v}` is a cycle edge or a bridge. The resulting coins
`ω {u, v} ∧ (cycle edge ∨ b {u, v})` are again independent, open with probability `p` on the
cycle edges and `p q` on the other pairs (`swgRate`), and the percolation graph is the
percolation of the complete graph with these coins (`perc_swg_eq`). Hence every event about the
percolation graph has the same probability under the two-stage law and under the collapsed law
(`expect_prob_swg_eq`). This is the independence used in the exploration of [BCDPTZ22]
Appendix C ("`Ŷ` is distributed as `Bin(|S_t|, pc/n)`").
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

variable {n : ℕ}

/-- The probability that a pair is an edge of the percolated `SWG(n, q)`: `p` for a cycle edge,
`p q` otherwise. -/
noncomputable def swgRate (n : ℕ) (p q : ℝ) (e : Sym2 (Fin n)) : ℝ := by
  classical
  exact if e ∈ (cycleGraph n).edgeSet then p else p * q

lemma swgRate_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (e : Sym2 (Fin n)) :
    0 ≤ swgRate n p q e := by
  unfold swgRate
  split_ifs
  · exact hp0
  · exact mul_nonneg hp0 hq0

lemma swgRate_le_one {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : q ≤ 1) (e : Sym2 (Fin n)) :
    swgRate n p q e ≤ 1 := by
  unfold swgRate
  split_ifs
  · exact hp1
  · nlinarith

/-- The collapsed coin of a pair: open percolation coin, and the pair is a cycle edge or an
open bridge. -/
noncomputable def swgCoin (n : ℕ) (e : Sym2 (Fin n)) (bq bp : Bool) : Bool := by
  classical
  exact bp && (decide (e ∈ (cycleGraph n).edgeSet) || bq)

/-- The percolation graph of `swg n b` is the percolation of the complete graph by the collapsed
coins. -/
lemma perc_swg_eq (b ω : Sym2 (Fin n) → Bool) :
    perc (swg n b) ω = perc ⊤ (fun e => swgCoin n e (b e) (ω e)) := by
  ext u v
  simp only [perc, swg, sup_adj, top_adj, swgCoin, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, mem_edgeSet]
  constructor
  · rintro ⟨h | ⟨h, hb⟩, hω⟩
    · exact ⟨h.ne, hω, Or.inl h⟩
    · exact ⟨h, hω, Or.inr hb⟩
  · rintro ⟨h, hω, hc | hb⟩
    · exact ⟨Or.inl hc, hω⟩
    · exact ⟨Or.inr ⟨h, hb⟩, hω⟩

/-- **The collapsed law**: for every event `E` on graphs, its probability for the percolation
graph of `SWG(n, q)` (over the bridges and the percolation) equals its probability for the
percolation of the complete graph with independent coins of probability `swgRate n p q`. -/
theorem expect_prob_swg_eq {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (E : SimpleGraph (Fin n) → Prop) :
    ((coins q hq0 hq1).expect fun b => (coins p hp0 hp1).prob fun ω => E (perc (swg n b) ω)) =
      (Distribution.independent fun e => Distribution.bernoulli (swgRate n p q e)
        (swgRate_nonneg hp0 hq0 e) (swgRate_le_one hp0 hp1 hq1 e)).prob
        (fun ω => E (perc ⊤ ω)) := by
  classical
  simp_rw [Distribution.prob_eq_expect, perc_swg_eq]
  refine expect_expect_coord (fun _ => bernoulli q hq0 hq1) (fun _ => bernoulli p hp0 hp1) _
    (swgCoin n) (fun e c => ?_) (fun z => if E (perc ⊤ z) then 1 else 0)
  simp only [Distribution.bernoulli, bernoulli, swgRate, swgCoin, Fintype.sum_bool]
  by_cases he : e ∈ (cycleGraph n).edgeSet <;> cases c <;> simp [he] <;> ring

end Epidemics
