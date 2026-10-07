import Epidemics.SubcriticalExploration

/-! # From one cluster to all components: the union bound (EPI-2)

The "furthermore" part of Theorem E.1 of Becchetti, Clementi, Denni, Pasquale, Trevisan,
Ziccardi, *Percolation and epidemic processes in one-dimensional small-world networks*
(arXiv:2103.16398): a tail bound `β` for the cluster of every vertex gives, by a union bound over
the vertices (every component is the component of one of its vertices), probability at least
`1 - n β` that all components are small. The scalar lemma `card_mul_exp_le` checks that the
choice `(10 / ε²) log n` makes `n β ≤ 1 / n` for the tail `β = exp (ε - ε² t / 2)`.
-/

namespace Epidemics
open Finset Dynamics SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Union bound over the components**: if the cluster of every vertex has more than `⌊L⌋₊`
vertices with probability at most `β`, then all components have at most `L` vertices with
probability at least `1 - n β`. -/
theorem prob_components_le_of_tail (G : SimpleGraph V) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {L β : ℝ} (hL : 0 ≤ L)
    (htail : ∀ s : V,
      (coins p h0 h1).prob (fun ω => ⌊L⌋₊ < ((perc G ω).connectedComponentMk s).supp.ncard) ≤ β) :
    1 - Fintype.card V * β ≤
      (coins p h0 h1).prob fun ω => ∀ K : (perc G ω).ConnectedComponent,
        (K.supp.ncard : ℝ) ≤ L := by
  have hbad : (coins p h0 h1).prob (fun ω => ¬∀ K : (perc G ω).ConnectedComponent,
      (K.supp.ncard : ℝ) ≤ L) ≤ Fintype.card V * β := by
    calc _ ≤ (coins p h0 h1).prob
          (fun ω => ∃ s ∈ (univ : Finset V),
            ⌊L⌋₊ < ((perc G ω).connectedComponentMk s).supp.ncard) := by
          refine Distribution.prob_mono _ fun ω hω => ?_
          push Not at hω
          obtain ⟨K, hK⟩ := hω
          obtain ⟨s, rfl⟩ := K.exists_rep
          exact ⟨s, mem_univ s, (Nat.floor_lt hL).mpr hK⟩
      _ ≤ ∑ s : V, (coins p h0 h1).prob
          (fun ω => ⌊L⌋₊ < ((perc G ω).connectedComponentMk s).supp.ncard) :=
          prob_exists_le_sum _ _ _
      _ ≤ ∑ _s : V, β := sum_le_sum fun s _ => htail s
      _ = Fintype.card V * β := by rw [sum_const, card_univ, nsmul_eq_mul]
  linarith [prob_not (coins p h0 h1)
    (fun ω => ∀ K : (perc G ω).ConnectedComponent, (K.supp.ncard : ℝ) ≤ L)]

/-- The union-bound arithmetic: for `n ≥ 2` and `0 < ε < 1`, the tail `exp (ε - ε² t / 2)` at
`t = ⌊(10 / ε²) log n⌋` is at most `1 / n²`. -/
lemma card_mul_exp_le {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (n : ℝ) * Real.exp (ε - ε ^ 2 * (⌊10 / ε ^ 2 * Real.log n⌋₊ : ℕ) / 2) ≤ 1 / n := by
  set L := 10 / ε ^ 2 * Real.log n with hL
  set k := ⌊L⌋₊
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog2 : (0.6931471803 : ℝ) < Real.log n :=
    Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hε2 : 0 < ε ^ 2 := by positivity
  have hεL : ε ^ 2 * L = 10 * Real.log n := by
    rw [hL]
    field_simp
  have hk : ε ^ 2 * L < ε ^ 2 * k + ε ^ 2 := by
    have := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one L) hε2
    linarith
  have hεε : ε ^ 2 ≤ ε := by nlinarith
  have hexp : Real.log n + (ε - ε ^ 2 * k / 2) ≤ -Real.log n := by nlinarith
  calc (n : ℝ) * Real.exp (ε - ε ^ 2 * k / 2)
      = Real.exp (Real.log n + (ε - ε ^ 2 * k / 2)) := by
        rw [Real.exp_add, Real.exp_log hnpos]
    _ ≤ Real.exp (-Real.log n) := Real.exp_le_exp.mpr hexp
    _ = 1 / n := by rw [Real.exp_neg, Real.exp_log hnpos, one_div]

end Epidemics
