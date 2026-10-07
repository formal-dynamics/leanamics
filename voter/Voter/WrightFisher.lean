import Voter.LazyLoop
import Voter.Coalescence

/-! # Neutral Wright–Fisher fixation (VOT-2)

Neutral Wright–Fisher with `n` labelled individuals: every individual of the next generation
picks a uniformly random parent in the current generation, itself included, and inherits its
allele. This is the synchronous voter with kernel `wfKernel V`, i.e. on the complete graph
`K_n` with self-loops; its stationary distribution is uniform. Allele `a` therefore fixes with
probability `c_a / n`, where `c_a` is its initial number of copies.

For `n ≥ 3` the complete graph is nonbipartite, so this is a corollary of Hassin–Peleg
Section 2.3 (`color_consensus_probability` on `⊤`). For every `n ≥ 1` it follows from the
self-loop version `color_consensus_probability_of_selfLoop` (Remark, p. 254).
-/

namespace Voter
open Dynamics Finset
variable {V C : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Every parent is sampled with positive probability `1/n` under Wright–Fisher sampling. -/
lemma wfKernel_pos [Nonempty V] (i j : V) : 0 < (wfKernel V i).weight j := by
  change 0 < (Fintype.card V : ℝ)⁻¹
  exact inv_pos.mpr card_cast_pos

omit [DecidableEq V] in
/-- The uniform distribution is stationary for Wright–Fisher sampling. -/
lemma wfKernel_stationary [Nonempty V] : (wfKernel V).Stationary (Distribution.uniform V) := by
  intro b
  simp only [wfKernel, ← Finset.sum_mul, (Distribution.uniform V).sum_one, one_mul]

omit [DecidableEq V] in
/-- Under the uniform distribution an event has probability its count over `n`. -/
lemma uniform_prob_eq_card [Nonempty V] (P : V → Prop) [DecidablePred P] :
    (Distribution.uniform V).prob P = ((univ.filter P).card : ℝ) / Fintype.card V := by
  unfold Distribution.prob
  rw [Distribution.uniform_expect]
  convert avg_indicator P

omit [DecidableEq V] in
/-- The complete graph on at least three vertices is not bipartite. -/
lemma top_not_colorable_two (hn : 3 ≤ Fintype.card V) : ¬ (⊤ : SimpleGraph V).Colorable 2 := by
  intro h
  have := h.card_le_of_pairwise_adj (fun i : V => i) (fun _ _ hij => hij)
  rw [Nat.card_eq_fintype_card] at this
  omega

/-- **Neutral Wright–Fisher fixation on `K_n`, `n ≥ 3` (VOT-2), via Hassin–Peleg Section 2.3.**
In a population of `n = |V| ≥ 3` individuals, allele `a` eventually fixes with probability
`c_a / n`, where `c_a` is the number of individuals initially carrying `a`. -/
theorem wrightFisher_fixation_of_three_le [Nonempty V] [Fintype C] [DecidableEq C]
    (hn : 3 ≤ Fintype.card V) (s : Config V C) (a : C) :
    eventualColor (wfKernel V) a s =
      ((univ.filter fun i => s i = a).card : ℝ) / Fintype.card V := by
  rw [color_consensus_probability ⊤ SimpleGraph.connected_top (top_not_colorable_two hn)
    (wfKernel V) (fun i j _ => wfKernel_pos i j) _ wfKernel_stationary, uniform_prob_eq_card]

/-- **Neutral Wright–Fisher fixation for every population size (VOT-2), via the Remark on
p. 254 of Hassin–Peleg.** Allele `a` eventually fixes with probability `c_a / n`. -/
theorem wrightFisher_fixation [Nonempty V] [Fintype C] [DecidableEq C]
    (s : Config V C) (a : C) :
    eventualColor (wfKernel V) a s =
      ((univ.filter fun i => s i = a).card : ℝ) / Fintype.card V := by
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [color_consensus_probability_of_selfLoop ⊤ SimpleGraph.connected_top (wfKernel V)
    (fun i j _ => wfKernel_pos i j) ⟨v, wfKernel_pos v v⟩ _ wfKernel_stationary,
    uniform_prob_eq_card]

end Voter
