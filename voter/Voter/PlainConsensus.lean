import Voter.PlainMeeting
import Voter.MeetingConsensus

/-! # `O(n³ log n)` consensus of the plain voter on connected nonbipartite graphs (VOT-6)

Hassin–Peleg Theorem 2.5 and Survey Theorem 8 (with the nonbipartiteness hypothesis of
Hassin–Peleg §2.1), for the plain synchronous voter dynamics: every vertex copies the colour
of a uniformly random neighbour. On every connected nonbipartite graph with `n` vertices, from
every initial colouring, it reaches consensus within `O(n³ log n)` rounds with probability at
least `1 - 1/n`. The proof combines the meeting time `plain_meeting_core` with the duality and
union bound `iterate_disagreement_le_of_meeting` (Hassin–Peleg Theorem 2.4, tail form).
-/

namespace Voter
open Dynamics

universe u v

/-- **Consensus tail with explicit constant.** On a connected nonbipartite graph with `n`
vertices, after `16 k n³` rounds the plain voter dynamics has not reached consensus with
probability at most `(n − 1) 2^{-k}`, from every colouring. -/
theorem plain_disagreement_le {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hc : G.Connected) (hnb : ¬ G.Colorable 2)
    (hd : ∀ i, 0 < G.degree i) (s : Config V C) (k : ℕ) :
    (transition (uniformNeighbor G hd)).iterate (k * (16 * Fintype.card V ^ 3)) disagreement s ≤
      ((Fintype.card V : ℝ) - 1) * (1 / 2) ^ k := by
  haveI : Nonempty V := hc.nonempty
  exact iterate_disagreement_le_of_meeting _
    (fun x y => by rw [event_pairWalk]; exact plain_meeting_core hc hnb hd (x, y)) s k

/-- **Consensus within `O(n³ log n)` rounds with probability at least `1 - 1/n`** (Hassin–Peleg
Theorem 2.5; Survey Theorem 8 with the nonbipartiteness hypothesis). There is a constant
`A > 0` such that on every connected nonbipartite graph with `n` vertices (all degrees
positive), for every finite palette and every initial colouring `s`, after `T ≥ A n³ log n`
rounds the plain synchronous voter dynamics (copy a uniformly random neighbour) has not
reached consensus with probability at most `1/n`. -/
theorem plain_voter_consensus_whp :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → ¬ G.Colorable 2 →
      ∀ (hd : ∀ i, 0 < G.degree i) (C : Type v) [Fintype C] (s : Config V C) (T : ℕ),
        A * (Fintype.card V : ℝ) ^ 3 * Real.log (Fintype.card V) ≤ T →
          (transition (uniformNeighbor G hd)).iterate T disagreement s ≤
            1 / (Fintype.card V : ℝ) := by
  refine ⟨80, by norm_num, ?_⟩
  intro V _ _ G _ hc hnb hd C _ s T hT
  haveI : Nonempty V := hc.nonempty
  obtain ⟨u₀⟩ := ‹Nonempty V›
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hc16 : (0 : ℝ) < 16 * (Fintype.card V : ℝ) ^ 3 := by positivity
  -- the number of halvings of the probability of being apart
  set k : ℕ := ⌊(T : ℝ) / (16 * (Fintype.card V : ℝ) ^ 3)⌋₊ with hk_def
  have hkT : k * 16 * (Fintype.card V : ℝ) ^ 3 ≤ T := by
    have := Nat.floor_le (div_nonneg (Nat.cast_nonneg T) hc16.le)
    rw [← hk_def, le_div_iff₀ hc16] at this
    linarith
  have hk : 5 * Real.log (Fintype.card V) < k + 1 := by
    have hlt := Nat.lt_floor_add_one ((T : ℝ) / (16 * (Fintype.card V : ℝ) ^ 3))
    rw [← hk_def] at hlt
    have : 5 * Real.log (Fintype.card V) ≤ (T : ℝ) / (16 * (Fintype.card V : ℝ) ^ 3) := by
      rw [le_div_iff₀ hc16]
      linarith
    linarith
  calc (transition (uniformNeighbor G hd)).iterate T disagreement s
      ≤ ∑ v ∈ Finset.univ.erase u₀,
          (pairWalk (uniformNeighbor G hd)).event (fun p => p.1 ≠ p.2) T (v, u₀) :=
        iterate_disagreement_le_pairWalk _ s T u₀
    _ ≤ ∑ v ∈ Finset.univ.erase u₀, ((1 : ℝ) / 2) ^ k := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [event_pairWalk]
        exact plain_apart_le_pow hc hnb hd v u₀ k T hkT
    _ = ((Fintype.card V : ℝ) - 1) * (1 / 2) ^ k := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u₀), Finset.card_univ,
          nsmul_eq_mul, Nat.cast_sub hcard, Nat.cast_one]
    _ ≤ 1 / (Fintype.card V : ℝ) := card_sub_one_mul_half_pow_le hcard hk

end Voter
