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
  sorry

end Voter
