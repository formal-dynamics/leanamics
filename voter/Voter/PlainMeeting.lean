import Voter.PlainCover

/-! # Meeting time of two plain random walks on a connected nonbipartite graph (VOT-6)

Hassin–Peleg Lemma 2.4 and Fact 2.3 (uniform case), for the plain walk: on a connected
nonbipartite graph with `n` vertices, two synchronous (simultaneous) uniform-neighbour random
walks are apart after `T` steps with probability at most `8 n³ / T`, from every pair of start
vertices; hence they meet within `16 n³` steps with probability at least `1/2`. This is the
hypothesis `hmeet` of `iterate_disagreement_le_of_meeting`.

*Why the lazy argument does not apply.* For the plain walk two adjacent tokens can swap
without meeting, so the Coppersmith–Tetali–Winkler potential of `Voter/MeetingTime.lean` read
on `G` has no drift at adjacent pairs, and the synchronous-versus-sequential comparison of
`Voter/MeetingDrift.lean` needs laziness.

*Route (Hassin–Peleg's reduction to the double cover `G̃`, following Tetali and Winkler).* A
simultaneous step of the two tokens at `(x, y)` is, on `G̃ = doubleCover G`, a step of the
first token from `(x, 0)` to `(x', 1)` followed by a step of the second token from `(y, 0)` to
`(y', 1)`. Between the two moves the tokens lie in different layers of `G̃`, hence are never
equal there. So the Coppersmith–Tetali–Winkler potential `Φ` of `G̃` (`meetingPotential`)
drops by `2` at each of the two moves whenever `x ≠ y`, by the hitting-time equations of `G̃`
(connected by `doubleCover_connected`), and the layer symmetry `hitting_doubleCover_flip`
brings the tokens back to layer `0`. The potential `plainPotential (x, y) = Φ((x, 0), (y, 0))`
thus drops by exactly `4` per synchronous step off the diagonal (`plainPotential_drift`), and
the commute bound `hitting_add_hitting_le` on `G̃` (`2n` vertices, volume `2 vol G ≤ 2 n²`)
bounds it by `32 n³`. The additive drift lemma `pairWalk_apart_mul_le` gives
`4 T · P(apart at T) ≤ 32 n³`.
-/

namespace Voter
open Dynamics Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Additive drift for the two-token walk.** If a nonnegative potential `F` drops by at least
`c` in expectation under one step of the two-token walk from every pair of distinct vertices,
then `c T · P(apart after T steps) ≤ F p`. -/
lemma pairWalk_apart_mul_le (H : Kernel V) (F : V × V → ℝ) (hF : ∀ p, 0 ≤ F p) {c : ℝ}
    (hdrift : ∀ x y, x ≠ y → (pairWalk H).apply F (x, y) ≤ F (x, y) - c) (T : ℕ)
    (p : V × V) :
    c * T * (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) p ≤ F p := by
  sorry

section Plain
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The meeting potential of two plain walks at `(x, y)`: the Coppersmith–Tetali–Winkler
potential `Φ` of the double cover `G̃` (`meetingPotential`, built from the hitting times of
`G̃`) at `((x, 0), (y, 0))`. -/
noncomputable def plainPotential (hc' : (doubleCover G).Connected) (B₀ : ℝ) (p : V × V) : ℝ :=
  meetingPotential hc' B₀ ((p.1, false), (p.2, false))

/-- **Hitting times of the double cover** (Hassin–Peleg Fact 2.3 on `G̃`, via the commute
bound): every hitting time of `G̃` is at most `16 n³`, where `n = |V|`. -/
lemma doubleCover_hitting_le (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (u v : V × Bool) :
    hitting (doubleCover G) hc' v u ≤ 16 * (Fintype.card V : ℝ) ^ 3 := by
  sorry

/-- The plain meeting potential is nonnegative. -/
lemma plainPotential_nonneg (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (p : V × V) : 0 ≤ plainPotential hc' (16 * (Fintype.card V : ℝ) ^ 3) p := by
  sorry

/-- The plain meeting potential is at most `32 n³`. -/
lemma plainPotential_le (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (p : V × V) :
    plainPotential hc' (16 * (Fintype.card V : ℝ) ^ 3) p ≤ 32 * (Fintype.card V : ℝ) ^ 3 := by
  sorry

/-- **Drift of the plain meeting potential** (the Tetali–Winkler reduction in Hassin–Peleg's
proof of Lemma 2.4). Off the diagonal, one synchronous step of two plain uniform-neighbour
walks lowers the potential by exactly `4` in expectation (`2` per token, in the
lazy-normalised units of `hitting`). -/
lemma plainPotential_drift (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (B₀ : ℝ) {x y : V} (hxy : x ≠ y) :
    (pairWalk (uniformNeighbor G hd)).apply (plainPotential hc' B₀) (x, y) =
      plainPotential hc' B₀ (x, y) - 4 := by
  sorry

/-- **Meeting tail, Markov form.** On a connected nonbipartite graph with `n` vertices, two
synchronous plain random walks started at `p` are apart after `T` steps with probability `P`
satisfying `T · P ≤ 8 n³`. -/
theorem plain_apart_mul_le (hc : G.Connected) (hnb : ¬ G.Colorable 2)
    (hd : ∀ i, 0 < G.degree i) (T : ℕ) (p : V × V) :
    (T : ℝ) * (pairWalk (uniformNeighbor G hd)).iterate T (Kernel.outside (Set.diagonal V)) p ≤
      8 * (Fintype.card V : ℝ) ^ 3 := by
  sorry

/-- **Meeting time with explicit constant** (Hassin–Peleg Lemma 2.4, uniform case:
`M = O(n · 2m) = O(n³)`, tail form). On a connected nonbipartite graph with `n` vertices, two
synchronous plain random walks are apart after `16 n³` steps with probability at most `1/2`,
from every pair of start vertices. -/
theorem plain_meeting_core (hc : G.Connected) (hnb : ¬ G.Colorable 2)
    (hd : ∀ i, 0 < G.degree i) (p : V × V) :
    (pairWalk (uniformNeighbor G hd)).iterate (16 * Fintype.card V ^ 3)
      (Kernel.outside (Set.diagonal V)) p ≤ 1 / 2 := by
  sorry

/-- **Iterated meeting time with explicit constant.** On a connected nonbipartite graph with
`n` vertices, two synchronous plain random walks are apart after `T ≥ 16 k n³` steps with
probability at most `2^{-k}`. -/
theorem plain_apart_le_pow (hc : G.Connected) (hnb : ¬ G.Colorable 2)
    (hd : ∀ i, 0 < G.degree i) (x y : V) (k T : ℕ)
    (hT : k * 16 * (Fintype.card V : ℝ) ^ 3 ≤ T) :
    (pairWalk (uniformNeighbor G hd)).iterate T (Kernel.outside (Set.diagonal V)) (x, y) ≤
      (1 / 2) ^ k := by
  sorry

end Plain

/-- **Meeting time of two plain walks** (Hassin–Peleg Lemma 2.4 with Fact 2.3, uniform case;
Tetali–Winkler). There is a constant `A > 0` such that on every connected nonbipartite graph
with `n` vertices (all degrees positive), from every pair of start vertices `x, y`, two
synchronous plain uniform-neighbour random walks have not met after `T ≥ A n³` steps with
probability at most `1/2`. This is exactly the hypothesis of
`iterate_disagreement_le_of_meeting` for `H = uniformNeighbor G hd`. -/
theorem plain_meeting_le_half :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → ¬ G.Colorable 2 →
      ∀ (hd : ∀ i, 0 < G.degree i) (x y : V) (T : ℕ), A * (Fintype.card V : ℝ) ^ 3 ≤ T →
        (pairWalk (uniformNeighbor G hd)).event (fun p => p.1 ≠ p.2) T (x, y) ≤ 1 / 2 := by
  refine ⟨16, by norm_num, ?_⟩
  intro V _ _ G _ hc hnb hd x y T hT
  rw [event_pairWalk]
  have hT₀ : 16 * Fintype.card V ^ 3 ≤ T := by exact_mod_cast hT
  exact (pairWalk_iterate_outside_antitone _ (x, y) hT₀).trans
    (plain_meeting_core hc hnb hd (x, y))

end Voter
