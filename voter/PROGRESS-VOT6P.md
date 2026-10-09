# VOT-6P: the plain walk on connected nonbipartite graphs

Roadmap VOT-6, remaining part: Hassin and Peleg's Theorem 2.5 for the **plain** synchronous
voter (every vertex copies a uniformly random neighbour) on connected nonbipartite graphs.
The lazy voter is done (`lazy_voter_consensus_whp`); the plain voter was covered only
conditionally on a meeting bound (`iterate_disagreement_le_of_meeting`). This job pins the
meeting bound and the unconditional consequence.

Sources: Y. Hassin, D. Peleg, *Distributed probabilistic polling and applications to
proportionate agreement*, Inf. Comput. 171 (2001), §2.4 (Lemma 2.4, Fact 2.3, Theorems 2.4
and 2.5); L. Becchetti, A. Clementi, E. Natale, *Consensus dynamics: an overview*, SIGACT
News 2020, Theorem 8; P. Tetali, P. Winkler, *Simultaneous reversible Markov chains* (1993);
D. Coppersmith, P. Tetali, P. Winkler, *Collisions among random walks on a graph*, SIAM J.
Discrete Math. 6 (1993).

## Status

Proving the 14 pinned `sorry`s. Order: `PlainCover.lean` (connectivity, hitting uniqueness,
layer symmetry, plain-step equations), then `PlainMeeting.lean` (additive drift and the
double-cover potential), then `PlainConsensus.lean`.

Already proved at pinning time: `doubleCover_adj`, `doubleCover_degree`,
`doubleCover_degree_pos`, `volume_doubleCover`, `plain_meeting_le_half`,
`plain_disagreement_le`.

Proved: all five `PlainCover.lean` sorries (`doubleCover_connected`, `hitting_unique`,
`hitting_doubleCover_flip`, `uniformNeighbor_expect_hitting`,
`uniformNeighbor_doubleCover_expect`). `lake build Voter.PlainCover` succeeds.
Remaining: eight sorries in `PlainMeeting.lean`, one in `PlainConsensus.lean`.
Current errors: none (`PlainCover` clean). Next: additive drift and `plainPotential_drift`.

## Pinned statements

`n = |V|`; `G̃ = doubleCover G`; `hitting` is the lazy-normalised hitting time of
`Voter/MeetingHitting.lean` (the solution of `h y = 0`, `(L h) x = 2 d_x` for `x ≠ y`),
which is twice the hitting time of the plain walk.

### `Voter/PlainCover.lean`: the bipartite double cover

| Declaration | Statement | Source |
| --- | --- | --- |
| `doubleCover` | `G̃` on `V × Bool`: `(a, i) ∼ (b, j)` iff `a ∼ b` and `i ≠ j` | HP proof of Lemma 2.4 (`h_ii = 0`) |
| `doubleCover_adj` | adjacency unfolds (proved) | |
| `doubleCover_connected` | `G` connected and not 2-colourable ⇒ `G̃` connected | HP Lemma 2.4 (implicit) |
| `doubleCover_degree` | `deg_G̃ (x, i) = deg_G x` (proved) | |
| `doubleCover_degree_pos` | positive degrees lift (proved) | |
| `volume_doubleCover` | `vol G̃ = 2 vol G` (proved) | |
| `hitting_unique` | the hitting-time system has a unique solution | |
| `hitting_doubleCover_flip` | `h̃_{(y,¬j)}(x,¬i) = h̃_{(y,j)}(x,i)`: swapping layers is an automorphism | |
| `uniformNeighbor_expect_hitting` | a plain step away from `y` lowers `hitting G hc y` by `2` in expectation | first-step equation |
| `uniformNeighbor_doubleCover_expect` | a plain step of `G̃` from `(x, i)` is a plain step of `G` from `x` with the layer flipped | |

### `Voter/PlainMeeting.lean`: the meeting bound

| Declaration | Statement | Source |
| --- | --- | --- |
| `pairWalk_apart_mul_le` | additive drift: `F ≥ 0` dropping by `c` off the diagonal ⇒ `c T · P(apart at T) ≤ F p` | (standard) |
| `plainPotential` | `Φ̃((x, 0), (y, 0))`, the Coppersmith–Tetali–Winkler potential (`meetingPotential`) of `G̃` | TW93 via HP Lemma 2.4 |
| `doubleCover_hitting_le` | every hitting time of `G̃` is `≤ 16 n³` | HP Fact 2.3 on `G̃` |
| `plainPotential_nonneg`, `plainPotential_le` | `0 ≤ plainPotential ≤ 32 n³` (with `B₀ = 16 n³`) | |
| `plainPotential_drift` | off the diagonal one synchronous plain step lowers the potential by exactly `4` | TW93 reduction in HP Lemma 2.4 |
| `plain_apart_mul_le` | connected nonbipartite ⇒ `T · P(apart at T) ≤ 8 n³` | HP Lemma 2.4, tail form |
| `plain_meeting_core` | apart after `16 n³` steps with probability `≤ 1/2` | HP Lemma 2.4 |
| `plain_apart_le_pow` | apart after `T ≥ 16 k n³` steps with probability `≤ 2^{-k}` | |
| `plain_meeting_le_half` | `∃ A > 0`, uniform over graphs: apart after `T ≥ A n³` with probability `≤ 1/2`; exactly the hypothesis `hmeet` of `iterate_disagreement_le_of_meeting` (proved from `plain_meeting_core`, `A = 16`) | HP Lemma 2.4; meeting `O(n³)` |

### `Voter/PlainConsensus.lean`: the consequence

| Declaration | Statement | Source |
| --- | --- | --- |
| `plain_disagreement_le` | no consensus after `16 k n³` rounds with probability `≤ (n − 1) 2^{-k}` (proved) | HP Theorem 2.4, tail form |
| `plain_voter_consensus_whp` | `∃ A > 0`: on every connected nonbipartite graph, every palette and colouring, no consensus after `T ≥ A n³ log n` rounds with probability `≤ 1/n` | HP Theorem 2.5; Survey Theorem 8 |

## Proof route (summary)

A simultaneous step of the two tokens at `(x, y)` is, on `G̃`, a move of the first token from
`(x, 0)` to `(x', 1)` followed by a move of the second token from `(y, 0)` to `(y', 1)`.
Between the two moves the tokens are in different layers, so they are distinct vertices of
`G̃` and the Coppersmith–Tetali–Winkler potential of `G̃` drops by `2` at each move (it would
fail on `G` itself, where adjacent tokens can swap). The layer symmetry returns the tokens to
layer `0`. With the commute bound on `G̃` (`2n` vertices, volume `≤ 2 n (n − 1)`), the
potential is at most `32 n³`, and additive drift gives the meeting bound. `G̃` is connected
exactly when `G` is connected and nonbipartite.

## Deviations from the source

* **Tail form instead of expected time** (as for the lazy walk, §4.2 of
  `FORMALIZATION_DIFFERENCES.md`): Lemma 2.4 bounds the expected meeting time `M`; we pin
  `P(apart at T) ≤ 8 n³ / T` and `≤ 1/2` at `T = 16 n³`. Theorem 2.5 bounds the expected
  consensus time; we pin `P(no consensus at T) ≤ 1/n` for `T ≥ A n³ log n` (the survey's
  "w.h.p." form).
* **Lemma 2.4 is proved through a potential on the double cover rather than by quoting
  Tetali–Winkler.** Hassin and Peleg quote "the meeting time of `G` is bounded by twice the
  hitting time of `G̃`" from Tetali and Winkler and then bound hitting times along a shortest
  path by `n · max` of adjacent commute times (Fact 2.3). We instead use the
  Coppersmith–Tetali–Winkler potential of `G̃` at the pair `((x, 0), (y, 0))`, whose exact
  drift `−4` per synchronous step (lazy-normalised units) gives the meeting bound in terms
  of the maximal hitting time of `G̃`, and we bound that by the commute bound already in the
  repository (`hitting_add_hitting_le`, path plus Cauchy–Schwarz) instead of the sum over
  a path of adjacent commute times. Both give `O(n · m) = O(n³)`.
* **Nonbipartiteness as `¬ G.Colorable 2`**, as in `Voter/Graph.lean`; positive degrees
  `hd` as in the lazy version (for a connected nonbipartite graph they hold automatically).
* **Explicit constants**: `16 n³` for meeting with probability `1/2`, `A = 16` for
  `plain_meeting_le_half`; any `A` (the route gives `A = 80`) for the consensus theorem.
* **Corrections to the sources.** The proof of Hassin–Peleg Lemma 2.4 needs a minor correction:
  it states `l ≤ Diam(G̃) ≤ n`, but the double cover has `2n` vertices and its diameter can
  be about `2n` (for a path of length `L` ending in a triangle, `n = L + 3`, the distance
  from `(x, 0)` to `(x, 1)` at the free end of the path is `2L + 3 = 2n − 3`; an exhaustive
  check shows that `2n − 3` is the maximum for `n ≤ 6`). The bound `Diam(G̃) ≤ 2n − 1` only
  changes the constant. Our route does not use the diameter of
  `G̃` (only a path in `G̃`, through `hitting_add_hitting_le`). Survey
  Theorem 8 needs a minor correction (the nonbipartiteness hypothesis), already recorded in
  `FORMALIZATION_DIFFERENCES.md` §4.1; this job formalizes the corrected statement.
