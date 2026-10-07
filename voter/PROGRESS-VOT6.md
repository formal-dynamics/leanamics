# VOT-6 progress: `O(n³ log n)` voter consensus on every connected graph

Roadmap row VOT-6 (Survey Thm 8; Hassin–Peleg Thm 2.5), building on VOT-3
(`Voter/Coalescence.lean`: `runRounds_eq_comp`, `disagreement_runRounds_le`, `voter_consensus_whp`).

## Status

* **Phase 1 (pin statements): done.** `lake build Voter` succeeds; the only warnings are the five
  `declaration uses 'sorry'` of the pinned theorems below. `PINNED.txt` (repository root) lists them.
* **Phase 2 (proofs): done.** All five pinned theorems are proved; `lake build Voter` is
  warning-free; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for every
  pinned declaration (also via `python3 ../scripts/check_axioms.py`, 25 declarations, after
  adding the five theorems to `Audit.lean`). Pinned text up to `:=` unchanged.

## Pinned (frozen up to `:=`)

| File | Declaration | Content |
| --- | --- | --- |
| `Voter/Meeting.lean` | `pairWalk` (def) | two tokens driven by the common rounds `r ~ Distribution.independent H`, token at `x` moves to `r x` (Survey Def. 5 with two tokens; diagonal absorbing, independent off it) |
| `Voter/Meeting.lean` | `iterate_disagreement_le_pairWalk` | any kernel `H`: `P(no consensus at T) ≤ ∑_{v ≠ u₀} P(tokens from (v, u₀) apart at T)` (duality, Survey Thm 6, plus union bound) |
| `Voter/Meeting.lean` | `iterate_disagreement_le_of_meeting` | any kernel `H`: if `P(apart at T₀) ≤ 1/2` from every pair, then `P(no consensus at k T₀) ≤ (n - 1) 2^{-k}` (HP Thm 2.4, tail form) |
| `Voter/MeetingTime.lean` | `lazyNeighbor` (def) | lazy uniform-neighbour kernel: self w.p. `1/2`, else uniform neighbour (built on `uniformNeighbor`) |
| `Voter/MeetingTime.lean` | `lazy_meeting_le_half` | `∃ A > 0`, every connected graph (positive degrees), every `x y`, `T ≥ A n³ → P(lazy walks not met by T) ≤ 1/2` (HP Fact 2.3 + Lemma 2.4, lazy uniform case) |
| `Voter/MeetingTime.lean` | `lazy_meeting_le_pow` | same with `T ≥ k A n³ → ≤ 2^{-k}` |
| `Voter/MeetingConsensus.lean` | `lazy_voter_consensus_whp` | `∃ A > 0`, every connected graph (positive degrees), every finite palette and colouring `s`, `T ≥ A n³ log n → P(no consensus at T) ≤ 1/n` (HP Thm 2.5; Survey Thm 8) |

Probabilities: `Kernel.event` / `Kernel.iterate` (dynamics API); nonconsensus: VOT-3's
`disagreement`; graph notions: Mathlib `SimpleGraph.Connected`, `SimpleGraph.degree`.

## Proved

All pinned theorems, with explicit constants inside the `∃`:

| Theorem | Witness / proof |
| --- | --- |
| `iterate_disagreement_le_pairWalk` | `iterate_project` to start from `id : Config V V`; VOT-3's `disagreement_runRounds_le s [B] u₀` pointwise; `iterate_transition_eq_leftRounds` (time reversal) and `iterate_leftRounds_pair` (projection to two vertices) |
| `iterate_disagreement_le_of_meeting` | the above plus `pairWalk_iterate_outside_mul_le` (submultiplicativity, diagonal absorbing) |
| `lazy_meeting_le_half` | `A = 51`: `lazy_meeting_core` (apart after `3 (16 n³ + 1) ≤ 51 n³` steps w.p. `≤ 1/2`) and `pairWalk_iterate_outside_antitone` |
| `lazy_meeting_le_pow` | `A = 51`: `lazy_apart_le_pow` (core lemma plus submultiplicativity) |
| `lazy_voter_consensus_whp` | `A = 255`: `k = ⌊T / (51 n³)⌋`, union bound `iterate_disagreement_le_pairWalk`, `lazy_apart_le_pow`, and `card_sub_one_mul_half_pow_le` (`(n − 1) 2^{-k} ≤ 1/n` once `k + 1 > 5 log n`) |

## Remaining

Nothing for VOT-6. Optional strengthenings (not pinned): the literature constant `A = 16` for the
meeting bound (our commute bound loses a factor `2` over darts, and the `3/4`-per-block step
loses more); an expected-time version of Theorem 2.5; HP's plain walk on nonbipartite graphs.

## Errors / obstacles

* Hassin–Peleg's PDF could not be retrieved: ScienceDirect, CORE and the Elsevier API block
  unauthenticated scripted access (Cloudflare / bot challenge / API key). See "Sources".
* Phase 2: no statement turned out false; only routine Lean fixes (imports, `omit`, casts under
  `set`).

## Proof structure (as realized)

Files (all in `voter/Voter/`, imported through `MeetingConsensus` from `Voter.lean`):

| File | Lines | Content |
| --- | --- | --- |
| `MeetingRounds.lean` | 127 | generic: `kernel_iterate_expect`, `kernel_iterate_finset_sum`, `independent_expect_pair` (two coordinates of an independent product are independent), `leftRounds`, `iterate_transition_eq_leftRounds` (time reversal of i.i.d. rounds) |
| `Meeting.lean` | 217 | `pairWalk` (pinned) and its API: `event_pairWalk`, `pairWalk_apply_diag`, `pairWalk_apply_of_ne`, diagonal absorbing, antitone, `pairWalk_iterate_outside_mul_le`, `iterate_leftRounds_pair`; T1, T2 |
| `MeetingDrift.lean` | 176 | any lazy kernel: `seqSurvival` (sequential walks), `seqSurvival_mul_le` (potential ⇒ `T · s_T ≤ F`), `iterate_outside_succ_le` (KMS Prop. B.9: `z_{T+1} ≤ (apart + s_T)/2`), `iterate_outside_le_three_quarters` |
| `MeetingHitting.lean` | 249 | graph Laplacian (Mathlib `lapMatrix`): maximum principle `le_zero_of_lapMatrix_le` (reuses `boundary_edge`), `exists_hitting`/`hitting`, `hitting_nonneg`, `hitting_lapMatrix_apply`, `hitting_symm` (`E_x T_y − E_y T_x = E_π T_y − E_π T_x`), `hitting_add_hitting_le` (commute bound `≤ 4 vol (n − 1)`, energy identity `lapMatrix_toLinearMap₂'` plus Cauchy–Schwarz along a path) |
| `MeetingTime.lean` | 268 | `lazyNeighbor` (pinned), `lazyNeighbor_expect`, `lazyNeighbor_expect_hitting`, `meetingPotential` and its drifts, `lazy_meeting_core`, `lazy_apart_le_pow`; T3, T4 |
| `MeetingConsensus.lean` | 92 | `card_sub_one_mul_half_pow_le`; T5 |

Differences from the phase-1 plan: hitting times exist by linear algebra (injective ⇒
surjective) rather than as limits; the potential is `h_y(x) − E_π T_y + B₀` with the
reversibility identity proved from the symmetry of `L`, so neither the hidden vertex nor the
cycle identity is needed; the finite drift lemma takes the form `T · s_T ≤ F` (no sums); the
voter-side monotonicity in `T` was not needed (T5 uses T1 and the pair bound at time `T`
directly).

Documentation updated: `README.md` (table and scope), `FORMALIZATION_DIFFERENCES.md` §1.2,
blueprint section "Section 2.4 on connected graphs", `Audit.lean`.

## Deviations from the sources

1. **Lazy walk instead of Hassin–Peleg's plain walk on nonbipartite graphs.** HP's standing
   hypotheses (§2.1) are a connected *nonbipartite* graph, no self-loops, and Thm 2.5 is the
   uniform case `H_ij = 1/d_i`. The survey's Thm 8 claims the bound for *any* connected graph,
   which is false for the plain synchronous walk on bipartite graphs (tokens on opposite sides
   never meet; cf. `Voter.Examples.twoVertex_never_consensus`). We pin the lazy kernel (self
   w.p. `1/2`, else uniform neighbour), for three reasons:
   (a) it lies within HP's weighted-polling framework with self-loops (their Remark after
   Thm 2.1; PropCon weights `H_ii = 1 − d_i/R̃_i` and, inferred from row sums, `H_ij = 1/R̃_i`, with
   `R̃_i = 2 d_i`);
   (b) it makes the survey's "every connected graph" true;
   (c) it is the setting of Cooper–Elsässer–Ono–Radzik (2013), who say this is equivalent to
   vertices choosing their own opinion w.p. 1/2, and of Kanade–Mallmann-Trenn–Sauerwald (2019),
   where `t_meet ≤ 4 t_hit` has a clean proof (Prop. B.9).
   I know of no comparably clean proof of an `O(n³)` synchronous meeting bound for the plain
   walk on nonbipartite graphs, and HP's own Lemma 2.4 text was unavailable. Its model is
   still covered *conditionally*: `iterate_disagreement_le_of_meeting` holds for every kernel
   `H`. Exact meeting times computed numerically (`/tmp` scripts, not in the repo) on paths,
   stars, lollipops, barbells and near-bipartite graphs up to `n = 48`: lazy `≤ 0.06 n³`,
   self-loop `≤ 0.04 n³`, plain `≤ 0.08 n³` on nonbipartite graphs, infinite on bipartite ones.
2. **Lazy rather than self-loop model, and VOT-3's `K_n` model is not a special case.** VOT-3
   uses Wright–Fisher sampling (uniform over all vertices, the complete graph with self-loops).
   The self-loop generalization (uniform over the closed neighbourhood) would contain it, but
   its holding probability `1/(d+1)` breaks the constant-factor coupling of KMS Prop. B.9. So
   the lazy kernel was chosen for provability; `lazyNeighbor ⊤ ≠ wfKernel`.
3. **High-probability form instead of expected time.** HP's Thm 2.4/2.5 bound the expected
   consensus time (`O(M log n)`, `O(n³ log n)`; as read by Cooper et al. and KMS). We pin
   `P(no consensus at T) ≤ 1/n` for `T ≥ A n³ log n` (task requirement; Survey Thm 8's
   "w.h.p." form). The meeting time is likewise a tail bound (`≤ 1/2` at `A n³`) instead of an
   expected meeting time `M = O(n³)`; the two agree up to constants (Markov's inequality,
   geometric trials).
4. **Existential constants** (`∃ A > 0`, uniform over all graphs, vertex types of a fixed
   universe and palettes) rendering `O(·)`. The proofs use `A = 51` (meeting) and `A = 255`
   (consensus); the literature route gives `A = 16` for the meeting bound.
5. **Two tokens as a coalescing pair driven by common rounds** (`pairWalk`, Survey Def. 5 with
   two tokens) instead of two independent walks with a path event "never met up to `T`".
   Before meeting the two are independent (distinct coordinates of `Distribution.independent H`),
   and the diagonal is absorbing, so "apart at time `T`" is exactly "not met within `T` steps".
6. **Positive-degree hypothesis** `hd : ∀ i, 0 < G.degree i`, needed to normalize the kernel
   (as for the existing `uniformNeighbor`). For a connected graph it only excludes `n = 1`,
   where consensus is trivial.
7. **Arbitrary finite palette** (survey: `n` colours; HP: two colours, reduced from `k`).
8. **Hassin–Peleg's hypotheses taken from secondary sources.** See "Sources".

## Sources

* Survey: Becchetti, Clementi, Natale, *Consensus dynamics: an overview*, SIGACT News 51(1)
  2020, preprint `hal-02507613` (read in full: Def. 3 is the asynchronous voter, but Thms 6–8
  follow the synchronous [HP01] line; Thm 7 uses the complete graph with self-loops; Thm 8:
  "Let G be any connected undirected graph. Starting from an arbitrary initial configuration c
  on G, the Voter dynamics reaches consensus w.h.p. in O(n³ log n) rounds.", citing [TW93] for
  meeting times).
* Hassin–Peleg, Inform. and Comput. 171 (2001), DOI 10.1006/inco.2001.3088: **not retrieved**.
  Hypotheses and numbering from `voter/FORMALIZATION_DIFFERENCES.md` (written from the paper:
  §2.1 standing hypotheses; §2.4 Fact 2.3 `Z_ij + Z_ji ≤ 1/(π_i h_ij)`, Lemma 2.4
  `M = O(n Z_max)`, Prop. 2.1 Chernoff, Thm 2.4 `O(M log n)`, Thm 2.5 `O(n³ log n)` uniform
  case; PropCon weights) and from Cooper–Elsässer–Ono–Radzik ("Hassin and Peleg showed that the
  voting is completed in expected O(n³ log n) time on any connected graph").
* Kanade, Mallmann-Trenn, Sauerwald, *On coalescence time in graphs*, arXiv:1611.02460
  (lazy walks throughout; `t_coal = O(t_meet log n)` "appears implicitly in [HP01]";
  Prop. B.9 `t_meet ≤ 4 t_hit`).
