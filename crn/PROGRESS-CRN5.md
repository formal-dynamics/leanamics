# CRN-5: deterministic population protocols for exact majority and plurality (progress)

Source: L. Gąsieniec, D. Hamilton, R. Martin, P. G. Spirakis, G. Stachowiak, *Deterministic
population protocols for exact majority and plurality*, OPODIS 2016, LIPIcs 70, Article 14
(doi 10.4230/LIPIcs.OPODIS.2016.14), cited as [GHMSS16]. No longer version with more detailed
proofs was found; the conference version is the reference.

Status: **statements pinned** (phase 1). Proved so far: the infrastructure lemmas
(`stablyComputesWith_output_iff`, `StablyMarks.map`, `StablyComputesWith.map`,
`card_staticState`, `StaticState.δ_weight`, `DynState.weight_ofWeight`, `DynState.δ_weight`,
`card_dynState`, `Protocol.gReaches_const_iff`, `DynInv.input`, `absMajority_eq_some_iff`,
`card_absState`, `isGroupWinner_zero_iff`, `card_relState_level`, `card_relState`).
Remaining: 20 `sorry`s, listed below.

The transition functions of the Lean definitions (P₁, P₂, the recolouring, Absolute-Majority for
`k = 1` with its outputs, Relative-Majority for `k = 2` with its outputs; 74,894 table entries)
were evaluated and compared with an independent model, on which the stable-computation property
was checked exhaustively (reachability on multisets of states): P₁ for all inputs with `n ≤ 7`,
P₂ with arbitrary interleavings of interactions and colour changes for `n ≤ 6`, Absolute-Majority
for `k = 1, n ≤ 5` and `k = 2, n ≤ 4`, Relative-Majority for `k = 1, n ≤ 5`, `k = 2, n ≤ 5` and
`k = 3, n ≤ 3`.
The duel lemma (`duel_wins_iff`) was checked for all count vectors with entries `≤ 2` (`k ≤ 2`)
and `≤ 1` (`k = 3`).

## Files

| File | Content |
| --- | --- |
| `Crn/ExactMajorityOutput.lean` | stable computation with outputs in any type, and marking (`StablyMarks`) |
| `Crn/ExactMajorityStatic.lean` | Section 2: the static protocol `P₁`, Lemmas 1–2, Theorem 3 |
| `Crn/ExactMajorityDynamic.lean` | Section 3: the dynamic protocol `P₂`, its invariants, Lemmas 4–5, stabilization |
| `Crn/ExactMajorityCompose.lean` | the composition step: `P₂` driven by another protocol (`Protocol.drive`) |
| `Crn/ExactMajorityAbsolute.lean` | Section 4: Absolute-Majority, Theorem 6 |
| `Crn/ExactMajorityRelative.lean` | Section 5: Relative-Majority, Theorem 7 |

## Pinned statements

Notation: colours are `k`-bit labels `L : Fin k → Bool` (`Label k`), bits read as `±1`
(`bitSign`); `x : Label k → ℕ` is the input count vector; `n ≥ 1` agents; the scheduler is fair, in
the reachability form of `StableBasic.lean` (CRN-3). `StablyMarks P O g`: from every configuration
reachable from the initial one, a configuration is reachable from which every agent `v` forever
outputs `O(state) = g x (ι v)` (`ι v` its input); `StablyComputesWith P O f` is the case where
`g x _ = f x`.

| Declaration | Paper | Statement | Status |
| --- | --- | --- | --- |
| `Protocol.StablyMarks`, `Protocol.StablyComputesWith`, `Protocol.OutputStableAt` | Section 1 (model) | stable computation with outputs in any type, possibly depending on the agent's input | definitions |
| `stablyComputesWith_output_iff` | | with the protocol's `Bool` output, `StablyComputesWith` is CRN-3's `StablyComputes` | proved |
| `StaticState`, `StaticState.δ`, `staticMajority` | Section 2, Figs. 1–2 | the 6-state protocol `P₁` | definitions |
| `StaticState.weight_sum_eq` | Lemma 1 | the weight sum equals the colour sum along every execution | sorry |
| `StaticState.absWeight_sum_step_le` | Lemma 2 (first part) | `R = ∑ |w|` does not increase | sorry |
| `StaticState.exists_reaches_absWeight_sum_eq` | Lemma 2 (second part) | `R = |∑ colours|` is reachable | sorry |
| `staticMajority_stablyComputes` | Theorem 3 | `P₁` stably computes `sign(#1 − #(−1))` (`0` for a tie) | sorry |
| `DynState`, `DynState.δ`, `DynState.recolour`, `dynamicMajority` | Section 3, Figs. 3–4 | the 8-state protocol `P₂` and the state change forced by a colour change | definitions |
| `Protocol.GStep`, `Protocol.GReaches` | Section 5 (groups) | steps between agents of the same group | definitions |
| `DynInv` | Section 3, invariants 1–2 | per group: colour sum = weight sum; `|w − c| ≤ 1`; a strong state in each group | definition |
| `DynInv.input` | | the initial configuration `[c_a]` satisfies `DynInv` | proved |
| `DynInv.gstep` | Lemma 4 (interactions) | interactions inside groups preserve `DynInv` | sorry |
| `DynInv.recolour` | Lemma 4 (external force) | a colour change with `recolour` preserves `DynInv` | sorry |
| `DynState.absWeight_sum_gstep_le` | Lemma 5 (first part) | `R` does not increase | sorry |
| `DynState.exists_greaches_noOpposite` | Lemma 5 (second part) | a configuration without opposite weights in a group is reachable | sorry |
| `DynInv.exists_stable` | Section 3, after Lemma 5 | from `DynInv`, a configuration is reachable from which every agent forever outputs the sign of its group's colour sum | sorry |
| `DynExtStep`, `dynamicMajority_stabilizes` | Section 3 | after any finite interleaving of interactions and colour changes, `P₂` stabilizes on the sign of the final colour sum | sorry |
| `dynamicMajority_stablyComputes` | Section 3 | without the force, `P₂` stably computes `sign(#1 − #(−1))` | sorry |
| `Protocol.drive` | Sections 4–5 (composition) | `P₂` driven by a protocol `D` through colours `col : Q → SignType`, inside groups `grp`, with recolouring in the same encounter | definition |
| `Protocol.drive_dynInv` | Lemma 4 for the composition | along every execution of `D.drive`, `DynInv` holds for the derived colours | sorry |
| `Protocol.drive_stablyMarks` | proofs of Theorems 6–7 | if `D` stably marks the agents with their eventual colours, `D.drive` stably marks them with the sign of their group's eventual colour sum | sorry |
| `bitsProtocol`, `majBit` | Section 4 (memory (1)–(2)) | `k` copies of `P₁` on the bits, and the majority bits | definitions |
| `bitsProtocol_stablyMarks` | Section 4 | the copies of `P₁` stably compute the `k` majority bits | sorry |
| `absColour`, `absoluteMajority`, `absOutput`, `IsAbsMajority`, `absMajority`, `absTarget` | Section 4.1 | Algorithm Absolute-Majority, its output, the specification | definitions |
| `absMajority_eq_some_iff` | | `absMajority x = some L ↔ 2·x_L > n` | proved |
| `absTarget_sum_sign_eq_one_iff` | proof of Theorem 6 | the eventual colour sum of `P₂` is positive iff an absolute majority exists | sorry |
| `majBit_eq_of_isAbsMajority` | proof of Theorem 6 | the majority bits of an absolute majority colour are its bits | sorry |
| `absoluteMajority_stablyComputes` | Theorem 6 | all agents eventually output `some L` (`L` held by more than half of the agents) or `none` | sorry |
| `card_absState` | Theorem 6 (space) | `2^k · 6^k · 8 ≤ 2^(4k+3)` states | proved |
| `RelState`, `RelState.label`, `RelState.won`, `stageColour`, `relativeMajorityLevel`, `relativeMajority` | Section 5.1 | Algorithm Relative-Majority as `k` nested `drive`s | definitions |
| `IsGroupWinner`, `IsPlurality`, `duelColour`, `wins`, `bitAt`, `prefixMask` | Section 5 | the specification (most frequent, ties to the lexicographically largest label) | definitions |
| `duel_wins_iff` | proof of Theorem 7, one stage | the stage-`i` duel selects the winner of the prefix group | sorry |
| `isGroupWinner_zero_iff` | | the winner of the whole population is the plurality colour | proved |
| `relativeMajority_level_stablyMarks` | proof of Theorem 7 (induction) | level `m ≤ k` stably marks each agent with whether it wins its group of prefix length `k − m` | sorry |
| `relativeMajority_stablyMarks` | Theorem 7 | every agent eventually knows whether its colour is the plurality colour | sorry |
| `card_relState_level`, `card_relState` | Theorem 7 (space) | `2^k · 8^k = 2^(4k)` states | proved |

## Deviations from the source

1. **Outputs.** CRN-3's `StablyComputes` has `Bool` outputs, read through the protocol's `output`
   field. Theorem 3 outputs a sign, Theorem 6 a colour or none, and the protocol of Theorem 7
   *marks* the agents (each agent learns whether its own colour wins, not the winner's label).
   `StablyMarks` (new, `ExactMajorityOutput.lean`) reads the outputs through a separate map and
   allows targets depending on the agent's input; for the `Bool` output it is `StablyComputes`
   (`stablyComputesWith_output_iff`). The transitions and reachability are CRN-3's.
2. **Colours.** The `C ≤ 2^k` colours are the `k`-bit labels (`Label k`); a population with fewer
   colours leaves some labels unused (count `0`). The paper's `±1` reading of bits is `bitSign`.
3. **Dynamic inputs.** The external force of Section 3 is modelled without changing the protocol
   framework: since the interaction table of `P₂` does not read the colours, the colours are a
   separate assignment `col` linked to the states by the invariants (`DynInv`); a colour change is
   a separate step (`DynExtStep`), and `dynamicMajority_stabilizes` covers every finite interleaving
   of interactions and changes. In the compositions the force is internal: the colour is a function
   of the driver's state, and the recolouring happens in the encounter that changes it
   (`Protocol.drive`), as the paper assumes that a colour does not change during an interaction
   of `P₂`.
4. **Fig. 4 needs a minor correction.** The prose rules of Section 3 are formalized. The table of
   Fig. 4 differs from them in five entries. Four are harmless (`[2]` meeting `[−1]` gives
   `[1], ⟨1⟩` instead of `[1], [0]`, symmetrically for `[−2]`, `[1]`: same weights). The entry for
   the initiator `[1]` meeting the responder `[0]`, printed `(⟨1⟩, [1])`, moves the weight to the
   `[0]` agent and breaks Invariant 2 (`|w(s_a) − c_a| ≤ 1`): an agent of colour `−1` in state
   `[0]` (reachable, e.g. after `[−1]` meets `[1]`) gets `[1]`, and a later change of its colour to
   `1` asks for the nonexistent state `[3]`. With the printed table, Absolute-Majority reaches this
   situation already for `k = 2` and the four colours `00, 00, 01, 01`. The text's
   `([1], ⟨1⟩)` is used.
5. **A third invariant; the final argument of Section 3 needs a minor correction.** `DynInv` adds
   that every group contains a strong state. The paper's final argument in Section 3 uses it in the
   tie case ("the last entity that reached state `[0]`") without stating it, and Invariants 1–2
   alone do not suffice (colours all `0` with states `⟨1⟩, ⟨−1⟩` satisfy them and never change); the
   third invariant holds initially and is preserved (an interaction never removes the last strong
   state, and a colour change makes a state strong), so the conclusion stands.
6. **Absolute-Majority.** The colour of an agent for `P₂` is `1` iff every copy `P₁(i)` currently
   reports the agent's own bit `l[i]` (the paper: "the contents of `s[i]` and `l[i]` reflect the
   initial setting"); a reported tie (`0`) counts as inconsistent. The output is `some L*` (the
   reported majority bits) if `P₂` reports `1`, and `none` otherwise; a colour held by exactly half
   of the agents is not an absolute majority (`P₂` then reports a tie).
7. **Relative-Majority.** The colours `c[i]` are derived from the label and the states of the stages
   `> i` instead of being stored, so that a change propagates to all lower stages within the same
   encounter (Stabilisation Stage 2). This saves the `k` bits of `c`: `2^k · 8^k = 2^(4k)` states.
   The protocol is the `k`-fold iteration of `Protocol.drive` (level `m` holds the stages
   `k − 1, …, k − m`), so that the proof of Theorem 7 is an induction on levels, each step being
   the composition theorem plus the duel lemma. Stage `k − 1` uses `P₂` with constant colours (the
   paper writes `P₁(k − 1)` in Stabilisation Stage 1 and `P₂(k − 1)` in the proof; both work).
   Ties are broken in favour of the lexicographically largest label, bit `0` first and `−1 < 1`:
   this is the paper's own specification (Section 5: "the colour with the latest in the
   lexicographical order label") and what its protocol does (Stabilisation Stage 2: on a tie the
   agents with `c[i] = 1` win), not a modelling choice; only the reading of `l[0]` as the most
   significant bit is implicit in the paper.
8. **What Theorem 7 delivers (and what it does not).** Theorem 7 is formalized in the sense of
   Section 5: the protocol of Section 5.1 *marks* the agents of the winning colour, i.e. eventually
   and forever every agent outputs whether its own colour is the winner (the most frequent colour,
   the lexicographically largest among several). It is not plurality consensus in the sense of all
   agents outputting the winner's label: Section 1.2's "all nodes learn about the most frequent
   colour with the largest label" needs an additional dissemination layer, which the paper does not
   give and which is not formalized. Section 1.2's "all most frequent colours eventually become
   aware of their dominance" is not what Section 5.1 does either: among several most frequent
   colours only the lexicographically largest is marked, the others lose a tie at some stage.
9. **Section 5.2 (uniqueness) needs a major correction and is not formalized.** Rule (2) sets the
   bit `c'` of a potential winner to `1` when it sees a tie, and only losers can reset it (rule
   (4)). A tie seen before the stages stabilize then persists: for `k = 1` and colours `1, 1, −1`,
   the `−1`-agent must eventually annihilate with one of the `1`-agents, which then reports `[0]`
   (a tie) and keeps `c' = 1` forever, while the other `1`-agent stays in `[1]` and keeps
   `c' = 0`; the loser's bit then changes forever (rules (3) and (4)). So the mechanism of
   Section 5.2 never stabilizes on this input, in any execution (checked exhaustively: none of the
   25 reachable configurations is output-stable for `c'`), and the claim that all entities are
   eventually informed does not hold as stated. A repaired rule, checked exhaustively for
   `k = 1, n ≤ 5` and `k = 2, n ≤ 4`: a potential winner recomputes `c'` from its current stage
   reports (`1` iff one of the stages it currently wins is a tie), and losers copy `c'` from
   potential winners. Section 5.1 and Theorem 7 do not depend on Section 5.2.
10. **Typos.** In the proof of Theorem 7, "let `i > k − 1`" should read `i < k − 1`; in the proof
    of Theorem 6, "instances of `P`" and "`P(2)`" should read `P₁` and `P₂`, and "`l(i)`" should
    read `l[i]`.
11. **Space.** The paper claims `O(k)` bits; the pinned bounds are exact state counts:
    `2^k · 6^k · 8 ≤ 2^(4k+3)` (Absolute-Majority) and `2^(4k)` (Relative-Majority).

## Draft ROADMAP row (not yet in ROADMAP.md)

| CRN-5 | **Exact majority and plurality with `O(log C)`-bit deterministic protocols.** With `C ≤ 2^k` colours as `k`-bit labels: the static majority protocol with tie reports, the dynamic majority protocol tolerating finitely many input changes by an external force, and their composition (a dynamic majority protocol driven by another protocol) give population protocols that stably compute the absolute majority colour or its absence (`2^k·6^k·8` states) and mark the agents of the plurality colour (ties to the lexicographically largest label; `2^(4k)` states). Purely combinatorial (fair executions in reachability form), on CRN-3's framework; Fig. 4 of the paper needs a minor correction, and the uniqueness mechanism of its Section 5.2 (not formalized) a major one. | Gąsieniec, Hamilton, Martin, Spirakis, Stachowiak, OPODIS 2016 (Lemmas 1–5, Theorems 3, 6, 7) | CRN-3 | M–L | open |
