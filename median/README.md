# The median dynamics and 2-Choices

Doerr, Goldberg, Minder, Sauerwald and Scheideler, *Stabilizing consensus with the power of two
choices* (SPAA 2011): every node holds a value from a linearly ordered set and, every round,
adopts the median of its own value and the values of two nodes sampled uniformly at random (with
replacement). With two values this is the 2-Choices dynamics.
Theorem and lemma numbers follow the 2009 version of the paper (Dagstuhl Seminar Proceedings 09371); in the
SPAA 2011 proceedings, Theorem 1 is Theorem 1.1 and Theorem 21 is Theorem 4.1, and the lemmas
are numbered differently.

**Main results** (namespace `Median`):

| Result | Lean declaration |
| --- | --- |
| The median commutes with monotone maps; thresholding the process gives the binary median process, for the same samples | `med3_monotone`, `threshold_step`, `threshold_run` |
| Validity (new values are current values), range, consensus fixed points | `step_mem`, `step_mem_Icc`, `step_of_consensus` |
| Binary case: one round maps the fraction `p` of `true` to `3p² − 2p³` in expectation | `expected_ones` |
| Almost-sure consensus | `absorbed` |
| 2-Choices from a gap of `128 √(n log n)`: all nodes hold the majority value after `⌈128 log n⌉` rounds w.p. `≥ 1 − 128/n`, for `log n ≥ 128` | `consensus_whp` (in [`Median/Binary.lean`](Median/Binary.lean)), via `binary_consensus` |
| 2-Choices from any start (possibly perfectly balanced): consensus after `⌈C log n⌉` rounds w.p. `≥ 1 − C/n`, for `log n ≥ C` (`C = 2¹⁸`) | `binary_any_start` (in [`Median/AnyStart.lean`](Median/AnyStart.lean)) |
| Reduction to two values: if every binary configuration fails within `T` rounds w.p. `≤ ε`, a configuration with `m` distinct values fails w.p. `≤ (m − 1) ε` | `consensus_of_binary` |
| **Theorem 1** (no adversary): from any configuration, with any number of values, consensus after `⌈C log n⌉` rounds w.p. `≥ 1 − C/n`, for `log n ≥ C` | `median_consensus_any` (`C = 3·2¹⁸ + 3`) |
| **Theorem 1 with the adversary, two values** (2-Choices; Theorem 10 of the 2009 version): against any adaptive adversary recolouring at most `F ≤ √n/C` nodes per round, from any binary configuration, all but `C (F + log n)` nodes hold the same value at every time from `⌈C log n⌉` to `⌈C log n⌉ + H`, except w.p. `≤ (C log n + H)/n²`, for `log n ≥ C` (`C = 2²⁰`) | `binary_almost_stable`, `binary_almost_stable_of_isAdvRun` (in [`Median/Adversary.lean`](Median/Adversary.lean)) |
| **Theorem 1 with the adversary** (SPAA 2011: Theorem 1.1; 2009 version: Theorems 2, 3 and 20): with `m` legal values and an adversary writing legal values only, the same almost stable consensus, except w.p. `≤ (m − 1)(C log n + H)/n²` | `median_almost_stable` |
| 2-Choices from a gap `Δ ≥ C √(n log n)`: consensus on the majority after `⌈C (log (n/Δ) + log log n)⌉` rounds w.p. `≥ 1 − C/n`, for `log n ≥ C` (`C = 128`) | `binary_consensus_fast` (in [`Median/ManyValues.lean`](Median/ManyValues.lean)) |
| Many values: a margin `Δ ≥ C √(n log n)` on both sides of a value `v` gives consensus on `v` after `⌈C (log (n/Δ) + log log n)⌉` rounds w.p. `≥ 1 − 2C/n` | `median_consensus_fast` |
| **Theorem 21, odd case** (equal supports): `2k+1` values held by `n/(2k+1)` nodes each, `C (2k+1) √(n log n) ≤ n`: the middle value wins after `⌈C (log (2k+1) + log log n)⌉` rounds w.p. `≥ 1 − C/n` | `odd_split_consensus` (`C = 256`) |

The thresholds `log n ≥ 128` (`n ≥ e¹²⁸`), `log n ≥ 256`, `log n ≥ 2¹⁸`,
`log n ≥ 3·2¹⁸ + 3` and `log n ≥ 2²⁰` come from the crude constants of the phase and drift arguments (see [PROVENANCE.md](../PROVENANCE.md) and roadmap MAJ-11). Where the
statements and proofs deviate from the paper is listed in
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

**Provenance.** For the results up to `consensus_whp`, the statements were written and pinned by
a second agent; the proofs were produced by
GLM-5.3 (on the Mistral API, driven by Mistral Vibe) under the fixed-statement protocol and
verified mechanically (statements unchanged, no placeholders, warning-free build, axiom audit).
For the results against an adaptive adversary (`Median/Adversary*.lean`), the statements were
fixed by a Claude agent and reviewed by a second agent before the proofs (the review led to the set `S` of legal
values in `median_almost_stable`, which also covers a corruption before the first round); the
proofs are by a Claude agent (Opus) under the fixed-statement protocol. See
[PROVENANCE.md](../PROVENANCE.md) for the other results.

## Two-sample voting on expanders

Cooper, Elsässer and Radzik, *The power of two choices in distributed voting* (ICALP 2014,
[arXiv:1404.7479](https://arxiv.org/abs/1404.7479)): on a graph, every vertex samples two
neighbours independently and uniformly at random (with replacement) and adopts their opinion if
the two samples agree. With two opinions this is the median rule with the samples restricted to
the neighbourhood (`graphStep`, `graphStep_bool`); rounds are pairs of the core's
`Dynamics.NeighborRound`. On a `d`-regular graph, `λ_G = max {λ₂, |λₙ|}` is computed from
Mathlib's sorted eigenvalues of the transition matrix `P = A/d` (`lambdaG`), and `E(S, T)` counts
ordered adjacent pairs (`edgeCount`). In [`Median/Expander.lean`](Median/Expander.lean):

| Result | Lean declaration |
| --- | --- |
| Expander mixing lemma (the paper's Lemma 3): `\|E(S, T) − d\|S\|\|T\|/n\| ≤ λ_G d √(\|S\|\|T\|)` on every `d`-regular graph | `expander_mixing` |
| Sets of at most `εn` vertices span at most `(3/10) d \|S\|` edges when `λ_G ≤ 3/5 − ε` | `sparse_of_lambdaG` |
| One round with a sparse minority `B` (the paper's Lemma 5 at `α = 3/10`): `𝔼\|B'\| ≤ (24/25)\|B\|`, and `\|B'\| ≤ (49/50)\|B\|` w.p. `≥ 1 − e^{−\|B\|/4850}` | `expected_minority_step`, `phaseII_step` |
| **Theorem 4**: `λ_G ≤ 3/5 − ε` and a minority of size `≤ (ε/5) n`: after `T` rounds the majority holds everywhere except with probability `≤ (24/25)^T \|B\| + T e^{−εn/24250}` | `two_choices_expander_explicit` |
| **Theorem 4**, `O(log n)` form: after `⌈C log n⌉` rounds, failure `≤ 1/n + (C log n + 1) e^{−εn/C}` (`C = 25000`), which tends to `0` for fixed `ε` | `two_choices_expander`, `two_choices_failure_tendsto` |

The proof replaces the paper's Phases II and III by a single supermartingale argument
(`expList_le_of_contract`); see [FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

**Provenance (Theorem 4).** The statements were written and fixed in advance by a Claude
agent and reviewed against the paper by a second agent, which found no problem with them (it
corrected the paper's lemma numbers cited in the docstrings and suggested stating the one-round
expectation bound separately, which was added as `expected_minority_step`); the proofs are by a
Claude agent under the fixed-statement protocol, and verified mechanically (statements
unchanged, no placeholders, warning-free build, axiom audit).

## Plurality consensus with `k` colours (k-party 2-Choices)

Every node samples two nodes uniformly at random (with replacement) and adopts their colour if
the two samples agree; otherwise it keeps its own. With two colours this is the median rule
(`TwoChoices.step_bool`). The colours are any type with decidable equality, and the probabilistic
theorems use `Fin k` for any `k`. Sources: Elsässer, Friedetzky, Kaaser, Mallmann-Trenn and
Trinker, arXiv:1602.04667 (v5, *Rapid asynchronous plurality consensus*; v1 to v4 are titled
*Efficient k-party voting with two choices*), Section 2.1, for the upper bound, and Berenbrink,
Clementi, Elsässer, Kling, Mallmann-Trenn and Natale, *Ignore or comply? On breaking symmetry in
consensus* (PODC 2017, [arXiv:1702.04921](https://arxiv.org/abs/1702.04921)), Theorem 5 and
Theorem 1 (Simplified), for the lower bound. Numbers follow these arXiv versions (see
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md)). Namespace `Median.TwoChoices`:

| Result | Lean declaration |
| --- | --- |
| The model; on `Bool` it is the median dynamics; a colour dominates, node by node, the binary median process started from its indicator | `rule`, `step`, `run`, `count`, `twice`, `kernel`, `step_bool`, `run_bool`, `run_dominates` (in [`Median/TwoChoicesDefs.lean`](Median/TwoChoicesDefs.lean)) |
| One-round expectations: `𝔼c_i' = c_i(1 + c_i/n − ∑_j c_j²/n²)`, Observation 2.1 (larger colours grow more in expectation), the expected gap and the aggregation of the minority colours | `expected_count`, `expected_count_mul`, `expected_count_mono`, `expected_gap`, `expected_gap_ge` (in [`Median/TwoChoicesExpect.lean`](Median/TwoChoicesExpect.lean)) |
| **Lemma 2.2**: if the largest colour has `a ≤ n/2` nodes and leads the second largest by `a − b ≥ z √(n log n)`, then `a' − b' > (a − b)(1 + a/(4n))` w.p. `≥ 1 − C/n²` (`z = 128`, `C = 2`) | `distance_increases` (in [`Median/TwoChoicesPlurality.lean`](Median/TwoChoicesPlurality.lean)) |
| **Lemma 2.3**, as a stochastic domination: if `c ≤ b`, then `P(c' ≥ t) ≤ P(b' ≥ t)` for every `t` | `count_stochDom` |
| **Theorem 1.2** (no adversary, any number of colours): if colour `i` leads every other colour by `z √(n log n)`, all nodes hold `i` after `⌈C (n/c_i) log n⌉` rounds w.p. `≥ 1 − C/n`, for `log n ≥ C` (`z = 128`, `C = 384`); also after `⌈C k log n⌉` rounds | `plurality_whp`, `plurality_whp_k` |
| The growth phase (the gap grows by `1 + a/(8n)` per round up to `a = 3n/4`) and the finishing phase (via the binary median process) | `growth_round`, `growth_phase`, `finish_phase` |
| Two colours, and almost-sure consensus | `two_colours_consensus_whp`, `absorbed` |
| One colour cannot grow fast: `P(∃ t ≤ T, c_i(t) > L) ≤ exp(−(L − c_i) + (e − 1) T L²/n)` | `colour_escape_le` (in [`Median/TwoChoicesLower.lean`](Median/TwoChoicesLower.lean)) |
| **Theorem 5** of Berenbrink et al.: if every colour has at most `ℓ` nodes, `ℓ' = max {2ℓ, γ log n}` and `T < n/(γ ℓ')`, no colour exceeds `ℓ'` nodes up to time `T` except w.p. `≤ 1/n`, for every `γ ≥ 8` | `lower_bound_strong` |
| **Theorem 1 (Simplified)**, 2-Choices lower bound: from colours of at most `β log n` nodes each, no consensus within `T` rounds except w.p. `≤ 1/n` whenever `(T + 1) C log n < n` (`C = max(8, 2β)²`), so consensus needs `Ω(n/log n)` rounds | `consensus_time_lower` |

The paper's hypothesis `k = O(n^ε)` is not needed: one-round Bernstein bounds with a node-wise
variance bound (`Median/TwoChoicesConc.lean`) replace its multiplicative Chernoff bounds, and
Observation 2.1 replaces the coupling of Lemma 2.3 in the growth step. The adversary of
Theorem 1.2 and its lower bounds are not formalized. The proofs of Theorem 1.2 and Lemma 2.3 of
Elsässer et al. and of Theorem 5 of Berenbrink et al. need minor corrections; see
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

**Provenance (k-party 2-Choices).** The definitions and statements were pinned by a Claude agent
and reviewed by a second agent; the proofs are by a Grok agent (grok-4.7) under the
fixed-statement protocol, and verified mechanically (statements unchanged, no placeholders,
warning-free build, axiom audit).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
