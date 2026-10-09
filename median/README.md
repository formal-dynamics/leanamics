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

### A small initial imbalance (Theorem 2)

The paper's Theorem 2: on a `d`-regular graph, an initial imbalance `ν₀ = (A − B)/n ≥ K λ_G`
suffices for the majority to win in `O(log n)` rounds. Phase I (the paper's Lemma 2 and
Corollary 2) brings the minority down to `n/20`, and Theorem 4 finishes. In
[`Median/ExpanderGeneralPhaseI.lean`](Median/ExpanderGeneralPhaseI.lean) and
[`Median/ExpanderGeneral.lean`](Median/ExpanderGeneral.lean), with `η = α n / √(A B)` and the
mixing hypothesis `MixingProp G d α c` of Lemma 2 (implied by `λ_G ≤ α`):

| Result | Lean declaration |
| --- | --- |
| Expected flows in one round: `𝔼 Δ_{BA} ≥ (A²B/n²)(1 − 2η)`, `𝔼 Δ_{AB} ≤ (AB²/n²)(1 + 15η)` | `expected_gain_ge`, `expected_loss_le` |
| Their tails: `P(Δ_{BA} ≤ (A²B/n²)(1 − 3η)) ≤ e^{−α²cn/6}`, `P(Δ_{AB} ≥ (AB²/n²)(1 + 17η)) ≤ e^{−α²c²n/2}` | `gain_tail`, `loss_tail` |
| One round of Phase I: `ν' ≥ ν + ν(1 − ν²)/2 − 12α/√(1 − ν²)` w.p. `≥ 1 − e^{−α²cn/6} − e^{−α²c²n/2}`, hence `ν' ≥ (5/4)ν` or `1 − ν' ≤ (3/4)(1 − ν)` | `phaseI_step`, `growth_small`, `growth_large` |
| **Lemma 2** (`K = 120`) and **Corollary 2**: if `ν₀ ≥ 120 α`, the minority drops to `≤ cn` within `T₁ = ⌈log_{5/4}(1/(2ν₀))⌉ + ⌈log_{4/3}(1/(4c))⌉` rounds, except w.p. `≤ T₁ (e^{−α²cn/6} + e^{−α²c²n/2})` | `phaseI`, `phaseI_expander` |
| **Theorem 2**, explicit form: `4000 λ_G ≤ ν₀`; after `T₁ + T₂` rounds the majority holds everywhere except w.p. `≤ T₁(e^{−α²n/120} + e^{−α²n/800}) + (24/25)^{T₂} n + (T₁ + T₂) e^{−n/97000}` with `α = ν₀/4000` | `two_choices_expander_general_explicit` |
| **Theorem 2**, `O(log n)` form: `K λ_G ≤ ν₀`; after `⌈C log n⌉` rounds, failure `≤ 1/n + (2C log n + C) e^{−ν₀²n/C}` (`K = 4000`, `C = 2·10¹⁰`) | `two_choices_expander_general` |

The paper's Theorem 2 claims success with probability tending to `1` whenever `ν₀ ≥ K λ_G`;
this fails when `λ_G` is of order `1/√n` or smaller (for instance on the complete graph with
`A − B` constant), and the formal bound is in terms of `ν₀² n` instead; see
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md) and
[PROGRESS-MAJ5B.md](PROGRESS-MAJ5B.md).

**Provenance (Theorem 2).** The statements were written and fixed in advance (pinned, together
with the defining equations `*_spec` of the definitions they use); the proofs are by Claude
agents (Opus) under the fixed-statement protocol, and verified mechanically (statements
unchanged, no placeholders, warning-free build, axiom audit).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
