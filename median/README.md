# The median dynamics and 2-Choices

Doerr, Goldberg, Minder, Sauerwald and Scheideler, *Stabilizing consensus with the power of two
choices* (SPAA 2011): every node holds a value from a linearly ordered set and, every round,
adopts the median of its own value and the values of two nodes sampled uniformly at random (with
replacement). With two values this is the 2-Choices dynamics.

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
| 2-Choices from a gap `Δ ≥ C √(n log n)`: consensus on the majority after `⌈C (log (n/Δ) + log log n)⌉` rounds w.p. `≥ 1 − C/n`, for `log n ≥ C` (`C = 128`) | `binary_consensus_fast` (in [`Median/ManyValues.lean`](Median/ManyValues.lean)) |
| Many values: a margin `Δ ≥ C √(n log n)` on both sides of a value `v` gives consensus on `v` after `⌈C (log (n/Δ) + log log n)⌉` rounds w.p. `≥ 1 − 2C/n` | `median_consensus_fast` |
| **Theorem 21, odd case** (equal supports): `2k+1` values held by `n/(2k+1)` nodes each, `C (2k+1) √(n log n) ≤ n`: the middle value wins after `⌈C (log (2k+1) + log log n)⌉` rounds w.p. `≥ 1 − C/n` | `odd_split_consensus` (`C = 256`) |

The thresholds `log n ≥ 128` (`n ≥ e¹²⁸`), `log n ≥ 256`, `log n ≥ 2¹⁸` and
`log n ≥ 3·2¹⁸ + 3` come from the crude constants of the phase and drift arguments (see [PROVENANCE.md](../PROVENANCE.md) and roadmap MAJ-11). Where the
statements and proofs deviate from the paper is listed in
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

**Provenance.** For the results up to `consensus_whp`, the statements were written and pinned by
hand; the proofs were produced by
GLM-5.3 (on the Mistral API, driven by Mistral Vibe) under the fixed-statement protocol and
verified mechanically (statements unchanged, no placeholders, warning-free build, axiom audit).
See [PROVENANCE.md](../PROVENANCE.md) for the other results.

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

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
