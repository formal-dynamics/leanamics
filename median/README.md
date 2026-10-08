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

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
