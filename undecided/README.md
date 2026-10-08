# The undecided-state dynamics

Synchronous undecided-state dynamics with two opinions on the complete graph (each node samples one node uniformly, with replacement). Main results in [`Undecided/Basic.lean`](Undecided/Basic.lean), namespace `Undecided`; see the
[blueprint](blueprint/src/content.tex) for the statements and the map to Lean declarations.

## Majority phase (UND-1)

After Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip
model* (SODA 2015, Theorem 11 with two colours) and Clementi, Ghaffari, Gualà, Natale, Pasquale
and Scornavacca (MFCS 2018, Theorem 3.2). Results in
[`Undecided/Majority.lean`](Undecided/Majority.lean) and
[`Undecided/MajorityAssembly.lean`](Undecided/MajorityAssembly.lean), namespace `Undecided`:

| Result | Lean declaration |
| --- | --- |
| A round leaves the counts of `a`, `b` and undecided nodes within `Λ` of their expectations except with probability `4 exp(-2Λ²/n)` | `bad_round` |
| Explicit form: if `log n ≥ 10⁴` and `count a - count b ≥ 10⁴ √(n log n)` (any number of undecided nodes), not all nodes hold `a` after `⌈10⁴ log n⌉` rounds with probability at most `2/n` | `majority_explicit` |
| MFCS 2018, Theorem 3.2: there is `C` such that, if `log n ≥ C` and `count a - count b ≥ C √(n log n)`, all nodes hold `a` after `⌈C log n⌉` rounds with probability `≥ 1 - C/n` | `majority_whp` |
| The same for either opinion (`|count a - count b| ≥ C √(n log n)`, the initial majority wins) | `majority_whp_abs` |
| SODA 2015, Theorem 11 for two colours: no undecided nodes and `count a ≥ (1 + α) count b` | `majority_whp_of_ratio` |

The proof uses Hoeffding's inequality in every round and three phases (growth of the bias, a
bridge, contraction of the potential `12 count b + count u`) composed by the Markov property; see
[`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md) for the route and the differences
from the papers.

## Sequential version (UND-2)

[`Undecided/SequentialMain.lean`](Undecided/SequentialMain.lean)
formalizes the approximate-majority protocol of Angluin, Aspnes and Eisenstat (Distributed
Computing 2008), one uniformly random ordered pair of agents per step: from any non-blank
configuration consensus within `O(n log n)` interactions, and from a gap of `C √n log n` the
initial majority wins, each with probability `1 - O(n^{-c})` for every `c` (`consensus_whp`,
`majority_whp`, `approximate_majority`). The proof uses six weighted supermartingales along finite
paths; see [`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md) for the route and the
deviations from the paper.

## Provenance

For `Undecided/Basic.lean`, the statements were written and pinned by a second agent; the
proofs were produced by a Grok agent under a fixed-statement protocol and verified mechanically
(statements unchanged, no placeholders, warning-free build, axiom audit). The sequential
statements and their proofs were written by a Claude agent under the same protocol; the statements
were reviewed by a second agent against the paper. The majority-phase statements (`Majority*`) and their
proofs were written by a Claude agent under the same protocol.

## Build

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
