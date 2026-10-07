# The undecided-state dynamics

Synchronous undecided-state dynamics with two opinions on the complete graph (each node samples one node uniformly, with replacement). Main results in [`Undecided/Basic.lean`](Undecided/Basic.lean), namespace `Undecided`; see the
[blueprint](blueprint/src/content.tex) for the statements and the map to Lean declarations.

**Sequential version (roadmap UND-2).** [`Undecided/SequentialMain.lean`](Undecided/SequentialMain.lean)
formalizes the approximate-majority protocol of Angluin, Aspnes and Eisenstat (Distributed
Computing 2008), one uniformly random ordered pair of agents per step: from any non-blank
configuration consensus within `O(n log n)` interactions, and from a gap of `C √n log n` the
initial majority wins, each with probability `1 - O(n^{-c})` for every `c` (`consensus_whp`,
`majority_whp`, `approximate_majority`). The proof uses six weighted supermartingales along finite
paths; see [`PROGRESS-UND2.md`](PROGRESS-UND2.md) for the route and the deviations from the paper.

**Provenance.** For `Undecided/Basic.lean`, the statements were written and pinned by hand; the
proofs were produced by a Grok agent under a fixed-statement protocol and verified mechanically
(statements unchanged, no placeholders, warning-free build, axiom audit). The sequential
statements and their proofs were written by a Claude agent under the same protocol; the statements
were reviewed by hand against the paper.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
