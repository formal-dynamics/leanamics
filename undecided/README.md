# The undecided-state dynamics

Synchronous undecided-state dynamics with two opinions, and with `k` colours, on the complete graph (each node samples one node uniformly, with replacement). Main results in [`Undecided/Basic.lean`](Undecided/Basic.lean), namespace `Undecided`; see the
[blueprint](blueprint/src/content.tex) for the statements and the map to Lean declarations.

**Majority phase (UND-1)**, in [`Undecided/Majority.lean`](Undecided/Majority.lean): for
`log n ≥ C` and any configuration (undecided nodes allowed) in which one opinion leads by at
least `C √(n log n)`, all nodes hold the initial majority opinion after `⌈C log n⌉` rounds with
probability at least `1 - C/n` (`majority_whp`, `majority_whp_abs`, with `C = 10⁴`; Clementi et
al., MFCS 2018, Theorem 3.2), and the two-colour case of Theorem 11 of Becchetti et al. (SODA 2015)
(`majority_whp_of_ratio`). The proof (Hoeffding per round, three phases composed by the Markov
property) is in `Undecided/Majority{Round,Arith,Stages,Assembly,Symm}.lean`; see
[PROGRESS.md](PROGRESS.md).

**Many colours (UND-3)**, in [`Undecided/Plurality.lean`](Undecided/Plurality.lean): the
`k`-colour undecided-state dynamics (`Undecided/PluralityBasic.lean`; the binary model is the
case `k = 2`, `Undecided/PluralityBinary.lean`) reaches consensus on the plurality colour within
`⌈C md(c) log n⌉` rounds with probability at least `1 - C/n`, where `md(c) = ∑ᵢ (cᵢ/c₁)²` is the
monochromatic distance, from any configuration without undecided nodes in which the plurality
beats every other colour by a factor `1 + α`, for `C k ≤ (n / log n)^{1/3}` and `log n ≥ C`
(`plurality_whp`, with `C = 10⁵ ((1+α)²/α)²`; Becchetti et al., SODA 2015, Theorem 11, with
the range of `k` discussed in [PROGRESS-UND3.md](PROGRESS-UND3.md)). The proof is in
`Undecided/Plurality{Conc,Round,Alg,Arith,Steps,Progress,Stages,Assembly}.lean`.

**Provenance.** UND-1: the statements were written and pinned by hand; the proofs were produced by
a Grok agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit). UND-3: the statements (pinned in a first phase,
then reviewed by hand against the paper) and the proofs were produced by a Claude agent under the
same protocol.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
