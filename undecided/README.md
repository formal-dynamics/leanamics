# The undecided-state dynamics

Synchronous undecided-state dynamics with two opinions on the complete graph (each node samples one node uniformly, with replacement). Main results in [`Undecided/Basic.lean`](Undecided/Basic.lean), namespace `Undecided`; see the
[blueprint](blueprint/src/content.tex) for the statements and the map to Lean declarations.

**Majority phase (UND-1)**, in [`Undecided/Majority.lean`](Undecided/Majority.lean): for
`log n ≥ C` and any configuration (undecided nodes allowed) in which one opinion leads by at
least `C √(n log n)`, all nodes hold the initial majority opinion after `⌈C log n⌉` rounds with
probability at least `1 - C/n` (`majority_whp`, `majority_whp_abs`, with `C = 10⁴`; Clementi et
al., MFCS 2018, Theorem 3.2), and the two-colour case of Theorem 11 of Becchetti et al. (SODA 2015)
(`majority_whp_of_ratio`). The proof (Hoeffding per round, three phases composed by the Markov
property) is in `Undecided/Majority{Round,Arith,Stages,Assembly,Symm}.lean`; see
[PROGRESS.md](PROGRESS.md).

**Provenance.** The statements were written and pinned by hand; the proofs were produced by a Grok
agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
