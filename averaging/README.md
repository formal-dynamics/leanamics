# Averaging dynamics on graphs

Every node of a finite graph replaces its value by the average of its neighbours' values. Main results in [`Averaging/Basic.lean`](Averaging/Basic.lean), namespace `Averaging`; see the
[blueprint](blueprint/src/content.tex) for the statements and the map to Lean declarations.

**Provenance.** The statements were written and pinned by hand; the proofs were produced by a Grok
agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit). AVG-1's rate bound (`Averaging/Rate*.lean`: Lovász's
Theorem 5.1, `|Pᵗ(u,v) − π(v)| ≤ √(d(v)/d(u)) λᵗ`) and the sequential-averaging identities
(`Averaging/Sequential*.lean`) were pinned by a Claude agent, reviewed by hand against the
sources, and then proved by the agent under the same protocol.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
