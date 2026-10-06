# CRNs are population protocols (CRN-1)

Count-conserving bimolecular chemical reaction networks (`A + B → C + D`) with a common rate
constant: the jump chain of stochastic mass-action kinetics equals the population protocol that
picks a uniformly random ordered pair of distinct agents, conditioned on the pair reacting, as
kernels on count vectors. Worked instance: the approximate-majority CRN
(`X + Y → X + B`, `X + Y → Y + B`, `B + X → X + X`, `B + Y → Y + Y`).

* [`Crn/Basic.lean`](Crn/Basic.lean): reactions, networks, count vectors, mass-action
  propensities and the jump chain `Crn.Network.jumpKernel`.
* [`Crn/Protocol.lean`](Crn/Protocol.lean): the population protocol, the pair-sampling identity
  and the main theorem `Crn.jumpKernel_eq_ppKernel`.
* [`Crn/ApproximateMajority.lean`](Crn/ApproximateMajority.lean): the worked instance.
* [`Crn/PairCount.lean`](Crn/PairCount.lean): counting ordered pairs of distinct agents by
  species.
* [`Crn/Condition.lean`](Crn/Condition.lean), [`Crn/DistLemmas.lean`](Crn/DistLemmas.lean):
  normalized weights, conditioning and expectation lemmas for `Dynamics.Distribution`.

**Status.** All statements proved (no `sorry`, standard axioms only); see
[`PROGRESS.md`](PROGRESS.md).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
