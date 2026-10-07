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

## Stably computable predicates (CRN-3, easy direction)

Population protocols with input and output (Angluin–Aspnes–Diamadi–Fischer–Peralta 2006) stably
compute every threshold predicate `∑ aᵢxᵢ < c` and every remainder predicate
`∑ aᵢxᵢ ≡ c (mod m)`, the stably computable predicates are closed under Boolean operations, and
a protocol is a count-conserving bimolecular CRN, so every Boolean combination of threshold and
remainder predicates (the semilinear predicates) is stably decided by such a CRN.

* [`Crn/StableBasic.lean`](Crn/StableBasic.lean): protocols, reachability, stable computation.
* [`Crn/StableBoolean.lean`](Crn/StableBoolean.lean): Boolean closure (product construction).
* [`Crn/StableThreshold.lean`](Crn/StableThreshold.lean),
  [`Crn/StableRemainder.lean`](Crn/StableRemainder.lean): threshold and remainder predicates.
* [`Crn/StableSemilinear.lean`](Crn/StableSemilinear.lean): the class `IsSemilinearPred` and the
  main theorem; inclusion into Mathlib's `IsSemilinearSet`.
* [`Crn/StableCrn.lean`](Crn/StableCrn.lean): transfer to CRNs and stable decision by CRNs.
* Proof helpers: [`StableInteract`](Crn/StableInteract.lean) (encounters, reachability),
  [`StableProduct`](Crn/StableProduct.lean) (parallel composition),
  [`StableLeader`](Crn/StableLeader.lean) (generic leader protocols),
  [`StableThresholdProtocol`](Crn/StableThresholdProtocol.lean),
  [`StableRemainderProtocol`](Crn/StableRemainderProtocol.lean),
  [`StableSemilinearSet`](Crn/StableSemilinearSet.lean),
  [`StableTransfer`](Crn/StableTransfer.lean) (counts of encounters, input tagging).

**Status.** CRN-1: all statements proved (no `sorry`, standard axioms only); see
[`PROGRESS.md`](PROGRESS.md). CRN-3: all statements proved as well (no `sorry`, standard
axioms only); see [`PROGRESS-CRN3.md`](PROGRESS-CRN3.md).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
