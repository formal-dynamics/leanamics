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

## Majority on graphs with very small local memory (CRN-4)

Population protocols on a connected interaction graph, where two agents interact only along an
edge (Mertzios, Nikoletseas, Raptopoulos, Spirakis, ICALP 2014, arXiv:1404.7671; Distributed
Computing 2017). The 4-state *ambassador protocol* stably computes the initial majority on every
connected graph, ties excluded (Theorem 2); no protocol with at most 3 states does, already on
complete graphs, so 4 states are optimal (Theorem 1); and the 3-state approximate-majority
protocol of Angluin, Aspnes and Eisenstat, with a uniformly random oriented edge per step and a
uniformly random placement of the two types, converges to the majority with probability at least
that of converging to the minority, at every finite time, hence with probability at least `1/2`
on connected graphs (Theorem 4). The proofs of Theorems 1, 2 and 4 need minor corrections (see
the differences file). Graphs are undirected.

* [`Crn/GraphMajorityBasic.lean`](Crn/GraphMajorityBasic.lean): protocols on an interaction
  graph, stable computation on graphs (agreeing with CRN-3 on complete graphs), majority.
* [`Crn/GraphMajorityAmbassador.lean`](Crn/GraphMajorityAmbassador.lean): the ambassador
  protocol and `Crn.ambassador_graphStablyComputes`.
* [`Crn/GraphMajorityLowerBound.lean`](Crn/GraphMajorityLowerBound.lean):
  `Crn.not_stablyComputesOnGraph_top_majority`, `not_graphStablyComputes_majority` and
  `rank_majority_eq_four`.
* [`Crn/GraphMajorityRandom.lean`](Crn/GraphMajorityRandom.lean): the one-way rule on a graph,
  `Crn.ApproxMajority.winProb_minority_le_majority` and `half_le_absorbProb_majority`.

**Status.** All statements proved (no `sorry`, standard axioms only). Deviations from the
sources (CRN-1, CRN-3 and CRN-4) are listed in
[`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
