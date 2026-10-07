# Formalization differences

Where the statements of `crn/` deviate from their sources, and why.

## CRNs are population protocols (`Basic`, `Protocol`, `ApproximateMajority`, CRN-1)

Sources: Anderson and Kurtz, *Continuous time Markov chain models for chemical reaction networks*
(2011), for CRNs as continuous-time Markov chains; Gillespie (1977) and Doty, *Timing in chemical
reaction networks* (SODA 2014, §2), for the combinatorial mass-action propensity;
Angluin, Aspnes and Eisenstat (2008) and Cardelli and Csikász-Nagy (2012) for approximate
majority.

1. **Mass-action convention.** The propensity of `A + A → ⋯` is `k·C(#A, 2)` (Gillespie; Doty
   §2), not Anderson and Kurtz's `κ·#A(#A − 1)` (their `λₖ(x) = κₖ ∏ xᵢ!/(xᵢ − yᵢₖ)!`). With a
   common rate constant, the uniformly-random-pair protocol matches Gillespie's form only. With
   Anderson and Kurtz's form the correspondence holds when every `A + A` reaction has half the
   rate constant of the others, and fails otherwise (checked numerically).
2. **Only count-conserving bimolecular CRNs.** `Reaction` is `A + B → C + D` by construction
   (two unordered pairs, `Sym2`), rather than general stoichiometry restricted by a predicate. A
   network is a `Finset` of reactions (no duplicates), required to be nonempty (the empty
   network is trivial: both chains are constant) and nontrivial (no reaction whose products
   equal its reactants; such a reaction does not change the continuous-time chain, and excluding
   it makes `jumpKernel` the embedded jump chain, see `jumpKernel_weight_self`).
3. **Randomized protocol.** Besides a uniformly random ordered pair of distinct agents, the
   protocol draws a uniformly random reaction, and "the pair reacts" means that the pair's
   species are that reaction's reactants. Several reactions may share their reactants (the two
   `X + Y` reactions of approximate majority), and then a protocol whose transition depends only
   on the pair cannot match a common rate constant. For example, the protocol that fires a
   uniformly random *applicable* reaction for the drawn pair gives, for approximate majority from
   counts `(#X, #Y, #B) = (2, 1, 1)`, the probabilities `1/5, 1/5, 2/5, 1/5` for the four
   reactions, while the jump chain gives `2/7, 2/7, 2/7, 1/7`. The deterministic one-way
   approximate-majority protocol of Angluin, Aspnes and Eisenstat has the same count chain but is
   not formalized.
4. **Observed on count vectors.** `ppStep` and `condStep` record the counts after an
   interaction, not the agents' new species: which agent receives which product does not matter
   for the counts and is not canonical for unordered reactions. `ppKernel` starts from a chosen
   configuration with the given counts; `condStep_eq_jumpKernel` shows that the choice does not
   matter (lumpability).
5. **Ordered pairs.** The protocol draws ordered pairs (initiator, responder); the pair-species
   probabilities (`pair_prob_of_ne`, `pair_prob_of_eq`) are those of unordered pairs.
6. **Jump chain only, terminal states absorbing.** Holding times of the continuous-time chain are
   not modelled. The jump chain is undefined at terminal states (zero total propensity), which
   are made absorbing here. `ppStep_expect` relates the unconditioned protocol, a lazy version of
   the jump chain, to the jump chain.
7. **Common rate constant only.** `k > 0` is a parameter of `jumpKernel` and the theorems hold
   for every `k`. Unequal rate constants (which would correspond to a weighted draw of the
   reaction) are not formalized.
8. **Conditioning lives in `crn/`.** `Crn.normalize` and `Crn.condition` (and the lemmas of
   `Crn/DistLemmas.lean`) are general operations on `Dynamics.Distribution` and are candidates to
   move to `dynamics/`.
