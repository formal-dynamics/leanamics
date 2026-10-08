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

## Semilinear predicates are stably computable (`Stable*`, CRN-3, easy direction)

Sources: Angluin, Aspnes, Diamadi, Fischer and Peralta, *Computation in networks of passively
mobile finite-state sensors*, Distributed Computing 18 (2006) [AADFP06], §3 (model) and §4
(Lemma 3 and Corollary 2: Boolean closure; Lemma 5: threshold and remainder predicates;
Theorem 5: Presburger-definable predicates); Angluin, Aspnes, Eisenstat and Ruppert (2007)
[AAER07] for the reachability form of stable computation; Chen, Doty and Soloveichik,
*Deterministic function computation with chemical reaction networks*, Natural Computing 13 (2014)
[CDS14], §§2.1–2.2, for chemical reaction deciders, with the "every species votes" convention of
Angluin, Aspnes and Eisenstat (PODC 2006) [AAE06].

1. **Stable computation in reachability form**, not with fair executions [AADFP06, §3.2]: every
   configuration reachable from the initial one can reach an output-stable configuration with the
   right output (the form of [AAER07] and [CDS14, §2.2]). For finite populations the two are
   equivalent (by AADFP06 Lemma 1, the configurations occurring infinitely often in a fair
   execution form a final strongly connected component); this equivalence is not formalized.
2. **Populations of every size `n ≥ 1`, and a minor correction to AADFP06 Lemma 5 for `n = 1`.** AADFP06 do
   not state a lower bound on the population size, but the protocols of their Lemma 5 start every
   agent with output bit `0` (input map `σᵢ ↦ (1, 0, aᵢ)`). With a single agent no encounter ever
   happens, so the output stays `0` even when the predicate holds (for example `a = (1)`, `c = 3`,
   one agent: `1 < 3` holds but the output is `0`); the protocols are correct for `n ≥ 2`. The
   theorems here are existential in the protocol, so this is harmless: the protocols used here
   start an agent with input `i` with output bit equal to the single-agent value (`[aᵢ < c]`,
   resp. `[aᵢ ≡ c (mod m)]`). The empty population `n = 0` is excluded, as usual (no agent, no
   output).
3. **Scope.** Predicates only (output alphabet `Bool`, all-agents predicate output convention),
   standard populations (complete interaction graph on `Fin n`), symbol-count input convention.
   Not covered: general interaction graphs, input-output relations and functions, other output
   conventions (AADFP06 Theorem 2), the integer-based input convention (Corollary 3).
4. **Threshold direction.** AADFP06 Lemma 5(1) is `∑ aᵢ xᵢ < c` (`stablyComputable_threshold`,
   and the atom of `IsSemilinearPred`); the form `∑ aᵢ xᵢ ≥ c` is its negation, stated separately
   as `stablyComputable_le_sum`.
5. **Remainder modulus `0 < m`** instead of AADFP06's `m ≥ 2` (a slight strengthening: `m = 1`
   gives the constant `true`), the natural hypothesis for `Int.ModEq`.
6. **Theorem 5 for an inductive class.** AADFP06 Theorem 5 concerns Presburger-definable
   predicates; its proof reduces them, by Presburger's quantifier elimination (their Theorem 4,
   cited without proof), to Boolean combinations of threshold, equality and remainder predicates.
   Here `IsSemilinearPred` is defined as the Boolean combinations of threshold and remainder
   predicates (equalities are conjunctions of two thresholds, as in the paper's proof). That this
   class equals the semilinear (Presburger-definable) predicates is not proved; instead,
   `IsSemilinearPred.isSemilinearSet` proves the inclusion into Mathlib's `IsSemilinearSet`
   (Mathlib proves `presburger.definable_iff_isSemilinearSet`), which shows that the class is
   not too large. The converse inclusion is Presburger's quantifier elimination.
7. **Agent-level configurations** (`Fin n → Q`, as AADFP06's `C : A → Q` and the configurations of
   CRN-1), not multisets. Count vectors enter through `counts`, in the predicate and in the
   transfer, where `Protocol.exists_network` shows that the induced dynamics on count vectors is
   that of a CRN.
8. **Transfer hypothesis.** CRN-1's networks are nonempty and have no reaction whose products
   equal its reactants, so `Protocol.exists_network` assumes a transition that changes the
   multiset of states of the two agents (otherwise the counts never change and there is no such
   network). It holds for every protocol (stable computation plays no role), with the reaction set
   characterized exactly. `StablyComputable.exists_network` provides such a transition by tagging
   the input states, which also makes the input map injective.
9. **Stable decision by CRNs.** `Network.StablyComputes` is the chemical reaction decider of
   [CDS14, §2.2] with every species voting (the convention of [AAE06]), no initial context
   (leaderless) and input species given by an injective map `X ↪ S`; the zero input is excluded
   (with no molecule the output is undefined in [CDS14]).
10. **Sanity check of the definition.** `Protocol.StablyComputes.unique` shows that stable
    computation determines the predicate on nonzero inputs, so the definition is not vacuous.
