# PROGRESS: CRN-1, CRNs ⇔ population protocols

Job: roadmap row CRN-1 (track CRN, and the Chemistry column of the dictionary table). Sources:
Anderson–Kurtz, *Continuous time Markov chain models for chemical reaction networks* (2011), for
CRNs as CTMCs; Gillespie (1977) and Doty, *Timing in chemical reaction networks*, SODA 2014, §2,
for the combinatorial mass-action propensity; Angluin–Aspnes–Eisenstat (2008) and
Cardelli–Csikász-Nagy (2012) for approximate majority. The core identity is elementary.

## Status

* **Phase 1 (pin statements): done.** New Lake package `crn/` (library `Crn`), layout copied
  from `undecided/` (same `lakefile.toml` pins, `lake-manifest.json` with the package name
  changed, `lean-toolchain`, `.gitignore`), plus `Audit.lean` and `README.md`. No CI wiring.
  `PINNED.txt` (repo root) lists the 42 pinned declarations.
* **Phase 2 (proofs): done.** All 13 pinned theorems are proved; no pinned statement was false.
  `lake build Crn` is warning-free; `python3 ../scripts/check_axioms.py` (and `#print axioms` from
  a scratch file under `/tmp`): only `propext`, `Classical.choice`, `Quot.sound`. The pinned text
  of all 42 declarations is byte-identical to the phase-1 commit `21b9a0d` up to `:=` (checked
  mechanically, with a negative control); the only lines removed from pinned files are the
  `sorry`s and `import Crn.Condition` (now `import Crn.DistLemmas`).

## Pinned (frozen up to `:=`)

`Crn/Condition.lean` (namespace `Crn`; not in `dynamics/`, which this job may not change)
* `normalize w hw h`: the distribution with weights `w a / ∑ w`.
* `condition p E h`: `p` conditioned on `E` (`h : p.prob E ≠ 0`), weights `p a / p(E)` on `E`.

`Crn/Basic.lean`
* `Reaction S`: `reactants products : Sym2 S` (`A + B → C + D`, unordered), `DecidableEq`.
* `Network S`: `reactions : Finset (Reaction S)`, `nonempty`, `nontrivial` (reactants ≠ products).
* `Counts S n := {x : S → ℕ // ∑ a, x a = n}`, `Counts.instFintype` (via `Finset.piAntidiag`).
* `Reaction.consumed r a`, `Reaction.produced r a`: multiplicities (`Sym2.toMultiset` count).
* `Reaction.propensity k r x = k * ∏ a, C(x a, consumed r a)` (Gillespie's form).
* `Counts.react x r`: `x a - consumed + produced` if `r` is applicable, else `x`.
* `Network.totalPropensity N k x = ∑ r ∈ N.reactions, propensity`.
* `Network.nextReaction N hk x h`: `normalize` of the propensities on `N.reactions`.
* `Network.jumpKernel N k hk n : Kernel (Counts S n)`: `point x` if `a₀(x) = 0`, else
  `(nextReaction).map (x.react ·)`.
* `Reaction.propensity_of_ne`: `r.reactants = s(A, B)`, `A ≠ B` ⇒ propensity `= k·x A·x B`.
* `Reaction.propensity_of_eq`: `r.reactants = s(A, A)` ⇒ propensity `= k·C(x A, 2)`.
* `Network.jumpKernel_weight_self`: `a₀(x) ≠ 0` ⇒ the jump chain's weight at `x` is `0`.

`Crn/Protocol.lean`
* `AgentPair n := {p : Fin n × Fin n // p.1 ≠ p.2}`; `pairDist hn` uniform on it (`hn : 2 ≤ n`).
* `counts c` for `c : Fin n → S`: `x a = #{v | c v = a}`.
* `sampleDist N hn`: uniform on `AgentPair n × N.reactions` (pair and reaction independent).
* `Reacts N c ω :↔ s(c u, c v) = ω.2.reactants`, with `instDecidablePredReacts`.
* `outcome N c ω`: `(counts c).react ω.2` if `Reacts`, else `counts c`.
* `ppStep N hn c = (sampleDist N hn).map (outcome N c)`: the protocol on counts.
* `condStep N hn c`: `point (counts c)` if `P(Reacts) = 0`, else
  `(condition (sampleDist N hn) (Reacts N c) h).map (outcome N c)`.
* `ppKernel N hn : Kernel (Counts S n)`: `condStep` from a chosen configuration with counts `x`
  (`Classical.choose`; `point x` if none, which never happens).
* `pair_prob_of_ne`: `P(s(c u, c v) = s(A, B)) = x A · x B / C(n, 2)` for `A ≠ B`.
* `pair_prob_of_eq`: `P(s(c u, c v) = s(A, A)) = C(x A, 2) / C(n, 2)`.
* `pair_prob_eq_propensity`: `P(s(c u, c v) = r.reactants) = propensity k r x / (k·C(n, 2))`.
* `reactProb_eq`: `P(Reacts) = a₀(x) / (k·|N|·C(n, 2))`.
* `ppStep_expect`: `E_ppStep f = (1 - P(Reacts))·f x + P(Reacts)·E_jump f`.
* `condStep_eq_jumpKernel`: `condStep N hn c = N.jumpKernel k hk n (counts c)` (any `k > 0`).
* `jumpKernel_eq_ppKernel` (**CRN-1**): `N.jumpKernel k hk n = ppKernel N hn`.

`Crn/ApproximateMajority.lean` (namespace `Crn.ApproxMajority`)
* `Species` (`X | Y | B`, `DecidableEq`, `Fintype`); `xyToXB`, `xyToYB`, `bxToXX`, `byToYY`;
  `network` (the four reactions; `nontrivial` by `decide`).
* `network_jump_expect`: for `D = 2·#X·#Y + #B·(#X + #Y) > 0` (in `ℕ`),
  `E_jump f = (#X#Y·f(x.react xyToXB) + #X#Y·f(x.react xyToYB) + #B#X·f(…bxToXX)
  + #B#Y·f(…byToYY)) / D`.
* `network_reactProb_eq`: `P(Reacts) = D / (4·C(n, 2))` (with `D` at `counts c`).
* `network_jumpKernel_eq_ppKernel`: the instance of CRN-1.

Sanity checks done in phase 1 (scripts outside the repo, `/tmp/crncheck/check.py`, exact rational
arithmetic, a line-by-line mirror of the Lean definitions including the `react` fallback and the
conditioning convention): every pinned theorem holds for 75 random networks (1–3 species, 1–6
reactions, including `A + A` reactions and several reactions with the same reactants), all
configurations with `n ≤ 5` agents (`n ≤ 4` for 3 species), with `k = 3/2`; and for approximate
majority with `n ≤ 6` (`network_jump_expect` for all counts with `n ≤ 8`, random `f`). Negative
controls fail as they should: Anderson–Kurtz's `κ·#A(#A−1)` for `A + A`, and a protocol that picks a
uniformly random *applicable* reaction for the drawn pair (AM from counts `(2,1,1)`: `1/5, 1/5,
2/5, 1/5` instead of the jump chain's `2/7, 2/7, 2/7, 1/7`). Lean-side: `#check` of the statements
shows the casts on the leaves as intended; `network.reactions.card = 4` and
`Fintype.card (Counts Species 3) = 10` by `decide`.

## Proved

All 13 pinned theorems, plus the definitions' obligations (`normalize`, `condition`,
`Counts.instFintype`, `Counts.react`, `nextReaction`). Helper lemmas (not pinned):

`Crn/DistLemmas.lean` (new; reusable for any `Dynamics.Distribution`)
* `dist_ext` (equal weights), `dist_ext_expect` (equal expectations), `weight_eq_expect`.
* `prob_eq_sum`, `prob_eq_expect`, `expect_ite`: `prob` and indicator expectations for any
  `DecidablePred` instance (`prob` itself is classical).
* `normalize_expect`, `condition_expect` (`E_cond f = E[1_E·f] / P(E)`), `uniform_expect_sum`,
  `uniform_prob` (counting ratio), `uniform_prod_expect` (uniform on `α × β`: average the first
  coordinate, then the second).

`Crn/PairCount.lean` (new; pure counting, no probability)
* `card_filter_pairs`: pairs of distinct agents = off-diagonal of `Fin n × Fin n`.
* `card_pairs`: `n·(n - 1)` ordered pairs of distinct agents.
* `card_pairs_of_ne`: `2·#A·#B` pairs with species `{A, B}` (`F_A ×ˢ F_B ∪ F_B ×ˢ F_A`).
* `card_pairs_of_eq`: `#A·(#A - 1)` pairs with species `{A, A}` (`offDiag` of `F_A`).

`Crn/Basic.lean`
* `Reaction.sum_consumed`, `sum_produced` (`= 2`); `count_toMultiset_mk` (multiplicities in
  `s(A, B)`); `consumed_le_of_propensity_ne_zero`; `propensity_nonneg`.
* `Counts.react_val`; `Counts.react_ne_self` (an applicable non-trivial reaction changes the
  counts, via `Sym2.ext` and `Multiset.count_pos`).
* `Network.totalPropensity_mul_expect`: `a₀(x)·E_jump f = ∑ᵣ aᵣ(x)·f(x.react r)`, valid also at
  terminal states (all `aᵣ ≥ 0`), which avoids case splits downstream.

`Crn/Protocol.lean`
* `counts_val`; `exists_counts_eq` (a configuration with given counts, through
  `Fintype.equivFinOfCardEq` on `Σ a, Fin (x a)`); `pairDist_prob`; `cast_mul_pred`
  (`m(m - 1) = 2·C(m, 2)` in `ℝ`); `choose_two_pos`; `sampleDist_expect` (pair first, then
  reaction).
* `sampleDist_expect_reacts`, the core computation:
  `E[1_{Reacts}·g(r)] = ∑ᵣ aᵣ(x)·g(r) / (k·|N|·C(n, 2))`. With `g = 1` it is `reactProb_eq`;
  `ppStep_expect` splits `f ∘ outcome = f x + 1_{Reacts}·(f(x.react r) - f x)`;
  `condStep_eq_jumpKernel` divides by `P(Reacts)` (`condition_expect`, `dist_ext_expect`), and
  `P(Reacts) = 0 ↔ a₀ = 0` handles terminal states.

`Crn/ApproximateMajority.lean`
* `network_reactions`, `network_sum` (propensity-weighted sum over the four reactions),
  `network_totalPropensity` (`k·(2·#X·#Y + #B·(#X + #Y))`).

## Remaining

Nothing for CRN-1. Possible extensions (not pinned): the deterministic one-way AM protocol of
Angluin–Aspnes–Eisenstat as an agent-level chain with the same count chain (bridge to UND-2);
unequal rate constants as a weighted reaction draw; the voter, Moran and SI rows of the
dictionary as instances; moving `normalize`/`condition` and `DistLemmas` to `dynamics/`; README
and blueprint, CI wiring (by hand).

## Errors

None open. Phase 1: `rw` could not unfold `consumed` under the sum binder (`simp only`);
`sum_count_eq_card` lives in namespace `Multiset`. Phase 2: `if` with the classical instance
(inside `prob`, `condition`) vs a `DecidablePred` instance, solved by comparing sums term by term
with `by_cases`; `rw` cannot solve the higher-order pattern `?g ω.2`, so `g` is given explicitly
and the hypothesis `beta_reduce`d.

## Deviations from the source

1. **Mass-action convention.** Propensity of `A + A → ⋯` is `k·C(#A, 2)` (Gillespie; Doty SODA
   2014 §2; the roadmap's key identity), not Anderson–Kurtz's `κ·#A(#A−1)` (their slides:
   `λₖ(x) = κₖ ∏ xᵢ!/(xᵢ − yᵢₖ)!`, "if `2S₂ →` anything, `λₖ(x) = κₖ x₂(x₂ − 1)`"). Reason: with
   a common rate constant, the uniform-random-pair protocol matches Gillespie's form only; with
   Anderson–Kurtz's form CRN-1 holds when every `A + A` reaction has half the rate constant of the
   others (the negative control above fails otherwise).
2. **Only count-conserving bimolecular CRNs are modelled.** `Reaction` is `A + B → C + D` by
   construction (two `Sym2`), rather than general stoichiometry with a predicate. A network is a
   `Finset` (no duplicate reactions), required `nonempty` (the empty network is trivial: both
   chains are constant) and `nontrivial` (no reaction with products = reactants; such a reaction
   does not change the CTMC, and excluding it makes `jumpKernel` the embedded chain, see
   `jumpKernel_weight_self`).
3. **Randomized protocol.** Besides the uniformly random ordered pair of distinct agents, the
   protocol draws a uniformly random reaction, and "the pair reacts" means its species are that
   reaction's reactants. Reason: several reactions may share reactants (AM's two `X + Y`
   reactions), and then a protocol whose transition depends only on the pair cannot match a
   common rate constant (negative control above). The deterministic one-way AM protocol of
   Angluin–Aspnes–Eisenstat (initiator `X`, responder `Y` → responder `B`, etc.) has the same count
   chain but is not pinned (possible extension, the bridge to UND-2).
4. **Observed on count vectors.** `ppStep`/`condStep` record the counts after the interaction,
   not the agents' new species: which agent receives which product is irrelevant for counts and
   not canonical for unordered reactions. `ppKernel` uses a chosen configuration with the given
   counts; `condStep_eq_jumpKernel` shows the choice does not matter (lumpability).
5. **Ordered pairs.** The roadmap says "a uniformly random pair", the job "ordered pair"; ordered
   pairs are used, and the pair-species probabilities are the roadmap's unordered ones.
6. **Jump chain only, terminal states absorbing.** Holding times of the CTMC are not modelled (as
   in the roadmap row); the CTMC jump chain is undefined at terminal states, made absorbing here.
   `ppStep_expect` relates the unconditioned protocol (a lazy version of the jump chain).
7. **Common rate constant only.** `k > 0` is a parameter of `jumpKernel` and the theorems hold for
   every `k`. Unequal rate constants (a weighted scheduler, per the roadmap) are not pinned.
8. **Conditioning operations live in `crn/`.** `Crn.normalize`, `Crn.condition` are candidates to
   move to `dynamics/` (this job may only change `crn/`).
