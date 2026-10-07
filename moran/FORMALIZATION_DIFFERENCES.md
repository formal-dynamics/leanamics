# Formalization differences

Where the statements of `moran/` deviate from their sources, and why.

## Fixation on the star (`Moran/Star*.lean`)

Sources: Broom and Rychtář, *An analysis of the fixation probability of a mutant on special
classes of non-directed graphs*, Proc. R. Soc. A 464 (2008), §5; Lieberman, Hauert and Nowak,
*Evolutionary dynamics on graphs*, Nature 433 (2005).

1. **Graph encoding.** The star is Mathlib's `starGraph c` on any finite type `V` with
   `Fintype.card V = n + 1` (any labelling), instead of vertices `0, …, n` with centre `0`.
   Only the limit theorem `star_fixation_uniform_tendsto` fixes `V = Fin (n + 1)`, centre `0`.
2. **Fixation probability** is the supremum of the finite-time fixation probabilities
   (`fixation`, as for the isothermal theorem), not the absorption probability of a
   path-space measure; the two agree in this finite setting.
3. **Closed form instead of the geometric sum.** Broom and Rychtář give
   `P_1 = 1 / (1 + n/(n+r) ∑_{j=1}^{n-1} q^j)` (mutant centre, one mutant leaf) and the
   average `φ`, with `q = (n + r)/(r (n r + 1))`. We sum the geometric series:
   with `κ = (n r + 1)/(r (n + r))`, a single mutant fixes with probability
   `(1 - q)/(1 - κ q^n)` from a leaf (`star_fixation_leaf`) and `(1 - κ)/(1 - κ q^n)` from
   the centre (`star_fixation_centre`). Their displayed `φ` is also stated verbatim
   (`star_fixation_uniform_sum`, with `∑_{j=1}^{n-1}` written `∑ j ∈ Ico 1 n`). Their notation
   `P⁰ᵢ` denotes a *mutant* centre (as their (5.1) and boundary conditions show).
4. **`r ≠ 1` in the closed forms**, which are `0/0` at `r = 1`. The neutral case is covered by
   `star_fixation_uniform_sum` (valid for every `r > 0`), whose `r = 1` case follows from
   `push_fixation`: on every connected graph a neutral single mutant at a uniformly random
   vertex fixes with probability `1/N` (`neutral_uniform_fixation`, `Moran/PushPull.lean`).
5. **General configurations and the invariant potential.** `star_fixation` (fixation from any
   configuration `s`, equal to `(1 - Φ s)/(1 - Φ (all mutant))`) and
   `star_potential_invariant` (the potential `Φ s = q^(#mutant leaves) · κ^[centre mutant]` is
   invariant in expectation) are not stated in the sources. They are an invariant-based
   characterization, by the same method as the isothermal theorem, from which the
   single-mutant formulas follow.
6. **Amplifier for every `n ≥ 2`.** Lieberman, Hauert and Nowak assert amplification for large
   stars, and Broom and Rychtář observe numerically that the average fixation probability is
   always increased for `r > 1`. We prove it for every `n ≥ 2` and every `r > 1`
   (`star_amplifier`), by an elementary argument (Bernoulli's inequality and a termwise
   comparison of geometric sums). `n ∈ {0, 1}` is excluded: then the star is complete (`K_1`,
   `K_2`) and equality holds. Following the definition of an amplifier (advantageous mutants
   favoured, disadvantageous ones disfavoured), the reverse inequality for `0 < r < 1` is also
   proved (`star_amplifier_deleterious`). Moran's formula is written explicitly,
   `(1 - 1/r)/(1 - (1/r)^N)` with `N = Fintype.card V`, as in `isothermal`.
7. **Large-`n` behaviour.** The formula `(1 - 1/r²)/(1 - 1/r^(2N))` of Lieberman, Hauert and
   Nowak is an approximation, not an identity; its exact content is stated as a limit:
   uniform-start fixation tends to `1 - 1/r²` as `n → ∞`, for `r > 1`
   (`star_fixation_uniform_tendsto`).
