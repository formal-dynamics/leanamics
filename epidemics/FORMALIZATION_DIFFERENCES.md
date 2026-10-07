# Formalization differences

Where the statements of `epidemics/` deviate from their sources, and why.

## The Kermack–McKendrick SIR model (`KermackMcKendrick*`, EPI-7)

Sources: W. O. Kermack, A. G. McKendrick, *A contribution to the mathematical theory of
epidemics*, Proc. R. Soc. Lond. A 115 (1927) 700–721; H. W. Hethcote, *The mathematics of
infectious diseases*, SIAM Review 42 (2000) 599–653, §2.3, system (2.2) and Theorem 2.1.

1. **Special case of Kermack–McKendrick 1927.** Their model has infectivity and removal rates
   depending on the age of infection; as in Hethcote §2.3, we formalize the constant-rate
   special case (the SIR ODE). Docstrings cite Hethcote 2000 (system (2.2), Theorem 2.1) for
   numbering, since the 1927 paper has no numbered theorems.
2. **Solution as hypothesis, on `[0, ∞)`.** Hethcote states existence, uniqueness and positive
   invariance of the triangle `T`; we do not construct solutions. The ODE is Mathlib's
   `IsIntegralCurveOn` of `fun _ ↦ sirField β γ` on `Set.Ici 0`, i.e. derivatives within
   `[0, ∞)` (one-sided at `0`); values for `t < 0` are irrelevant. Positivity of `s` and `i` is
   proved, not assumed.
3. **`ℝ³` as `ℝ × ℝ × ℝ`, components as three functions.** The curve is
   `fun t ↦ (s t, i t, r t)`; the theorems speak about `s`, `i`, `r` directly. We keep `r` in
   the state with `r' = γ i` (Hethcote eliminates it by `r = 1 - s - i`; here conservation is a
   theorem, `IsSolution.sum_eq_one`).
4. **Initial data.** Hethcote allows `s₀, i₀ ≥ 0` and `r(0) = 1 - s₀ - i₀ ≥ 0`; we fix
   `r(0) = 0` and `s(0), i(0) > 0`. Hence `i₀ + s₀ = 1`, and his equation
   `i₀ + s₀ - s∞ + ln(s∞/s₀)/σ = 0` becomes `s∞ = s₀ exp(-R₀(1 - s∞))`. The peak value is
   stated verbatim as `i₀ + s₀ - 1/R₀ - log(R₀ s₀)/R₀`.
5. **"Initially increases"** is formalized as `∃ ε > 0, StrictMonoOn i (Set.Icc 0 ε)` (a
   statement about `i`, not merely the sign of `i'(0)`, which would be a tautology).
6. **Threshold, subcritical case.** Hethcote's "if `σ s₀ ≤ 1`, `i(t)` decreases to zero" is
   split into `strictAntiOn_i` (strictly decreasing on `[0, ∞)`) and `tendsto_i` (which holds
   for every solution).
7. **Limits.** "`s∞` exists" is `∃ sInfty, Tendsto s atTop (𝓝 sInfty)`; the properties of `s∞`
   are stated for any limit (hypothesis `Tendsto s atTop (𝓝 sInfty)`), avoiding a `limUnder`
   definition. `i∞ = 0` is `Tendsto i atTop (𝓝 0)`; `r∞ = 1 - s∞` is `tendsto_r`.
8. **Uniqueness of the final size.** Hethcote's "unique root in `(0, 1/σ)`" is stated on the
   slightly larger `(0, 1/R₀]` (`R₀ x ≤ 1`), together with `0 < s∞` and `R₀ s∞ < 1`; we also add
   uniqueness on `(0, 1]` (`final_size_unique_of_le_one`), the physically meaningful range.
9. **Additions**, all from Hethcote's Theorem 2.1: `strictAntiOn_s`, `strictMonoOn_r`,
   `strictAntiOn_i`, `tendsto_r`, `limit_pos`, `R₀_mul_limit_lt_one`, the two uniqueness
   statements and `exists_peak`.
10. **Proof route.** Positivity of `i` uses the barrier `i(t) ≥ i(0) e^{-γ t}/2` (via
    `image_le_of_deriv_right_lt_deriv_boundary'`) instead of integrating `β s - γ` or Gronwall.
    The model-independent calculus lemmas (constancy and strict monotonicity from the sign of a
    derivative within `[0, ∞)`, limits of monotone functions) are in
    `KermackMcKendrickCalculus.lean`.

## Randomized rumor spreading revisited (`Revisited/`, EPI-8)

Source: B. Doerr, A. Kostrygin, *Randomized rumor spreading revisited*, ICALP 2017; long version
arXiv:2303.11150 (numbering of the long version: Lemma 9, Lemma 19, Lemma 20, Definition 11,
Theorem 21, Theorem 31).

### Lemma 20 of the paper is false as stated

Lemma 20 (Lemma 5 of the overview) claims: if `p_k ≤ p` and `c_k ≤ c/n` for every `k < f n`,
then there is `f' ∈ ]f, 1[` such that, with probability `1 - O(1/n)`, the number of informed
nodes lies in `[f n, f' n]` at the end of some round. The proof bounds one round: from
`k < f n`, `P[k + X(k) ≥ f' n] = O(1/n)`. It then concludes that the whole process jumps over
`[f n, f' n]` with probability `O(1/n)`, but the process may spend many rounds below `f n`, with
a chance to jump in each.

**Counterexample.** From every `S` with `|S| < f n`, inform all nodes with probability
`ε = c/n` and otherwise none. For `n ≥ c/p`, `p_k = ε ≤ p` and `c_k = ε(1 - ε) ≤ c/n`, but the
process started from one node jumps from `1` to `n` with probability 1. (The same process with
`ε_k = c k / n²` satisfies the lower exponential growth conditions, so the last sentence of
Theorem 1, which rests on Lemma 20, is also unproved in general. That sentence is a lower-bound
statement, outside the scope of this formalization.)

Two true versions are formalized instead:

* `overshoot_round`, the one-round estimate of the proof, for every `f' ∈ ]f + p(1-f), 1[`;
* `jumpProb_le`, the path statement with the union bound over rounds:
  `P[jump within t rounds] ≤ C/n · E[number of those rounds started below f n]`, that is,
  `O(E[T(|S|, f n)] / n)`.

A smaller slip in the same proof: it writes `E[X(k)] ≤ p n (1 - f)`; the correct bound is
`p (n - k)`. The threshold `f + p(1-f)` for `f'` is still right, because
`k + p(n - k) < n (f + p(1-f))` for `k < f n`.

### Statements

1. **Processes and spreading times.** A rumor-spreading process is a Markov kernel
   (`Dynamics.Kernel`) on the set of informed nodes under which informed nodes stay informed
   (`RumorProcess`). The spreading time `T(k, m)` (Definition 8) is handled through its tail
   `notYet m t S = P[fewer than m nodes informed after t rounds from S]`; expectations
   `E[T] = ∑_t P[T > t]` are bounded through every finite partial sum of this series.
2. **No homogeneity.** Homogeneity (Definition 6) is defined (`Homogeneous`) but not assumed:
   the growth and shrinking conditions (`UpperGrowth`, `UpperShrinking`) are bounds for every
   state, which every homogeneous process satisfying the paper's conditions satisfies.
3. **Starting sets.** The paper starts from one informed node (Theorem 21) or from exactly
   `n - ⌊g n⌋` informed nodes (Theorem 31). Here the growth and total-time theorems start from
   any nonempty `S`, and Theorem 31 from any `S` with `n - |S| ≤ g n`.
4. **Time convention.** Tails are `P[T > ⌈log_{1+γ} n⌉ + r]` and `P[T > ⌈(1/ρ) ln n⌉ + r]`.
   This matches the paper's `P[T > log_{1+γ} n + r]` up to replacing `A` by `A e^α`. The
   constants `A, α, B` and the threshold `N` are explicit and depend only on the parameters of
   the conditions (`N` may be enormous).
5. **Definition 11, uniform side condition.** The side condition `e^{-ρ_n} + a g < 1` is taken
   uniformly in `n`, as `e^{-ρlo} + a g < 1`. The per-`n` reading is not enough: if
   `e^{-ρ_n} + a g = 1 - δ_n` with `δ_n → 0` fast, then rounds near `g n` uninformed nodes shrink
   by a factor `1 - δ_n`, and escaping them costs `Θ(log n)` extra rounds, not `O(1)`. Lemma 19,
   which the paper uses to shrink `g`, likewise needs a uniform `p`.
6. **`ρ_n ∈ [ρlo, ρhi]` is kept**, also for the uniform constants. The upper bound matters: for
   `ρ = ln n`, the term `a u / n` makes the shrinking double exponential, which takes about
   `log₂ ln n` rounds, not `ln n / ρ + O(1) = O(1)`.
7. **Lemma 20's hypotheses.** `overshoot_round` assumes the bounds only for the one starting set,
   and does not require it to be nonempty (Chebyshev does not need it). `jumpProb_le` assumes
   them for every nonempty `S` with `|S| < f n` (the paper's `1 ≤ k < f n`) and starts from a
   nonempty set. The bad event "jumps over `[f n, f' n[`" is a path event (`JumpsOver`), and its
   probability `jumpProb` is an expectation over `Dynamics.Kernel.trajectory`.
8. **Total spreading time.** `spreading_upper_tail` and `spreading_upper_expect` are not single
   statements of the paper. They compose Theorem 21, Lemma 19 and Theorem 31 the way the paper
   does for concrete protocols (Section 3.4, Appendix C, e.g. Theorem 51). The middle-range
   hypothesis is Lemma 19's: every uninformed node becomes informed with probability at least
   `p` when `f n ≤ |S|` and `n - |S| > g n`. Like `connect_tail`, it takes `0 < p ≤ 1`; the
   paper's Lemma 19 takes `0 < p < 1`. If `f + g ≥ 1` the middle range is empty and the
   hypothesis is vacuous. The growth and shrinking conditions have separate constants `a, c`
   and `a', c'`.
9. **Unused hypotheses kept for fidelity.** Some hypotheses of the paper are not needed by the
   proofs (`0 < f`, `f < 1`, `f' < 1` in `overshoot_round`, `0 < f` in `jumpProb_le`, `g < 1` in
   the four shrinking and total-time theorems); they are kept in the statements.

### Proof routes (not statement changes)

1. **Lemma 19** does not use a dummy process. The potential is `g S = n - |S|` while
   `ℓ ≤ |S| < m`, and `0` once `|S| ≥ m`.
2. **Theorem 21.** The phase crossing does not use stochastic domination by sums of geometric
   random variables (Lemmas 10, 11, 25). It is an induction on `Kernel.iterate` with a phase
   potential. `f` is shrunk to `f' = min(f/2, 1/(8(a+1)))` only inside the phase construction,
   to keep the round target `E0(k) = E(k) - A k^{3/4}` increasing; the theorem's threshold stays
   `f n`, and Lemma 19 crosses `[k_J, f n)`. Cantelli's inequality (not Chebyshev's) bounds the
   probability of missing a round target, by `q/(1+q)`. Time is split in half between the phase
   potential and Lemma 19, which halves both exponential rates.
3. **Theorem 31** is proved with the single quadratic potential `Φ = u + (β/n) u²` of the number
   `u` of uninformed nodes, which satisfies `E[Φ'] ≤ e^{-ρ} (1 + K/n) Φ`, instead of the paper's
   phase calculus (target sequence, Chebyshev per phase and geometric domination, Lemmas 32–37).
   A first stage by Lemma 19 brings the number of uninformed nodes below a smaller `g₀ n`.
4. **Lemma 20, path form,** is proved by a union bound along `Kernel.trajectory`.
5. `Distribution.prob` and `Kernel.event` are bridged by `prob_indicator_eq`, because `prob`
   decides propositions with `Classical.propDecidable`.
