# PROGRESS-MAJ4: k-party 2-Choices (roadmap MAJ-4 and MAJ-6 (a))

Status: **proved**. `lake build Median` succeeds with no warnings, and
`python3 ../scripts/check_axioms.py` reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry` remains in `median/`. Constants used below: `γ₀ = 8` (lower bound), `z = 128` and
one-round `C = 2` (Lemma 1 and `growth_round`), phase `C = 128` (`growth_phase`; `plurality_whp`
then takes `C₁ + 256`).

## Sources

* **MAJ-4.** Elsässer, Friedetzky, Kaaser, Mallmann-Trenn, Trinker, *Efficient k-party voting
  with two choices*, arXiv:1602.04667. The latest arXiv version (v5, February 2017) is titled
  *Rapid asynchronous plurality consensus*; numbering below follows v5. The synchronous
  2-Choices results are Theorem 1 (upper bound, stated in Section 1.2) and its proof in
  Section 2.1 (Observation 1, Lemma 1, Lemma 2, proof of Theorem 1).
* **MAJ-6 (a).** Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn, Natale, *Ignore or
  comply? On breaking symmetry in consensus*, PODC 2017, arXiv:1702.04921 (v1). Theorem 1
  (simplified) and Theorem 3 (`lem:lowerTCstrong`, Section 6, full proof in Appendix C).

## The model (`Median/TwoChoicesDefs.lean`, namespace `Median.TwoChoices`)

Colours are any type `α` with decidable equality (the probabilistic theorems use `Fin k`);
configurations and rounds are those of the median dynamics (`Median.Config n α = Fin n → α`,
`Median.Round n = Fin n → Fin n × Fin n`: the two nodes sampled by every node, independently,
uniformly, with replacement, itself included). `rule own a b = if a = b then a else own`,
`step x r v = rule (x v) (x (r v).1) (x (r v).2)`, `run x l = l.foldl step x`,
`count x i = #{v | x v = i}`, `twice x r i = #{v | both samples of v hold i}`,
`kernel n α = Kernel.ofStep step`.

## Pinned statements

Status: **P** = proved. Every pinned statement below is proved; the assemblies
(`plurality_whp`, `plurality_whp_k`, `consensus_time_lower`) no longer depend on a `sorry`.

### Model and bridge (`TwoChoicesDefs.lean`)

| Lean | Statement | Status |
| --- | --- | --- |
| `step_of_ne`, `step_of_eq`, `step_of_consensus` | samples differ ⇒ keep own colour; samples agree ⇒ adopt; consensus is fixed | P |
| `count_step_le` | `c_i' ≤ c_i + twice x r i` (a colour gains only nodes that see it twice) | P |
| `count_step_eq_zero` | an extinct colour stays extinct | P |
| `rule_bool`, `step_bool`, `run_bool`, `count_true` | **bridge**: on `Bool` the rule is `med3`, `step = Median.step`, `run = Median.run`, `count · true = ones` | P |
| `run_dominates` | the binary median process on the indicator of colour `i`, run with the same rounds, is dominated node by node by "holds `i`" | P |

### One-round expectations (`TwoChoicesExpect.lean`; Elsässer et al., Section 2.1)

| Lean | Paper | Statement | Status |
| --- | --- | --- | --- |
| `avg_pair` | – | both samples hold `j` w.p. `(c_j/n)²` | P |
| `avg_step_node` | – | `P(v ends in i) = (c_i/n)² + [x v = i](1 − ∑_j (c_j/n)²)` | P |
| `expected_count` | Eq. (1) | `𝔼c_i' = c_i + (n − c_i)c_i²/n² − (c_i/n²)∑_{j≠i} c_j²` | P |
| `expected_count_mul` | proof of Obs. 1 | `𝔼c_i' = c_i(1 + c_i/n − S/n²)`, `S = ∑_j c_j²` | P |
| `expected_count_mono` | Observation 1 | `c_r ≤ c_s ⇒ 𝔼c_r' ≤ 𝔼c_s'` | P |
| `expected_gap` | proof of Lemma 1 | `𝔼(c_i' − c_j') = (c_i − c_j)(1 + (c_i + c_j)/n − S/n²)` | P |
| `sum_sq_le_aggregate` | proof of Lemma 1 | aggregation of the minority colours: `S ≤ c_i² + (n − c_i) b` if `b` bounds every other colour | P |
| `sum_sq_le_max` | proof of Lemma 1 | `S ≤ a n` if `a` bounds every colour | P |
| `expected_gap_ge` | proof of Lemma 1 | `𝔼(a' − b') ≥ (a − b)(1 + (a/n)(1 − a/n))` for the largest and second largest colour | P |
| `sum_count` | – | the counts add up to `n` | P |

### Plurality consensus, MAJ-4 (`TwoChoicesPlurality.lean`)

| Lean | Paper | Statement | Status |
| --- | --- | --- | --- |
| `distance_increases` | **Lemma 1** | `∃ z C`, `log n ≥ C`, `i` largest, `j` second largest, `c_i ≤ n/2`, `c_i − c_j ≥ z√(n log n)` ⇒ `P(c_i' − c_j' > (c_i − c_j)(1 + c_i/(4n))) ≥ 1 − C/n²` | P (`z = 128`, `C = 2`) |
| `count_stochDom` | **Lemma 2** | `c_c ≤ c_b` ⇒ `P(c_c' ≥ t) ≤ P(c_b' ≥ t)` for every `t` (stochastic domination) | P |
| `growth_round` | proof of Thm 1 | `∃ z C`, `log n ≥ C`, `a = c_i ≤ 3n/4`, every other colour `≤ a − g`, `g ≥ z√(n log n)` ⇒ w.p. `≥ 1 − C/n²`: `a' ≥ a` and every other colour `≤ a' − g(1 + a/(8n))` | P (`z = 128`, `C = 2`) |
| `growth_phase` | proof of Thm 1 | `∃ z C`, gap `≥ z√(n log n)` ⇒ after `⌈C (n/c_i) log n⌉` rounds `c_i ≥ 3n/4` w.p. `≥ 1 − C/n` | P (`z = 128`, `C = 128`) |
| `finish_phase` | proof of Thm 1 (two colours) | `log n ≥ 128`, `c_i ≥ 3n/4` ⇒ consensus on `i` after `⌈128 log n⌉` rounds w.p. `≥ 1 − 128/n` (via `run_dominates` and `Median.binary_consensus`) | P |
| `plurality_whp` | **Theorem 1** (upper bound) | `∃ z C`, `log n ≥ C`, `c_i − c_j ≥ z√(n log n)` for all `j ≠ i` ⇒ all nodes hold `i` after `⌈C (n/c_i) log n⌉` rounds w.p. `≥ 1 − C/n` | P |
| `plurality_whp_k` | roadmap form | the same after `⌈C k log n⌉` rounds | P |
| `two_colours_consensus_whp` | Section 2.1 (`k = 2`) | `Median.consensus_whp` transferred through `run_bool` | P |
| `absorbed` | proof of Thm 1, last paragraph (almost agreement) | from every configuration, consensus almost surely (`kernel` iterates of `notConsensus` tend to 0) | P |
| `expList_consensus_mono` | – | consensus on `i` is monotone in the number of rounds | P |

### The lower bound, MAJ-6 (a) (`TwoChoicesLower.lean`)

| Lean | Paper (Berenbrink et al.) | Statement | Status |
| --- | --- | --- | --- |
| `avg_exp_twice` | proof of Thm 3 | `𝔼 exp(θ · twice) = (1 + (c_i/n)²(e^θ − 1))^n` (the nodes seeing `i` twice are `n` independent Bernoulli variables) | P |
| `expected_see_distinct` | proof of Thm 3 | the expected number of nodes whose two samples differ (they keep their own colour) is `n − S/n` | P |
| `expected_changed_le` | proof of Thm 3 ("most nodes see two different colours and keep their own") | all colours `≤ ℓ` ⇒ the expected number of nodes changing colour is `≤ ℓ` | P |
| `colour_escape_le` | proof of Thm 3 (one colour) | `c_i ≤ L` ⇒ `P(∃ t ≤ T, c_i(t) > L) ≤ exp(−(L − c_i) + (e − 1) T L²/n)` | P (`θ = 1`) |
| `lower_bound_strong` | **Theorem 3** | `∃ γ₀`, `∀ γ ≥ γ₀`, all colours `≤ ℓ`, `ℓ' = max {2ℓ, γ log n}`, `T < n/(γ ℓ')` ⇒ `P(∃ t ≤ T, ∃ i, c_i(t) > ℓ') ≤ 1/n` | P (`γ₀ = 8`) |
| `consensus_time_lower` | **Theorem 1** (simplified, lower bound) | `∀ β > 0, ∃ C`: all colours `≤ β log n` and `(T + 1) C log n < n` ⇒ `P(consensus at some t ≤ T) ≤ 1/n` | P |

## Deviations from the source

1. **No bound on the number of colours in Theorem 1.** The paper assumes `k = O(n^ε)` for a
   small constant `ε`; it uses it only to make the multiplicative Chernoff bounds of Lemma 1
   applicable (`δ_i < 1`, which needs `a, b ≥ n^{1−ε}`). With Bernstein's inequality and the
   node-by-node variance (`Var(a' − c') ≤ 10 a²/n`), the deviation is `O(a √(log n/n) + log n)`
   for any `k`, which the drift `(a − b) a/(4n) ≥ z a √(log n/n)` absorbs. The pinned
   `distance_increases`, `growth_round`, `growth_phase` and `plurality_whp` therefore have no
   hypothesis on `k` (stronger statements). The variance bound holds node by node (a node of
   colour `i` or `j` contributes only when it leaves its colour, probability `≤ S/n² ≤ a/n`; any
   other node contributes `q_i + q_j ≤ 2a²/n²`), and with the deviation `λ = (a − b) a/(8n)` the
   Bernstein exponent is `≥ (a − b)²/(1344 n) ≥ (z²/1344) log n`: the failure probability of one
   colour is `n^{−z²/1344}` (`n^{−12}` for `z = 128`), so the union bound over the at most `n`
   colours present (absent colours stay absent) costs only a factor `n`. An exact computation of
   `Var(a' − c_j')` (`n` up to `10⁸`, from `k = 2` to `k ≈ n`, including `a ≈ z√(n log n)` and
   many colours of the size of the second largest) never exceeded `0.38 · 10a²/n`; Monte Carlo
   runs with `n = 2·10⁵` and up to `k ≈ 1.9·10⁵` colours, gap `2√(n log n)`, confirmed the
   one-round claims in every trial.
2. **The time bound is the paper's `O((n/c₁) log n)`**, and the roadmap's `O(k log n)` is the
   corollary `plurality_whp_k` (`c₁ ≥ n/k`).
3. **No adversary.** Theorem 1 also covers an `F = c₁(c₁ − c₂)/(8n)`-dynamic adversary
   (stabilizing near-plurality); this is not formalized (cf. roadmap MAJ-3 for the binary case).
   The lower-bound parts of Theorem 1 of Elsässer et al. and their Theorems 2 (a gap `O(√n)` loses
   with constant probability) and the `Ω(n/c₁ + log n)` run-time bound are not pinned.
4. **"w.h.p."** is `1 − C/n` (theorems) and `1 − C/n²` (one-round lemmas), with `∃ C` and the
   regime `log n ≥ C`. Lemma 1 is pinned with the paper's strict inequality and factor
   `1 + a/(4n)`.
5. **Lemma 2 as stochastic domination.** The paper states it as the existence of a coupling
   with `c' ≤ b'`; the pinned statement is the stochastic domination `P(c' ≥ t) ≤ P(b' ≥ t)`
   that such a coupling gives (the way it is used in the proof of Theorem 1). It is not needed by
   the formal route (Observation 1 and a per-colour Bernstein bound replace it) but is pinned as
   the paper's lemma.
6. **Proof route for Theorem 1.** The paper grows the gap while `a ≤ n/2` (Lemma 1), then appeals
   to the two-colour result of Cooper et al. once `a ≥ (1/2 + ε₁)n`. Formally: `growth_round` works
   up to `a ≤ 3n/4` with the factor `1 + a/(8n)` and also keeps `a` from decreasing, `growth_phase`
   reaches `a ≥ 3n/4`, and `finish_phase` uses the node-wise domination of the colour by the binary
   median process (`run_dominates`) and the existing `Median.binary_consensus`.
7. **Theorem 3 of Berenbrink et al.:** the largest support `ℓ` is generalized to any upper bound
   `ℓ` on all supports; `γ` ranges over all `γ ≥ γ₀` ("a sufficiently large constant"); the
   window `t < n/(γ ℓ')` is "every `t ≤ T` with `T < n/(γ ℓ')`". The proof's domination by a
   binomial process is replaced by an exponential supermartingale (`colour_escape_le`, with
   `θ = 1`), which needs no coupling.
8. **The roadmap's MAJ-6 (a) form** `consensus_time_lower`: "every colour has at most `β log n`
   nodes" (so `k ≥ n/(β log n)`) and the window `(T + 1) C log n < n`; consensus is
   `∃ c, run x l = fun _ => c`.

## Remarks on the sources

* Elsässer et al., **proof of Theorem 1** (needs a minor correction): Lemma 1 is proved for
  `a ≤ n/2`, but the hand-off to the two-colour process needs `a ≥ (1/2 + ε₁)n`, and the time
  bound `O((n/a) log n)` uses the initial `a` while the growth factor `1 + a/(4n)` uses the current
  one; both are repaired by `growth_round` (valid up to `3n/4`, and `a' ≥ a` w.h.p.).
* Elsässer et al., **proof of Lemma 2** (needs a minor correction): read literally (every node
  samples `π(v)` instead of `v`, the configuration unchanged), the coupling does not give
  `c' ≤ b'` pointwise, even under the lemma's hypotheses: for `n = 5`, colours
  `(A, A, A, B, C)`, it fails in 2 406 250 of the 9 765 625 rounds (the coupling moves the samples
  but not the nodes: a node of `C` that keeps its colour is not matched with a node of `B̂` that
  keeps its colour). The statement itself (as stochastic domination) holds in all 120 510 exact
  checks with `n ≤ 5`, `k ≤ 4`, and follows from a matching of nodes and of sample pairs
  (`count_stochDom`: a permutation `τ` sends the `c`-class into the `b`-class, and for each node a
  permutation of sample pairs embeds its adopting set into the image's; `Φ` reindexes rounds and
  preserves `avg`).
* Berenbrink et al., **proof of Theorem 3** (needs a minor correction of a constant): for
  `δ ≥ 1` the Chernoff bound `exp(−δμ/3)` at `(1 + δ)μ = max{2μ, (γ/2) log n}` gives
  `exp(−(γ/12) log n)`, not `exp(−(γ/6) log n)`; `γ ≥ 36` (instead of `18`) restores the
  `1/n³`. The theorem is unaffected ("`γ` sufficiently large").

## What was proved

Everything pinned is proved. Main new pieces, besides the pinned statements:

* `Median/TwoChoicesConc.lean` (635 lines): one-round Bernstein bounds. `gap_dev_le` (variance
  `≤ 10 a²/n`, deviation `λ`, bound `2`) and `count_dev_le` (variance `≤ 2 a²/n`). The node-wise
  variance uses `variance f ≤ avg ((f − y₀)²)`, with `y₀ ∈ {−1, 0, 1}` according to the node's
  colour. `gap_tail_twelve` and `count_tail_twelve` turn the exponent into `n^{−12}` for `z = 128`.
* `distance_increases` and `growth_round` (`growth_round_aux`) call those tails with
  `λ = g a/(8n)` and, for the count, `λ = a g/(4n)`. Failure of one round is at most `2/n²`.
* `stay_three_quarters`: if `a ≥ 3n/4` and `log n ≥ 128`, then `P(a' ≥ 3n/4) ≥ 1 − 1/n²`
  (`count_dev_le`, drift from `sum_sq_le_aggregate`, split at `7n/8`).
* `growth_phase`: `Dynamics.expList_escape` on `growthSet`, with ratio `q = 1 + a₀/(8n)`.
  `growth_ratio_pow_gt` gives `q^{⌈128 (n/a₀) log n⌉} > n`, so the gap cannot fit in `n` nodes
  unless the count has already reached `3n/4`. The escape failure is at most `128/n`.
* `count_stochDom`: `pairBoth`, `pairAgreeOff`, `adoptPairs`, `adoptPairs_card_le`, then
  `Equiv.Perm.exists_map_finset_eq` twice and `Dynamics.avg_equiv`. No `[Fintype α]`.
* `colour_escape_le`: induction on the horizon, inner term `≤ Φ_T(count (step x r) i)`, averaged
  by `avg_exp_twice` and `(1 + q(e−1))^n ≤ exp(n q (e−1))`. `lower_bound_strong` unions over the
  colours with positive count (`≤ n` of them) and gets `≤ 1/n`.

Line counts: `TwoChoicesDefs.lean` 185, `TwoChoicesExpect.lean` 235, `TwoChoicesConc.lean` 635,
`TwoChoicesPlurality.lean` 1511, `TwoChoicesLower.lean` 495, `TwoChoices.lean` 19.
