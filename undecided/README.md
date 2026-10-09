# The undecided-state dynamics

Synchronous undecided-state dynamics with two opinions, and with `k` colours, on the complete graph (each node samples one node uniformly, with replacement). Main results in [`Undecided/Basic.lean`](Undecided/Basic.lean), namespace `Undecided`; see the
[blueprint](blueprint/src/content.tex) for the statements and the map to Lean declarations.

## Majority phase (UND-1)

After Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip
model* (SODA 2015, Theorem 11 with two colours) and Clementi, Ghaffari, Gualà, Natale, Pasquale
and Scornavacca (MFCS 2018, Theorem 3.2). Results in
[`Undecided/Majority.lean`](Undecided/Majority.lean) and
[`Undecided/MajorityAssembly.lean`](Undecided/MajorityAssembly.lean), namespace `Undecided`:

| Result | Lean declaration |
| --- | --- |
| A round leaves the counts of `a`, `b` and undecided nodes within `Λ` of their expectations except with probability `4 exp(-2Λ²/n)` | `bad_round` |
| Explicit form: if `log n ≥ 10⁴` and `count a - count b ≥ 10⁴ √(n log n)` (any number of undecided nodes), not all nodes hold `a` after `⌈10⁴ log n⌉` rounds with probability at most `2/n` | `majority_explicit` |
| MFCS 2018, Theorem 3.2: there is `C` such that, if `log n ≥ C` and `count a - count b ≥ C √(n log n)`, all nodes hold `a` after `⌈C log n⌉` rounds with probability `≥ 1 - C/n` | `majority_whp` |
| The same for either opinion (`|count a - count b| ≥ C √(n log n)`, the initial majority wins) | `majority_whp_abs` |
| SODA 2015, Theorem 11 for two colours: no undecided nodes and `count a ≥ (1 + α) count b` | `majority_whp_of_ratio` |

The proof uses Hoeffding's inequality in every round and three phases (growth of the bias, a
bridge, contraction of the potential `12 count b + count u`) composed by the Markov property; see
[`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md) for the route and the differences
from the papers.

## Many colours (UND-3)

After Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip
model* (SODA 2015, arXiv:1407.2565, Theorem 11). The `k`-colour dynamics is in
[`Undecided/PluralityBasic.lean`](Undecided/PluralityBasic.lean) (namespace
`Undecided.Plurality`; a configuration is `Fin n → Option (Fin k)`, `none` meaning undecided),
the main theorem in [`Undecided/Plurality.lean`](Undecided/Plurality.lean). With `cᵢ` the number
of nodes of colour `i` and `md(c) = ∑ᵢ (cᵢ / maxⱼ cⱼ)²` the monochromatic distance:

| Result | Lean declaration |
| --- | --- |
| Expected counts after one round (the paper's (3) and (4)): `E[c'ᵢ] = cᵢ (cᵢ + 2q)/n`, `E[q'] = (q² + (n - q)² - ∑ᵢ cᵢ²)/n` | `expected_count_some`, `expected_count_none` |
| `1 ≤ md(c) ≤ k` (the paper's (1)) | `one_le_md`, `md_le_card` |
| The binary dynamics of `Undecided/Basic.lean` is the case `k = 2` | `step_two`, `foldl_two`, `count_two` |
| A round in which some count leaves its concentration window (deviation `√(3ℓ(µ + 2ℓ))` from its mean `µ`) has probability at most `(k + 4) e^{-ℓ}`, that is `(k + 4)/n³` for `ℓ = 3 log n` | `bad_le` |
| Explicit form: with `C = 10⁵ ((1 + α)²/α)²`, `log n ≥ C` and `(C k)³ log n ≤ n`, consensus on `m` fails after `⌈C md(x) log n⌉` rounds with probability at most `6/n` | `plurality_explicit` |
| SODA 2015, Theorem 11: for every `α > 0` there is `C` such that, if `log n ≥ C`, `C k ≤ (n / log n)^{1/3}`, there are no undecided nodes and `(1 + α) cᵢ ≤ c_m` for all `i ≠ m`, all nodes hold `m` after `⌈C md(x) log n⌉` rounds with probability `≥ 1 - C/n` | `plurality_whp` |

The range of `k` is the paper's exponent `1/3` with a small constant depending on `α`; see
[`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md) for the reasons and the proof
route (Bernstein per round, an invariant on the colour ratios, growth of `c_m (c_m + 2q)/n`, and a
final contraction), in
`Undecided/Plurality{Conc,Round,Alg,Arith,Steps,Progress,Stages,Assembly}.lean`.

### The `Ω(md(c))` lower bound

The same paper (SODA 2015, Theorem 8 with Lemmas 3, 6 and 7) shows that, without any bias, the
dynamics needs `Ω(md(c))` rounds: after the first round most nodes are undecided, their number
descends to about `n/2` within `O(log n)` rounds while no colour exceeds `O(n/md(c))` nodes, and
then no colour grows faster than by a factor `1 + O(1/md(c))` per round. Main theorems in
[`Undecided/LowerBound.lean`](Undecided/LowerBound.lean), with `R(c) = ∑ᵢ cᵢ / maxⱼ cⱼ`
(`ratioR`) and `Λ(c) = R(c)²/md(c)` (`ratioLam`, in
[`Undecided/LowerBoundBasic.lean`](Undecided/LowerBoundBasic.lean)); all constants are
existential:

| Result | Lean declaration |
| --- | --- |
| `md ≤ R ≤ k`, `md ≤ Λ ≤ k`, and the expectations in terms of `δ = q - n/2` (the paper's (19) and (20)) | `md_le_ratioR`, `ratioR_le_card`, `md_le_ratioLam`, `ratioLam_le_card`, `mu_eq_half`, `muU_sub_half` |
| Lemma 3 (first round): from a configuration without undecided nodes, w.h.p. every colour has at most `2n/R²` nodes, the plurality at least `n/(2R²)`, and `n(1 - 2/Λ) ≤ q ≤ n(1 - 1/(2Λ))` | `first_round` |
| Lemma 6 (descent): w.h.p. the undecided nodes reach `n/2 ± 2γ² n/md(c)` within `O(log n)` rounds, while every colour stays at most `γ n/md(c)` | `undecided_square`, `undecided_not_below`, `descent` |
| Lemma 7 (plateau): from there, w.h.p. every colour stays at most `2γ n/md(c)` for `Ω(md(c))` rounds | `plateau_step`, `plateau` |
| SODA 2015, Theorem 8: there is `C` such that, if `log n ≥ C`, `C k ≤ (n / log n)^{1/6}` and there are no undecided nodes, then after every `T ≤ md(x)/C` rounds every colour has at most `C n/md(x)` nodes with probability `≥ 1 - C/n`; if `C(T + 1) ≤ md(x)`, all nodes hold the same colour after `T` rounds with probability at most `C/n` | `lower_bound_whp`, `lower_bound_consensus` |

Lemmas 6 and 7 need minor corrections (a missing factor `n`, the growth factor of Lemma 7, the
direction of a Cauchy–Schwarz bound, bounds on the largest colour rather than the initial
plurality); see [`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md) for these and the
proof route, in `Undecided/LowerBound{Basic,Arith,Round,First,DescentCore,Descent,Plateau}.lean`.

## Sequential version (UND-2)

[`Undecided/SequentialMain.lean`](Undecided/SequentialMain.lean)
formalizes the approximate-majority protocol of Angluin, Aspnes and Eisenstat (Distributed
Computing 2008), one uniformly random ordered pair of agents per step: from any non-blank
configuration consensus within `O(n log n)` interactions, and from a gap of `C √n log n` the
initial majority wins, each with probability `1 - O(n^{-c})` for every `c` (`consensus_whp`,
`majority_whp`, `approximate_majority`). The proof uses six weighted supermartingales along finite
paths; see [`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md) for the route and the
deviations from the paper.

## Provenance

For `Undecided/Basic.lean`, the statements were written and pinned by a second agent; the
proofs were produced by a Grok agent under a fixed-statement protocol and verified mechanically
(statements unchanged, no placeholders, warning-free build, axiom audit). The sequential
statements and their proofs were written by a Claude agent under the same protocol; the statements
were reviewed by a second agent against the paper. The majority-phase statements (`Majority*`) and their
proofs were written by a Claude agent under the same protocol. The `k`-colour statements (`Plurality*`) and their proofs
were written by a Claude agent under the same protocol; the statements were reviewed by a second
agent against the paper. The lower-bound statements (`LowerBound*`) were pinned by a Claude agent
and reviewed by a second agent; their proofs were produced by a Grok agent under the same
protocol.

## Build

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
