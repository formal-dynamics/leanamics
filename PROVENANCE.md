# Provenance of the results

For every main result of the library: the paper it comes from, whether the formal proof
follows a published proof (and how it deviates) or takes a different route, the explicit
size and constant hypotheses of the Lean statement, and who or what produced the proof.

**When you add or change a result, add or update its entry here.** If a source is unknown,
say so rather than guessing.

## Explicit constants

Where a paper proves a statement "for sufficiently large `n`", the Lean statement makes the
threshold explicit. These thresholds come from the constants of the published proofs (or of
our elementary proofs), and some are astronomically large:

| Result | Size hypothesis | Population size it means |
| --- | --- | --- |
| `ThreeMajority.majority3_consensus_whp` | `30 ≤ log n` | `n ≥ e³⁰ ≈ 1.1 · 10¹³` |
| `Plurality.theorem_3_8`, Corollaries 3.10–3.12, `majority3_vanishing_bias` | `40 ≤ log n` | `n ≥ e⁴⁰ ≈ 2.4 · 10¹⁷` |
| `Plurality.theorem_4_8_b` | `20 ≤ log n`, `60 ∣ n` | `n ≥ e²⁰ ≈ 4.9 · 10⁸` |

The statements are correct as asymptotic `O(log n)` results, but they say nothing about
realistic population sizes. Lowering these thresholds is a roadmap target (MAJ-11). Results
not listed here have no size hypothesis beyond `n ≥ 1` or `n ≥ 2`.

## Results

"Pinned" means that a human wrote and froze the definitions and statements, and an AI agent
wrote the proofs under the fixed-statement protocol: statements byte-identical to the pinned
baseline, no placeholders, a warning-free build, and only standard axioms.

### Rumor spreading (`rumor_spread/`)

| Result | Source | Proof | Constants | Produced by |
| --- | --- | --- | --- | --- |
| `RumorPush.push_informs_all_whp`: push on `K_n` informs every node in `O(log n)` rounds w.h.p. | Classical; no specific paper is formalized. The blueprint cites Frieze–Grimmett (DAM 1985) and Pittel (SIAM J. Appl. Math. 1987) for the sharp bound `log₂ n + ln n`. | Own elementary proof (`latex/rumor_push.tex`): growth phase via good rounds and the moment bound `𝔼[(1/2)^good] ≤ (15/16)^T`, then contraction of the uninformed by 2/3 per round and Markov. No Chernoff bound. | `2 ≤ n`; `(⌈117 log n⌉ + 23) + ⌈6 log n⌉` rounds; failure `≤ 2/n` | Aakash Kumar, imported from a separate repository (commit 9da2dc2 records a Claude co-author); PR #1 |

### Majority dynamics (`3-majority/`, `plurality/`)

| Result | Source | Proof | Constants | Produced by |
| --- | --- | --- | --- | --- |
| `ThreeMajority.majority3_consensus_whp`: two opinions, from a 3/5 majority, consensus in `O(log n)` rounds | No specific paper is formalized (the blueprint cites Doerr et al., SPAA 2011, and Becchetti et al., SODA 2015, for the sharper `√(n log n)` regime). | Own elementary proof (`latex/three_majority.tex`): exact one-round map `3x² − 2x³`, a mean-scaled Chernoff bound proved from `1 + x ≤ eˣ`, growth from `[3/5, 3/4]`, then contraction of the minority and a final Markov step. | `30 ≤ log n`; `10 + ⌈6 log n⌉ + 2` rounds; failure `≤ 500/n` | Aakash Kumar, imported (commit 9965e34 records a Claude co-author); PR #2 |
| `Plurality.theorem_3_8` (and `theorem_3_8_bigO`): `k` colors from a bias `22√(λ n log n)` | Becchetti, Clementi, Natale, Pasquale, Silvestri, Trevisan, *Simple dynamics for plurality consensus*, SPAA 2014, Theorem 3.8 | Follows the SPAA proof with repairs (`plurality/FORMALIZATION_DIFFERENCES.md`): the saturation phases are redefined, a missing union bound over colors is added (per-round failure `1/n` instead of `1/n²`), `λ < √n` is dropped, `k ≥ 2` is added, and Lemma 3.7 (unproved in the paper) gets a proof. The journal version's proof was checked and not used. | `40 ≤ log n`; `≤ 130 λ log n` rounds (paper: `100 λ log n`); failure `11T/n` (paper: `11T/n²`) | Maria Sofia Bucarelli (commit 4510132 records a Claude co-author); PR #6 |
| Corollaries 3.10–3.12, Theorem 4.2, Theorem 4.8 (a, b), Lemma 4.11, Theorem 4.12 | Same paper | Follow the paper with the deviations of `FORMALIZATION_DIFFERENCES.md` §3: Theorem 4.2 holds for `k ≤ n^{1/4−δ}`; Theorem 4.8 (a) leaves open the rules with `Δ_r, Δ_b ≤ 1`; Lemma 4.11 has factor `1 + 2h²/k`. Observation 3.9 is not formalized. | 3.10–3.12: `40 ≤ log n`; 4.8 (b): `20 ≤ log n`, `60 ∣ n` | As above |
| `Plurality.binary_consensus_whp`: `k = 2` from 3/5 | Same paper, case `k = 2` | Reuse of `majority3_consensus_whp` through the pathwise bridge `colorSet_run` | as `majority3_consensus_whp` | As above |
| `Plurality.majority3_vanishing_bias`: two opinions from a gap `22√(3 n log n)` | Same paper, Theorem 3.8 with `k = 2`, `λ = 3` (roadmap MAJ-2b) | Corollary of `theorem_3_8_bigO`, transferred to `ThreeMajority.run` through `colorSet_run` | `40 ≤ log n`; `≤ 390 log n` rounds; failure `≤ 429 log n / n` | Emanuele Natale with Claude (Anthropic); PR #13 |

### Voter model (`voter/`)

| Result | Source | Proof | Constants | Produced by |
| --- | --- | --- | --- | --- |
| `Voter.consensus_probability` (and the uniform, regular and many-color corollaries): consensus on a color with probability equal to its stationary mass | Hassin, Peleg, *Distributed probabilistic polling and applications to proportionate agreement*, Information and Computation 171 (2001), Sections 2.1–2.3 | Follows the paper's martingale and absorption argument, with the deviations of `voter/FORMALIZATION_DIFFERENCES.md`: a "without loss of generality" step of Lemma 2.1 is repaired, absorption probabilities are suprema of finite-time probabilities (no path space), any stationary distribution works, self-loops are allowed. | none | Niccolò D'Archivio (commit 8b91ab2); PR #3 |
| `Voter.voter_consensus_whp`: consensus on `K_n` (with self-loops) within `2 n log n` rounds w.p. `≥ 1 − 1/n` | Hassin–Peleg §2.4; Becchetti, Clementi, Natale, *Consensus dynamics: an overview*, SIGACT News 2020, Theorems 6–7 | Duality with backward coalescing random walks, the exact meeting probability `(1 − 1/n)^T`, and a union bound | `2 n log n ≤ T` | Pinned (7fcb31f); proofs by a Grok agent (grok-4.7, ~30 min); PR #5 |

### Moran process (`moran/`)

| Result | Source | Proof | Constants | Produced by |
| --- | --- | --- | --- | --- |
| `Moran.isothermal`, `isothermal_neutral`, `moran_formula`: the "if" direction of the isothermal theorem, Moran's formula | Lieberman, Hauert, Nowak, *Evolutionary dynamics on graphs*, Nature 2005; Moran 1958. The "if and only if" is false (Galanis et al., J. ACM 2017, Prop. 12). | Different from the classical proof: an invariant potential `(1/r)^{#mutants}` and the generic absorption theorem (`fixation_eq_of_invariant`), avoiding the projection onto the number of mutants, which is not Markov in general (Keller–Uğurlu, arXiv:2403.12598, give a martingale proof) | exact formulas; `0 < r`, `r ≠ 1` | Pinned (d06dc8a); proofs by a Grok agent (grok-4.7, ~1 h); PR #7 |
| `Moran.push_fixation`, `pull_fixation`: neutral push/pull fixation on any connected graph | Antal, Redner, Sood, PRL 96 (2006), which derive the formulas by a mean-field approximation | Exact proof: invariant reproductive values (`1/deg` for push, `deg` for pull) and the generic absorption theorem | exact; connected, `n ≥ 2` | Pinned (e58cb55); proofs by a Grok agent (grok-4.7, ~32 min); PR #8 |

### Epidemics (`epidemics/`)

| Result | Source | Proof | Constants | Produced by |
| --- | --- | --- | --- | --- |
| `Epidemics.infected_iff`, `recovered_iff`, `final_recovered_iff`, `prob_infected_eq_prob_connected`: Reed–Frost ⇔ bond percolation, pathwise | Kempe, Kleinberg, Tardos, KDD 2003 (live-edge coupling); Becchetti et al., arXiv:2103.16398, Theorem A.3 | BFS layers of the percolated graph, one coin per edge. Stronger than the usual distributional statement with fresh coins, which is not formalized. | exact; `card V` rounds | Pinned (fa01243); proofs by a Grok agent (grok-4.7, ~26 min); PR #11 |

### Undecided-state dynamics (`undecided/`)

| Result | Source | Proof | Constants | Produced by |
| --- | --- | --- | --- | --- |
| `Undecided.expected_count_*`, `expected_bias` (factor `1 + q/n`), `absorbed` | Basic laws of the dynamics, as in the survey (Becchetti, Clementi, Natale, SIGACT News 2020, §6); no specific proof is formalized | Exact per-node probabilities summed over nodes; absorption via the shared `finite_absorption` | exact | Pinned (cb62f04); proofs by a Grok agent (grok-4.7, ~27 min); PR #12 |

### Averaging dynamics (`averaging/`)

| Result | Source | Proof | Constants | Produced by |
| --- | --- | --- | --- | --- |
| `Averaging.tendsto_degAvg`: convergence to the degree-weighted average; `not_tendsto_of_colorable` | Classical (survey §7.2) | Different from the survey's spectral argument: walk weights, a common walk length (parity fixed by the odd closed walk), and a Doeblin contraction of `max − min`. No spectral theorem. | none; connected with an odd closed walk | Pinned (f18d21d); proofs by a Grok agent (grok-4.7, ~66 min); PR #12 |

### Shared layer (`dynamics/`)

| Result | Source | Proof | Produced by |
| --- | --- | --- | --- |
| `Dynamics.Kernel.nested_phases` | Lemma A.4 of the SPAA 2014 plurality paper, stated there without proof (dropped in the journal version) | Phase by phase with a survival observable; the paper's hypothesis `ε ≤ ν` is not needed | Maria Sofia Bucarelli; PR #6 |
| `Dynamics.Kernel.finite_absorption`, `exists_stationary` | Standard | Uniform absorption blocks and geometric decay; stationarity via Cesàro averages and compactness of the simplex | Niccolò D'Archivio; PR #3 |

## In progress

- **Median dynamics / 2-Choices** (`median/`, roadmap MAJ-1): Doerr, Goldberg, Minder,
  Sauerwald, Scheideler, *Stabilizing consensus with the power of two choices*, SPAA 2011.
  Structural results proved by GLM-5.3 (Mistral API, via Mistral Vibe) on a pinned baseline;
  consensus from a gap `C √(n log n)` in progress. The constant `C` will be recorded here.
