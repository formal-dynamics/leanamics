# Leanamycs roadmap

Results we would like to see formalized next, grouped into tracks. Every target has a
stable **ID** (`VOT-3`, `MAJ-4`, …), a source, the infrastructure it needs, a size estimate
and a status.

## How to contribute

1. **Pick a target** whose status is `open`. Check the
   [open issues](https://github.com/formal-dynamics/leanamycs/issues) in case someone has
   just claimed it.
2. **Open an issue** titled `[ID] short name` (for example `[EPI-1] Reed–Frost ⇔ bond
   percolation`) saying that you are working on it. That's all it takes to claim a target, and
   it prevents duplicated work. If you stop, say so in the issue so the target goes back to `open`.
3. **Open a pull request** when you have something to show. Drafts are welcome. Follow the
   project layout described in the [README](README.md): a separate Lake package (or an
   extension of an existing one), a blueprint with `\lean{}` tags, and a `sorry`-free build.
4. Want to propose a result that is not listed? Open an issue; the roadmap is meant to grow.

Status values: `open` · `claimed (#issue)` · `in review (#PR)` · `done`.

Done results are documented in [PROVENANCE.md](PROVENANCE.md): source paper, proof route
(published proof followed, with deviations, or a different proof), explicit constants and
authorship. When a target is done, add its entry there.

Sizes (rough, for someone fluent in Lean + Mathlib): **S** days · **M** 1–3 weeks ·
**L** 1–3 months · **XL** research-level.

## Design principles to preserve

All existing developments use a **finite probability layer**: randomness lives on finite
types, expectations are finite sums, and multi-round processes are handled by recursion on
the number of rounds (`expList`) or by iterating finite stochastic kernels. There is no
measure theory, no `PMF`/`ENNReal`, and no appeal to Mathlib's `ProbabilityTheory`. Absorption
probabilities ("eventually reaches consensus") are limits of finite-time probabilities, not
events in a path space. Most targets below fit this layer. The few that cannot are marked.

**Build on `dynamics/`.** The shared `dynamics/` package (merged in
[#3](https://github.com/formal-dynamics/leanamycs/pull/3), together with `voter/`) provides
weighted finite distributions, finite kernels, stationary distributions and geometric
absorption. New targets should use `dynamics/` rather than growing another private copy of
the probability layer.

## The dictionary behind the tracks

The same few Markov chains appear under different names in distributed computing,
population genetics, epidemiology and chemistry. Several targets turn this dictionary into
theorems.

| Distributed computing | Population genetics | Epidemiology | Chemistry (CRN) |
| --- | --- | --- | --- |
| Synchronous PULL voter on `K_n` with self-loops | Neutral Wright–Fisher (each offspring picks a uniform parent) | – | – (synchronous rounds) |
| Sequential PULL voter on a graph | Neutral Moran, death–Birth (dB) | – | on `K_n`: `X + Y → X + X`, `X + Y → Y + Y` (equal rates) |
| Sequential PUSH voter on a graph | Neutral Moran, Birth–death (Bd) | – | on `K_n`: same as the row above |
| PUSH with fitness-biased senders | Moran Bd with mutant fitness `r` | – | `M + W → M + M` (rate `r`), `M + W → W + W` (rate `1`): same jump chain |
| Voter ⇔ coalescing random walks | Wright–Fisher/Moran ⇔ coalescent | – | – |
| Sequential Undecided-State dynamics | – | – | approximate majority `X + Y → X + B`, `X + Y → Y + B`, `B + X → X + X`, `B + Y → Y + Y` (the cell-cycle switch) |
| PUSH rumor spreading (`rumor_spread/`, synchronous) | – | SI epidemic | sequential version: `S + I → I + I` |
| – | – | Daley–Kendall rumour model | `X + Y → 2Y`, `2Y → 2Z`, `Y + Z → 2Z` (ignorant, spreader, stifler) |
| COBRA walk (push to `k` neighbours) | – | BIPS infection (dual process) | – (synchronous rounds) |
| Independent Cascade | – | Reed–Frost SIR ⇔ bond percolation | continuous-time SIR `S + I → 2I`, `I → R`; its mass-action ODE is Kermack–McKendrick |

In the chemistry column, reactions belong to a well-mixed stochastic CRN. Count-conserving
bimolecular reactions with a common rate constant are exactly population protocols on `K_n`
(CRN-1), and unequal rate constants give a weighted scheduler, as for Moran fitness.
Synchronous-round dynamics (Wright–Fisher, 3-Majority, the rounds of `rumor_spread/`) have no
CRN counterpart, since a CRN has no global clock (Doty, SODA 2014); their sequential versions do.

On graphs, the push/pull asymmetry is exactly the Bd/dB asymmetry of evolutionary graph
theory (Hindersin–Traulsen 2015: most random graphs amplify selection under Bd but suppress
it under dB).

---

## FND: foundations

| ID | Item | Needs | Size | Status |
| --- | --- | --- | --- | --- |
| FND-1 | Shared `dynamics/` package (uniform and weighted finite distributions, independent products, pushforward). | – | – | done (#3) |
| FND-2 | Finite kernels and absorption: uniform absorption blocks ⇒ geometric survival bound ⇒ absorption limit (`Dynamics.Kernel.finite_absorption`). | FND-1 | – | done (#3) |
| FND-3 | **Chernoff for independent, non-identical Bernoulli(pᵢ)** on `Distribution` products. Today's Chernoff lives in `3-majority/` and is stated for uniform sampling. | FND-1 | M | open |
| FND-4 | **Finite-horizon optional stopping.** If `𝔼[φ(X_T)] = φ(X₀)` for all `T` and survival → 0, then the absorption probability is `(φ(x₀) − φ(B))/(φ(A) − φ(B))`. `voter/` proves this pattern inline (`whiteProbability_error`); extract it as a reusable lemma. | FND-2 | S | open |
| FND-5 | **Expectation-level drift lemma.** If a nonnegative potential satisfies `𝔼[Ψ_{t+1} ∣ X_t] ≤ Ψ_t − c/Ψ_t` while not absorbed, then (by Jensen and iterating on `𝔼[Ψ_t]`) absorption happens by time `O(Ψ₀²/c)` with probability `≥ 1/2`. This is the argument of Berenbrink et al. (ICALP 2016, Lemma 2.2); it uses no concentration, so it fits the finite layer directly. | FND-2 | S–M | open |
| FND-6 | **Time reversal of i.i.d. rounds:** `expList α T (F ∘ List.reverse) = expList α T F` (from `Equivalence`). | FND-1 | S | open |
| FND-7 | **Graph-indexed rounds:** every vertex samples a uniform neighbour (product of subtypes, as `rumor_spread`'s `Tgt`), plus a sequential "one random node/edge per step" round type. | FND-1 | S | open |

## VOT: voter model, Wright–Fisher, coalescence

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| VOT-1 | **Hassin–Peleg proportionate agreement.** Weighted synchronous voter: colour `i` wins with probability equal to its initial stationary mass (`d(v)/2m` for uniform neighbours). | Hassin–Peleg 2001; Survey Thm 4 | FND-2 | – | done (#3) |
| VOT-2 | **Neutral Wright–Fisher and the lazy voter.** Allele `i` fixes with probability `cᵢ/n`. Since #3 the voter theorem only needs `G.Adj i j → 0 < H i j`, so kernels with self-loops are allowed (example: `Voter.Examples.wrightFisher_one_third`, three individuals). Remaining: state Wright–Fisher on `K_n` (`n ≥ 3`) and the lazy voter (`H = (I + D⁻¹A)/2`, needed by VOT-5) as corollaries. Optional extension: drop non-bipartiteness when some `H i i > 0` (Hassin–Peleg's Remark, p. 254), which needs self-loop rounds in the propagation argument. | classical | VOT-1 | S | open |
| VOT-3 | **Voter ⇔ coalescing random walks; `O(n log n)` consensus on `K_n`.** Pathwise, `c_T(u) = c₀(r₁(r₂(⋯r_T(u))))`, so consensus follows once the backward map `r₁ ∘ ⋯ ∘ r_T` is constant, i.e. once the coalescing walks have met. On `K_n` with self-loops, backward walks from two distinct vertices have not met after `T` rounds with probability exactly `(1 − 1/n)ᵀ`; a union bound over the walks that must meet a fixed vertex gives consensus within `2n ln n` rounds w.p. `≥ 1 − 1/n` (`Voter.voter_consensus_whp`). | Survey Thms 6–7; Hassin–Peleg §2.4 | FND-1 | M | done (#5) |
| VOT-4 | **Push vs pull neutral fixation (sequential).** From mutant set `S` on a connected graph: pull (dB) fixes w.p. `vol(S)/2m`; push (Bd) fixes w.p. `∑_{v∈S} 1/d(v) / ∑_{v∈V} 1/d(v)`. Each follows exactly from a one-step invariant (`φ = d`, resp. `φ = 1/d`); both formulas were checked against exact absorbing-chain solutions on an irregular 6-vertex graph. | Antal–Redner–Sood, PRL 2006 ("voter model dynamics" ∝ `k`, "invasion process" ∝ `1/k`, derived there by approximation for heterogeneous networks) | FND-4, FND-7 | S–M | done (#8) |
| VOT-5 | **Consensus time `O(m/(d_min·φ))`** for the *lazy* synchronous voter (adopt the sampled neighbour's opinion w.p. 1/2) on any graph with `m` edges, conductance `φ` and minimum degree `d_min`. Precisely: w.p. `≥ 1/2`, `T ≤ min{m/(d_min φ), n log n/φ²}` up to constants, hence the expectation bound by restarting; dynamic graphs with fixed degrees too. Proof plan from the paper: the concave potential `Ψ = √vol(minority side)` drops by `∑_u λ_u d_u / (32Ψ³)` per round in expectation (Lemma 2.1; the paper notes the plain volume does not work), FND-5 turns this into time (Lemma 2.2), and a phase argument handles `κ > 2` opinions (Lemma 2.3). A 2026 follow-up (Rocha Avila–Dell–Lapinskas, arXiv:2606.13374) extends the bound to temporal conductance and proves it tight. | **Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn**, *Bounds on the voter model in dynamic networks*, ICALP 2016, [arXiv:1603.01895](https://arxiv.org/abs/1603.01895) | VOT-2, FND-5, FND-7 | M–L | open |
| VOT-6 | **`O(n³ log n)` consensus on any connected graph** via meeting times of random walks. | Survey Thm 8; Hassin–Peleg Thm 2.5 | VOT-3 | L | open |

## MOR: Moran process

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| MOR-1 | **Moran's formula.** Bd Moran on `K_n`, mutant fitness `r`: from `i` mutants, fixation probability `(1 − r^{−i})/(1 − r^{−n})`. In every state `P(up)/P(down) = r`, so `r^{−X_t}` is invariant (FND-4). | Moran 1958 | FND-1, FND-4 | M | done (#7) |
| MOR-2 | **Isothermal theorem ("if" direction).** On every regular graph (more generally, a doubly-stochastic weight matrix) the ratio is still exactly `r` in every configuration, so MOR-1's formula holds verbatim from *every* initial mutant set (checked exactly on the Petersen graph; the star is a control where it fails). Why a formal proof is worth having: the widely quoted "if and only if" is false (Galanis et al., Prop. 12: a non-isothermal 3-vertex weighted graph with the Moran fixation probability; the formal statement in LHN05's supplement is correct), and the classical proof projects onto the mutant count, which need not be Markov. Keller–Uğurlu (arXiv:2403.12598) give a martingale / optional-stopping proof, which is the natural blueprint here. | Lieberman–Hauert–Nowak, Nature 2005 | MOR-1, FND-7 | M | done (#7) |
| MOR-3 | **Amplifiers and suppressors (stretch).** Exact fixation on the star; [Gia16]'s `1 − Ω̃(n^{−1/3})` upper bound for undirected graphs and its strong amplifier/suppressor; the `Ω(n^{−1/2})` extinction lower bound for strongly connected digraphs [GLLMPP18]; megastars [GGGLR17]; polynomial absorption time [DGMRSS14]. This literature has already had published claims corrected (Díaz et al. 2013 on superstars). | see References | MOR-2 | XL | open |

## EPI: epidemics, percolation, information spreading

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| EPI-1 | **Reed–Frost ⇔ bond percolation, pathwise.** With one coin per edge, the Independent Cascade process has `I_t` = nodes at `G_p`-distance exactly `t` from `I₀` and `R_t` = distance `< t`. This holds because each edge is examined at most once: after its flip, one endpoint stays recovered forever. Hence the epidemic lasts at most the largest finite `G_p`-distance from `I₀`, so `τ ≤ n − 1` (not `diam(G)`: on `K_n` the open edges can form a path). This coupling is stronger than the distributional equivalence usually stated, and easier to formalize. | [BCDPTZ22] Thm A.3, after Kempe–Kleinberg–Tardos | FND-1 | S–M | in review |
| EPI-2 | **Subcritical ⇒ small outbreaks.** Max degree `d`, `p < (1−ε)/(d−1)` ⇒ w.h.p. every component of `G_p` has size `O_ε(log n)`. Corollaries: Reed–Frost with `R₀ < 1` infects `O(\|I₀\| log n)` nodes (via EPI-1), and subcritical Erdős–Rényi. The formal crux is the principle of deferred decisions: couple the adaptive BFS to one i.i.d. coin sequence consumed in exploration order. | [BCDPTZ22] Thm 2.3/E.1 | EPI-1, FND-3 | M–L | open |
| EPI-3 | **Supercritical giant component.** `G(n,(1+ε)/n)` has a linear-size component w.h.p., by the DFS argument of Krivelevich–Sudakov (needs only Chernoff). Epidemic reading: Reed–Frost on `K_n` with `R₀ = pn > 1` infects `Ω(n)` nodes w.p. `Ω(1)`. | Krivelevich–Sudakov, RSA 2013 | FND-3 | L | open |
| EPI-4 | **COBRA ⇔ BIPS duality.** COBRA walk: each informed vertex pushes to `k` random neighbours, then stays silent until informed again. BIPS epidemic (SIS type): a persistent source `v`; every other vertex samples `k` neighbours and is infected iff one of them was infected in the previous step. Duality (paper's Thm 4, connected regular `G`, any `k ≥ 1`): `P(COBRA from C has not hit v by t) = P(C ∩ A_t = ∅ ∣ A₀ = {v})` for all `C, v, t`, proved by induction on `t` with one-step conditioning, an ideal fit for the finite layer. The paper's consequence: COBRA cover time `O(log n)` on `r`-regular graphs with `1 − λ` bounded below by a constant. Formalize the duality first (S–M), then the bound (L). | **Cooper, Radzik, Rivera**, *The coalescing-branching random walk on expanders and the dual epidemic process*, PODC 2016, [arXiv:1602.05768](https://arxiv.org/abs/1602.05768) | FND-7 | S–M / L | open |
| EPI-5 | **SI epidemics beyond PUSH:** PULL and PUSH–PULL rumor spreading on `K_n`, next to `rumor_spread/`; optionally the sharp `log₂ n + ln n` for PUSH (Frieze–Grimmett, Pittel). | classical | – | M (L sharp) | open |
| EPI-6 | **Small-world SIR thresholds (stretch).** Critical `p = (√(c²+6c+1) − c − 1)/(2c)` for cycle + `G(n,c/n)`, and `1/2` for cycle + random matching. | [BCDPTZ22] Thms 2.1, 2.2, 2.4, 2.5 | EPI-2, EPI-3 | XL | open |
| EPI-7 | **Kermack–McKendrick SIR (deterministic ODE):** with `s + i + r = 1` and `r(0) = 0`, the infected fraction initially grows iff `R₀s₀ > 1`, and the final-size equation `s_∞ = s₀·exp(−R₀(1 − s_∞))` holds (from `ds/dr = −R₀s`). Outside the finite-probability layer; its own package using Mathlib's ODE/analysis. | Kermack–McKendrick 1927 | – | M–L | open |

## MAJ: majority-type dynamics

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| MAJ-1 | **2-Choices (= binary Median) from a vanishing bias:** from a gap `s ≥ c√(n log n)` between the two opinions, consensus on the majority in `O(log n)` rounds w.h.p. (the classical regime; with `s = O(√n)` the majority can lose with constant probability). Its expected one-round map is the same cubic as 3-majority's, `x(1−(1−x)²) + (1−x)x² = 3x² − 2x³`, so the growth/saturation phases of `plurality/` are the template; per-agent adoptions are independent but not identically distributed. | Doerr, Goldberg, Minder, Sauerwald, Scheideler, SPAA 2011; Survey Cor 12 | – | M | in review |
| MAJ-2 | **From constant to vanishing bias.** `ThreeMajority.majority3_consensus_whp` currently assumes `(3/5)·n ≤ \|I₀\|`, a *constant* advantage of `n/10` over one half. Improve it in two separately claimable steps. **MAJ-2a (any constant advantage):** opinion-1 fraction `≥ 1/2 + ε` for every fixed `ε > 0`, consensus in `O(log(1/ε) + log n)` rounds w.h.p. In expectation the existing growth step already works: `p(1/2 + d) − 1/2 = d(3/2 − 2d²)`, so the bias still grows by a factor `≥ 5/4` for all `d ≤ √2/4`. What must change are the concentration constants in `Growth.lean`, which currently force `d ≳ 0.02`. **MAJ-2b (vanishing advantage):** bias `s ≥ c√(n log n)`, i.e. fraction `1/2 + Θ(√(log n / n)) → 1/2`, consensus in `O(log n)` rounds w.h.p. Now the expected gain per round (`≈ s/2`) is of the same order as the Chernoff deviation, so `c` must dominate it. This is essentially optimal: with `s = O(√n)` the bias shrinks in one round with constant probability. Both steps then transfer to 2-Choices once MAJ-1 exists. | BCN+17a (Survey Thm 18 with `k = 2`, tightness in §5.2); Survey §4 Cases 1–2 and Cor 12 for 2-Choices | – (3-majority); MAJ-1 (2-Choices) | S–M (2a) / M–L (2b) | done via `plurality/`: `Plurality.majority3_vanishing_bias` gives MAJ-2b (gap `22√(3 n log n)`, `O(log n)` rounds, for `log n ≥ 40`), and hence MAJ-2a for large `n` |
| MAJ-3 | **F-bounded adaptive adversary** that recolours `≤ F = o(s)` nodes per round as a function of the history. Modelling the adversary inside `expList` is the interesting part. | Survey Thm 10, Cor 12 | MAJ-2 | M | open |
| MAJ-4 | **k-party 2-Choices.** For `k = O(n^ε)` and initial gap `c₁ − c₂ = Ω(√(n log n))`, 2-Choices converges to the plurality in `O(k log n)` rounds w.h.p. (tight for some configurations; a gap of `O(√n)` can lose with constant probability). The crux is aggregating the minority colours instead of applying Chernoff colour by colour. | **Elsässer, Friedetzky, Kaaser, Mallmann-Trenn, Trinker**, *Efficient k-party voting with two choices*, [arXiv:1602.04667](https://arxiv.org/abs/1602.04667) (PODC 2017 BA); Survey Thm 13 | MAJ-2 | L | open |
| MAJ-5 | **2-Choices on expanders.** (a) *Warm-up (paper's Thm 4):* on a `d`-regular graph with `λ_G = max{λ₂, \|λ_n\|} = 3/5 − ε`, a minority of size `≤ (ε/5)n` disappears and the majority wins in `O(log n)` steps. (b) *Main (paper's Thm 2):* on any `d`-regular graph, an initial imbalance `\|A − B\| ≥ K·λ_G·n` (absolute constant `K`, no degree condition) gives the same conclusion. Both hold w.p. `1 − o(1)`. Key tool: the expander mixing lemma with `λ_G` (Survey Lemma 16; check Mathlib first). | **Cooper, Elsässer, Radzik**, *The power of two choices in distributed voting*, ICALP 2014, [arXiv:1404.7479](https://arxiv.org/abs/1404.7479); Survey Thm 17 | MAJ-1, FND-7, AVG-1 | M (a) / L (b) | open |
| MAJ-6 | **3-Majority vs 2-Choices separation.** From any configuration (any `k ≤ n`), 3-Majority reaches consensus in `O(n^{3/4} log^{7/8} n)` rounds w.h.p., while 2-Choices can need `Ω(n/log n)` (`k = Ω(n/log n)`, `c₁ = O(log n)`). Suggested split: (a) the 2-Choices lower bound (most nodes see two different colours and keep their own); (b) the paper's comparison framework, which dominates 3-Majority's colour reduction by the voter model's (reuses VOT-3). | **Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn, Natale**, *Ignore or Comply? On breaking symmetry in consensus*, PODC 2017, [arXiv:1702.04921](https://arxiv.org/abs/1702.04921); Survey Thms 20–21 | VOT-3 | L (a) / XL (b) | open |
| MAJ-7 | **3-Majority with `k` colours:** `c₁ ≥ n/λ` and bias `≥ 22√(λ n log n)` ⇒ plurality in `O(λ log n)` w.h.p., for every `λ ≥ 3` (constant `λ` gives `O(log n)`). Formalized as `Plurality.theorem_3_8`; the paper's proof needed two repairs, see `plurality/FORMALIZATION_DIFFERENCES.md`. Corollaries 3.10–3.12 too, including the headline `O(min{k, (n/log n)^{1/3}} log n)`. | **Becchetti, Clementi, Natale, Pasquale, Silvestri, Trevisan**, *Simple dynamics for plurality consensus*, SPAA 2014, [arXiv:1310.2858](https://arxiv.org/abs/1310.2858); Survey Thm 18 | FND-1 | – | done (`plurality/`) |
| MAJ-8 | **Drift hitting-time lemma, then symmetry breaking:** binary 3-Majority/2-Choices from *any* configuration in `O(log n)`. The lemma (DGM+11 Claim 2.9) is reusable across MAJ, UND and MOR-3. | Survey §4 Case 3 | MAJ-2 | L–XL | open |
| MAJ-9 | **Classification:** majority is the only 3-input dynamics that preserves the plurality from bias `o(n)` (paper's Thm 4.8). Formalized in `plurality/`: (b) a clear-majority solver is uniform (`Plurality.theorem_4_8_b`); (a) a solver follows the clear majority on every pair, **except** rules with `Δ_r, Δ_b ≤ 1` (`Plurality.theorem_4_8_a`). The paper's supermartingale argument does not cover that case: the process is pulled to an interior point, and which color wins depends on how it escapes. Remaining: that case (metastability; the absorption probability from the interior point). | **Becchetti, Clementi, Natale, Pasquale, Silvestri, Trevisan**, *Simple dynamics for plurality consensus*, SPAA 2014, [arXiv:1310.2858](https://arxiv.org/abs/1310.2858); Survey §5.4; BCN+17a | FND-4 | L | open |
| MAJ-10 | **Lower bounds for plurality dynamics:** from a balanced start, 3-majority needs `Ω(k log n)` rounds (Thm 4.2, `Plurality.theorem_4_2_log`) and `h`-plurality needs `Ω(k/h²)` (Thm 4.12, `Plurality.theorem_4_12_log`). The `Ω(k log n)` reading holds for `k ≤ n^{1/4-δ}`; the paper's range `k ≤ (n/log n)^{1/4}` is too wide for its proof, see `plurality/FORMALIZATION_DIFFERENCES.md`. | **Becchetti, Clementi, Natale, Pasquale, Silvestri, Trevisan**, *Simple dynamics for plurality consensus*, SPAA 2014, [arXiv:1310.2858](https://arxiv.org/abs/1310.2858) | MAJ-7 | M | done (`plurality/`) |
| MAJ-11 | **Realistic constants.** The formal majority theorems hold only for astronomically large populations: `log n ≥ 40` (`n ≥ 2.4·10¹⁷`) for `Plurality.theorem_3_8` and `majority3_vanishing_bias`, `log n ≥ 30` (`n ≥ 10¹³`) for `ThreeMajority.majority3_consensus_whp`. The thresholds come from the constants of the published proofs, which are stated only for sufficiently large `n`, so the same is true of the literature. Improve the constants (sharper concentration, tighter phase bookkeeping) until the theorems apply to realistic `n` (say `n ≥ 10⁴`), keeping the bias `O(√(λ n log n))` and `O(λ log n)` rounds. A first step is to make every threshold a named parameter and track how it propagates. | `PROVENANCE.md` (explicit constants); BCN+14 | MAJ-7, MAJ-2 | M–L | open |

## UND: undecided-state dynamics

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| UND-0 | **Basics (synchronous, binary, `K_n`):** exact one-round expectations `𝔼[a'] = a(n − b + q)/n`, `𝔼[q'] = (q² + 2ab)/n`, hence the bias grows by the factor `1 + q/n`; almost-sure absorption in a monochromatic configuration. | Survey §6; Clementi et al. 2018 | FND-2 | S | in review |
| UND-1 | **Synchronous, binary, majority phase:** from bias `Ω(√(n log n))` (start with a constant fraction), convergence to the plurality in `O(log n)` w.h.p. The non-monotone undecided count is the new difficulty. | Survey Thm 28; Clementi et al. 2018 | FND-3 | M–L | open |
| UND-2 | **Sequential (population protocol) version:** `O(n log n)` interactions, plurality-preserving above `ω(√(n log n))`, via the Angluin–Aspnes–Eisenstat potential function. The canonical CRN result: Cardelli–Csikász-Nagy (2012) show that the cell-cycle switch computes this approximate majority. | Survey Thm 23; AAE08 | FND-2 | L–XL | open |
| UND-3 | **Many colours:** convergence in `O(md(c) log n)`, where `md` is the monochromatic distance. | Becchetti, Clementi, Natale, Pasquale, Silvestri, *Plurality consensus in the gossip model*, SODA 2015, [arXiv:1407.2565](https://arxiv.org/abs/1407.2565); Survey Thm 29 | UND-1 | XL | open |

## CRN: chemical reaction networks

Well-mixed stochastic CRNs under mass-action kinetics are continuous-time Markov chains on
species counts, and their natural (biological or epidemiological) instances are dynamics in the
survey's sense (Definition 1), in the random sequential model. Designed CRNs that rely on a
leader or on phases (e.g. the Turing-universal constructions of Soloveichik–Cook–Winfree–Bruck)
are not dynamics, but their computability results still suit Lean well.

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| CRN-1 | **CRNs ⇔ population protocols.** For a CRN whose reactions are all count-conserving and bimolecular (`A + B → C + D`) with a common rate constant, the jump chain of stochastic mass-action kinetics equals the chain of the population protocol that picks a uniformly random pair of distinct agents, conditioned on the pair reacting. Key identity: the pair has species `{A, B}` with probability `#A·#B / C(n,2)` (`C(#A,2) / C(n,2)` if `A = B`), which is the mass-action propensity up to a common factor. Unequal rate constants give a weighted scheduler. Makes the voter, Moran, SI and approximate-majority rows of the dictionary instances of one model. | Anderson–Kurtz 2011 (CRNs as CTMCs); elementary | FND-1, FND-2 | S–M | open |
| CRN-2 | **Kurtz's law of large numbers for SIR.** For `S + I → 2I` (rate `β/N`) and `I → R` (rate `γ`), the scaled counts `(S, I, R)/N` converge, uniformly on `[0, T]` and in probability, to the Kermack–McKendrick ODE (EPI-7) as `N → ∞`. Bridges the deterministic epidemiology target and the stochastic tracks; the same argument gives the classical Daley–Kendall limit (a fraction ≈ 0.203 never hears the rumour). Needs a finite-horizon martingale concentration bound plus Gronwall, beyond today's layer. | Kurtz, J. Appl. Probab. 1970 and J. Chem. Phys. 1972; Daley–Kendall 1965 | EPI-7, FND-3 | L | open |
| CRN-3 | **Stably computable predicates.** *Easy direction:* threshold predicates (`∑ aᵢxᵢ ≥ c`) and remainder predicates (`∑ aᵢxᵢ ≡ c mod m`) are stably computable by population protocols, hence by count-conserving CRNs, and closure under Boolean combinations gives every semilinear (Presburger) predicate. Stable computation quantifies over fair executions, so this is purely combinatorial (no probability). *Converse* (nothing else is stably computable): research-level. | Angluin–Aspnes–Diamadi–Fischer–Peralta 2006 (constructions); Angluin–Aspnes–Eisenstat–Ruppert 2007 (converse); Chen–Doty–Soloveichik 2014 (functions) | CRN-1 | M (easy) / XL (converse) | open |

## AVG: averaging dynamics and community detection

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| AVG-1 | **Basics:** `Pᵗx → (∑ π(v)x(v))·𝟙` on connected non-bipartite graphs; the rate bound of Survey Thm 33; the expected-matrix identities (4)–(5) for the random sequential version. For regular graphs the symmetric spectral theorem suffices. | Survey §7.2 | Mathlib linear algebra | M | in review (convergence on connected non-bipartite graphs and the bipartite counterexample; rate bound and sequential version open) |
| AVG-2 | **Strong reconstruction by averaging** on a connected `(2n,d,b)`-clustered regular graph with `1 − 2b/d > (1+δ)λ`: the sign of `x^{(t−1)}(u) − x^{(t)}(u)` recovers the two clusters for all `t ≥ C log n`. **Hint:** the argument is deterministic once `⟨x, χ⟩ ≠ 0`. That is a sum of `2n` Rademacher signs, so it is even, and when nonzero `\|α₂\| ≥ 2/√(2n)`; the eigen-decomposition then gives an explicit `t`. The only probability needed is `P(⟨x,χ⟩ = 0) = C(2n,n)/4ⁿ ≤ 1/√(πn)`, an exact count on a uniform finite type (so "w.h.p." here means `1 − O(n^{−1/2})`). | Survey Thm 36; BCN+17b | AVG-1 | M–L | open |

---

## Suggested order

1. ~~Land PR #3~~ **Done** (FND-1, FND-2, VOT-1). Most tracks build on `dynamics/`.
2. **Quick wins on top of it:** VOT-2, FND-4, VOT-4, then MOR-1 and MOR-2 (the isothermal theorem, the headline of the population-genetics track). Independently, **MAJ-2a** strengthens the existing 3-majority theorem and can start any time, and **CRN-1** and the easy direction of **CRN-3** (no probability at all) are good entry points.
3. **FND-3 (weighted Chernoff)** unlocks EPI-2, EPI-3 and UND-1. EPI-1 needs nothing new and can start in parallel.
4. **VOT-3 (duality)**, which MAJ-6(b) and EPI-4 reuse.
5. **MAJ-2b** (vanishing bias for 3-majority) and **MAJ-1** (refactor into a generic binary theorem), then MAJ-4.
6. **AVG-1 → AVG-2**, the first project built mainly on Mathlib linear algebra.

## Out of scope for now

Population-protocol memory lower bounds (Survey §6.2, arbitrary schedulers); Interval-Consensus
convergence times (Survey Thms 26–27); Oja-style distributed eigenvector computation (MTMM18).

## How the entries were checked

Checked against the original paper's theorem statements: VOT-1 (via PR #3), VOT-5, MOR-2,
EPI-1, EPI-2, EPI-4, EPI-6, MAJ-5. Checked against the survey's statement and/or the paper's
abstract only: VOT-6, MOR-3, EPI-3, MAJ-2–MAJ-4, MAJ-6–MAJ-9, UND-1–UND-3, AVG-1, CRN-2, CRN-3. Entries
marked "classical" rest on textbook results. Formulas derived for this roadmap were checked
independently: the Moran formula (MOR-1), the isothermal property on a regular graph (MOR-2)
and both push/pull fixation formulas (VOT-4) against exact absorbing-chain solutions over all
mutant sets on small graphs; the 2-Choices cubic (MAJ-1) and the bias-growth identity (MAJ-2a) symbolically; the pair-sampling identity behind CRN-1 by hand; the Daley–Kendall rates against their restatement by Lebensztayn–Rodriguez (2025); and the explicit
recovery time in the AVG-2 hint by simulation on random clustered expanders. Claimers
should still read the source before formalizing.

## Notes on the sources

Statements must use the corrected forms of these typos and citation slips:

- **Survey Thm 33:** `√(d(v)/d(v)) λᵗ` should read `√(d(v)/d(u)) λᵗ` (Lovász, *Random walks on graphs: a survey*, Thm 5.1). Lovász's text itself defines `λ = min{|λ₂|, |λ_n|}`, a slip for `max`; the survey correctly uses `max`.
- **Survey Thm 17** adds a condition `d ≤ √n` that is not in the cited result: Cooper–Elsässer–Radzik's Thm 2 holds for every `d`-regular graph (the `√n` belongs to their Corollary 1, on random regular graphs). The survey's `λ₂` means the second largest eigenvalue *in absolute value*, i.e. `max{λ₂, |λ_n|}`.
- **Survey §6.4 and Thm 29** cite [BCN+16] (*Stabilizing consensus with many opinions*, a 3-majority paper) for the monochromatic-distance result on the Undecided-State dynamics; it is in [BCN+15] (*Plurality consensus in the gossip model*, SODA 2015).
- **Survey Def 3** describes the sequential voter, while Hassin–Peleg's Thm 4 is synchronous. Both satisfy the degree-weighted invariant.
- **Survey §7.2–7.3:** "the random sequential model described in Definition 30" should be Definition 31; "Algorithm 30/31" should be "Definition 30/31".
- **[BCDPTZ22] v3, Thm 2.5 claim 2** repeats the `SWG(n,c/n)` threshold, but `3-SWG(n)` has no parameter `c`; by Thm 2.2 it should be `p < 1/2 − ε`. §3.2 cites "Claim 3 of Theorem 2.2", which has two claims.

## References

- **[BCN20]** L. Becchetti, A. Clementi, E. Natale. *Consensus Dynamics: An Overview.* ACM SIGACT News 51(1):58–104, 2020. [doi:10.1145/3388392.3388403](https://doi.org/10.1145/3388392.3388403), open copy [hal-02507613](https://hal.science/hal-02507613). "Survey Thm N" refers to this paper.
- **[BCDPTZ22]** L. Becchetti, A. Clementi, R. Denni, F. Pasquale, L. Trevisan, I. Ziccardi. *Percolation and Epidemic Processes in One-Dimensional Small-World Networks.* [arXiv:2103.16398](https://arxiv.org/abs/2103.16398).
- Y. Hassin, D. Peleg. *Distributed probabilistic polling and applications to proportionate agreement.* Inf. Comput. 171, 2001.
- P. A. P. Moran. *Random processes in genetics.* Proc. Camb. Phil. Soc. 54, 1958.
- E. Lieberman, C. Hauert, M. A. Nowak. *Evolutionary dynamics on graphs.* Nature 433, 2005.
- **[DGMRSS14]** J. Díaz, L. A. Goldberg, G. Mertzios, D. Richerby, M. Serna, P. Spirakis. *Approximating fixation probabilities in the generalized Moran process.* Algorithmica 69(1):78–91, 2014. Also *On the fixation probability of superstars*, Proc. R. Soc. A 469:20130193, 2013.
- **[GGGLR17]** A. Galanis, A. Göbel, L. A. Goldberg, J. Lapinskas, D. Richerby. *Amplifiers for the Moran process.* J. ACM 64(1), 2017. [arXiv:1512.05632](https://arxiv.org/abs/1512.05632).
- T. Antal, S. Redner, V. Sood. *Evolutionary dynamics on degree-heterogeneous graphs.* Phys. Rev. Lett. 96:188104, 2006.
- **[Gia16]** G. Giakkoupis. *Amplifiers and suppressors of selection for the Moran process on undirected graphs.* [arXiv:1611.01585](https://arxiv.org/abs/1611.01585).
- **[GLLMPP18]** L. A. Goldberg, J. Lapinskas, J. Lengler, F. Meier, K. Panagiotou, P. Pfister. *Asymptotically optimal amplifiers for the Moran process.* Theor. Comput. Sci. 758:73–93, 2019.
- P. Keller, M. Uğurlu. *Fixation probability in Moran-like processes on graphs.* [arXiv:2403.12598](https://arxiv.org/abs/2403.12598).
- L. Hindersin, A. Traulsen. *Most undirected random graphs are amplifiers of selection for Birth-death dynamics, but suppressors of selection for death-Birth dynamics.* PLoS Comput. Biol., 2015.
- M. Krivelevich, B. Sudakov. *The phase transition in random graphs: a simple proof.* Random Struct. Algorithms 43(2):131–138, 2013.
- L. Lovász. *Random walks on graphs: a survey.* Combinatorics, Paul Erdős is Eighty, Vol. 2, 1993.
- CRNs: T. G. Kurtz, *Solutions of ordinary differential equations as limits of pure jump Markov processes*, J. Appl. Probab. 7, 1970, and *The relationship between stochastic and deterministic models for chemical reactions*, J. Chem. Phys. 57, 1972; D. F. Anderson, T. G. Kurtz, *Continuous time Markov chain models for chemical reaction networks*, in Design and Analysis of Biomolecular Circuits, Springer, 2011; L. Cardelli, A. Csikász-Nagy, *The cell cycle switch computes approximate majority*, Sci. Rep. 2, 2012; D. Soloveichik, M. Cook, E. Winfree, J. Bruck, *Computation with finite stochastic chemical reaction networks*, Nat. Comput. 7, 2008; D. Doty, *Timing in chemical reaction networks*, SODA 2014; H.-L. Chen, D. Doty, D. Soloveichik, *Deterministic function computation with chemical reaction networks*, Nat. Comput. 13, 2014.
- Population protocols: D. Angluin, J. Aspnes, Z. Diamadi, M. J. Fischer, R. Peralta, *Computation in networks of passively mobile finite-state sensors*, Distrib. Comput. 18, 2006; D. Angluin, J. Aspnes, D. Eisenstat, E. Ruppert, *The computational power of population protocols*, Distrib. Comput. 20, 2007.
- D. J. Daley, D. G. Kendall. *Stochastic rumours.* IMA J. Appl. Math. 1, 1965; rates as restated in E. Lebensztayn, P. M. Rodriguez, [arXiv:2507.07914](https://arxiv.org/abs/2507.07914).
- D. Kempe, J. Kleinberg, É. Tardos. *Maximizing the spread of influence through a social network.* Theory of Computing 11, 2015.
- Author picks (full entries in the tables): Berenbrink et al. [arXiv:1702.04921](https://arxiv.org/abs/1702.04921) and [arXiv:1603.01895](https://arxiv.org/abs/1603.01895); Cooper, Elsässer, Radzik [arXiv:1404.7479](https://arxiv.org/abs/1404.7479); Cooper, Radzik, Rivera [arXiv:1602.05768](https://arxiv.org/abs/1602.05768); Elsässer et al. [arXiv:1602.04667](https://arxiv.org/abs/1602.04667).
