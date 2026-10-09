# Formalization differences

Where the statements and proofs of `median/` deviate from Doerr, Goldberg, Minder, Sauerwald and
Scheideler, *Stabilizing consensus with the power of two choices* (SPAA 2011), and why. The
sections on expanders, on plurality consensus with `k` colours and on the lower bound for
2-Choices name their own sources.

Theorem and lemma numbers of Doerr et al. follow the 2009 version of the paper (Dagstuhl Seminar Proceedings 09371); in the
SPAA 2011 proceedings, Theorem 1 is Theorem 1.1 and Theorem 21 is Theorem 4.1, and the lemmas
are numbered differently.

## Consensus from any configuration (`AnyStart`)

1. **Only the adversary-free part of Theorem 1.** The paper's main theorem gives almost stable
   consensus in `O(log m log log n + log n)` rounds against an adversary corrupting up to `√n`
   nodes, and stable consensus in `O(log n)` rounds without an adversary. Only the latter is
   formalized (`median_consensus_any`); the adversary is roadmap MAJ-3.
2. **Explicit constants and a lower bound on `n`.** "With high probability" is the explicit
   failure bound `C/n` after `⌈C log n⌉` rounds, under `C ≤ log n`; the proofs use
   `C = 2¹⁸` for `binary_any_start` and `3·2¹⁸ + 3` for `median_consensus_any`. As for
   `consensus_whp` (`log n ≥ 128`), the theorems therefore apply only to astronomically large
   populations (roadmap MAJ-11). Consensus is the event `notConsensus (run x l) = 0` along the
   list `l` of independent uniform rounds, and its failure probability is the expectation
   `expList (Round n) T (fun l => notConsensus (run x l))`.
3. **The proof goes through two values.** Instead of following the paper's multi-valued
   argument, every configuration is reduced to its threshold configurations
   `fun v => decide (b ≤ x v)`, which follow the same rounds (the paper's Lemma 17, our
   `threshold_run`): a run that has not reached consensus has two values `a < b`, and the
   threshold at `b` has not reached consensus either. A union bound over the at most `n - 1`
   thresholds (`consensus_of_binary`) then needs a binary failure bound of `o(1/n)`; it is
   obtained by running three blocks of `⌈C₀ log n⌉` rounds, which turns `C₀/n` into `(C₀/n)³`
   because consensus is absorbing (`expList_amplify`).
4. **Symmetry breaking by a potential.** For 2-Choices from an arbitrary (possibly perfectly
   balanced) binary configuration, the paper's Lemmas 13 to 16 are replaced by a drift argument
   on `gapPot y = exp (-|g| / (256 √n))`, where `g` is the number of `true` nodes minus the
   number of `false` nodes. One round contracts it in expectation by `e^{-1/65536}` up to an
   additive `e^{1/131072 - √n/512}` (`avg_gapPot_step`): away from balance by Hoeffding's lemma
   applied at every node (`avg_exp_neg_gapR_step`), near balance (`|g| ≤ √n/64`) because the
   next gap has variance at least `n/10` (`one_tenth_le_variance_coord`), so by Paley-Zygmund
   `|g'| ≥ √n/4` with probability at least `9/64`. After `⌈2¹⁷ log n⌉` rounds, Markov's
   inequality gives `|g| ≥ 128 √(n log n)` except with probability `2/n` (`escape_bound`), and
   `binary_consensus`, applied to the configuration or to its flip, finishes within
   `⌈128 log n⌉` rounds except with probability `128/n` (`finish_bound`).
5. **Generic lemmas not yet in `dynamics/`.** Several lemmas proved in namespace `Median` only
   use notions of the shared layer (`avg`, `expList`, `variance`, `Kernel`) or plain real
   inequalities: the fixed-time drift lemmas `iterate_le_of_drift`, `iterate_add_le`,
   `expList_le_of_drift`, `expList_add_le`; the moment bounds `avg_exp_sum_le` (Hoeffding's
   mgf bound for any real `t`), `avg_sum_sq`, `avg_sum_fourth_le`, `avg_pz`, `avg_pz_sum`,
   `avg_pz_zero_one`, `variance_of_zero_one`; and `ceil_add_ceil_le`, `mul_ceil_le_ceil`,
   `pow_three_le_of_log`, `log_pow_four_div_le`. They are candidates for the shared core.

## Many values: the middle one wins fast (`ManyValues`)

1. **The deterministic core of the odd case of Theorem 21.** The paper starts from a uniformly
   random configuration with `m` values and shows consensus in `O(log m + log log n)` rounds
   when `m` is odd (and `Θ(log n)` rounds when `m` is even). The formal statement
   `odd_split_consensus` assumes instead that the `2k + 1` values have exactly equal support
   `n/(2k+1)` and that `C (2k+1) √(n log n) ≤ n`; the random start (whose supports only
   fluctuate around `n/m`) and the even case are not formalized. The underlying statement
   `median_consensus_fast` only needs a margin `Δ ≥ C √(n log n)` on both sides of a value `v`
   (at least `Δ` more nodes at or above `v` than below it, and symmetrically), so it also covers
   unequal supports.
2. **Explicit constants and a lower bound on `n`.** "With high probability" is the explicit
   success bound `1 - C/n` (`1 - 2C/n` for `median_consensus_fast`), under `C ≤ log n`; the
   proofs use `C = 128` for `binary_consensus_fast` and `median_consensus_fast`, and `256` for
   `odd_split_consensus`. Consensus on `v` is the event `run x l = fun _ => v`.
3. **Proof route.** `binary_consensus_fast` chains one-round moves, each failing with
   probability at most `n⁻²`, through four segments: the gap grows by a factor `5/4` per round
   until the minority is below `n/4` (`O(log (n/Δ))` rounds); six rounds bring it to `n/8`; it
   then shrinks quadratically (`m ↦ ≈ 3m²/n`, Bernstein) down to `512 log n`
   (`O(log log n)` rounds); eight more rounds give consensus. For many values, the thresholds
   `u ↦ [v ≤ x u]` and `u ↦ [x u ≤ v]` both run as 2-Choices with the same samples (the second
   because the median is self-dual, `med3_antitone`), their gaps are the two margins, and
   consensus of both on `true` forces consensus on `v`; a union bound gives `1 - 2C/n`.
4. **Generic lemmas not yet in `dynamics/`.** The kernel and round lemmas
   `kernel_event_mono_set`, `kernel_event_chain`, `kernel_event_comp`, `expList_ge_of_and` and
   `expList_foldl_mono` (`ManyValuesKernel.lean`) do not mention the median rule, and the scalar
   facts `exists_lt_pow_mul`, `exists_le_two_pow_two_pow`, `le_pow_ceil_real`,
   `mul_one_div_sq_le`, `nat_ceil_mul_le_of_le`, `log_two_ge`, `log_two_le_one`
   (`ManyValuesScalar.lean`) are plain real inequalities. They live in namespace `Median` until
   the shared core provides them.

## Two-sample voting on expanders (`Expander`)

Source: Cooper, Elsässer and Radzik, *The power of two choices in distributed voting*
(ICALP 2014, arXiv:1404.7479), Theorem 4, with its Lemma 3 (expander mixing lemma) and Lemma 5.
Lemma numbers follow the arXiv version.

1. **Model.** The graph is a simple `d`-regular graph on a finite vertex type with `d > 0` (no
   loops or multiple edges). Every vertex samples two neighbours independently and uniformly
   with replacement, the case the paper analyses; sampling without replacement is not covered.
   A round is a pair of the core's `NeighborRound G` (`GraphRound G`), and the update is the
   median of the own opinion and the two samples, which for two opinions is the 2-Choices rule
   (`graphStep_bool`). Opinions are Booleans and the majority opinion is any `a : Bool`; the
   minority `B` is the set of vertices whose opinion differs from `a`.
2. **The spectral quantity.** `lambdaG G d = max {λ₂, |λₙ|}`, where `λ₁ ≥ ⋯ ≥ λₙ` are Mathlib's
   sorted eigenvalues (`Matrix.IsHermitian.eigenvalues₀`) of the transition matrix
   `(1/d) A`; it is set to `0` on graphs with fewer than two vertices, which cannot be
   `d`-regular with `d > 0`. The expander mixing lemma is stated with this quantity, which equals
   the paper's `max {|λ₂|, |λₙ|}`. `E(S, T)` (`edgeCount`) counts ordered pairs `(u, v) ∈ S × T`
   of adjacent vertices, so `E(S, S) = 2 |E(S)|`; "`S` spans at most `α d |S|` edges" is written
   `E(S, S) ≤ 2 α d |S|`. The mixing lemma holds for every `d`-regular graph, including `d = 0`
   and graphs with `λ_G ≥ 1`, where it is trivial.
3. **Hypothesis of Theorem 4.** The paper assumes `λ_G = 3/5 − ε`; the formal statements assume
   `λ_G ≤ 3/5 − ε` with `ε > 0`, which is more general. The bound on the minority, at most
   `(ε/5) n`, is the paper's.
4. **"With high probability" made explicit.** `two_choices_expander_explicit` bounds the failure
   probability after `T` rounds by `(24/25)^T |B| + T e^{−εn/24250}`, where failure means that
   not every vertex holds `a` after `T` rounds (consensus is absorbing, so the vote is then
   completed). `two_choices_expander` takes `T = ⌈C log n⌉` with an absolute constant `C`
   (`C = 25000` in the proof) and bounds the failure probability by
   `1/n + (C log n + 1) e^{−εn/C}`; `two_choices_failure_tendsto` shows that this tends to `0`
   for fixed `ε > 0` (as in the paper, the bound is only small when `εn` is large compared with
   `log n`).
5. **Lemma 5 at `α = 3/10` only, with explicit constants.** `phaseII_step` and
   `expected_minority_step` are the paper's Lemma 5 for the value `α = 3/10` used in the proof of
   Theorem 4, so `γ = (1 − 2α)(1 − 3α)/2 = 1/50`; the unspecified constant `γ̃` is `1/4850`. The
   hypothesis `A > B` of the paper is not needed. The expected decrease is bounded as in the
   paper; the concentration step uses one multiplicative Chernoff bound on the new minority
   `|B'| = ∑ᵥ [v holds an opinion ≠ a]` (a sum of independent indicators), with mean bound
   `(24/25) |B|` and `δ = 1/48`, instead of separate bounds on the two flows `Δ_{AB}` and
   `Δ_{BA}`. For this, one round on a `d`-regular graph is identified with `|V|` independent
   uniform draws from `Fin d × Fin d` through an enumeration of each neighbourhood
   (`roundEquiv`).
6. **Proof route of Theorem 4.** The paper combines its Lemma 6 and Corollary 4 (Phase II: the
   minority falls from `(3/13)(3/5 − λ_G) n` to a slowly growing `ω` in `O(log n)` rounds)
   with its Lemma 9 and Corollary 5 (Phase III: from `ω` to `0`), for `ω = log n / log log n`. The
   formalization uses instead one supermartingale argument (`expList_le_of_contract`). In the
   region `|B| ≤ (ε/5) n`, every superset of `B` of size at most `(13/3) |B| ≤ εn` is sparse by
   the mixing lemma (`sparse_of_lambdaG`: `E(S, S) ≤ d |S|² / n + λ_G d |S|`), so the expected
   minority contracts by `24/25` per round, and by the Chernoff bound one round leaves the
   region with probability at most `e^{−εn/24250}`. This gives the explicit bound of item 4
   directly; for fixed `ε` (more generally, when `εn` is large compared with `log n`) the
   failure probability is polynomially small in `n`, while the paper's phases give `e^{−Θ(ω)}`,
   which for `ω = log n / log log n` is `n^{−Θ(1/log log n)}`. The sparsity threshold `εn`
   replaces the paper's `c n` with `c = 1 − (2/5)(1 − λ)^{−1} ≥ ε`, and the mixing lemma
   replaces the conductance bound of Jerrum and Sinclair used in the proof of Lemma 6.
7. **No adversary.** The paper notes that its theorems hold against an adversary that
   redistributes the opinions before every round (keeping their numbers). The formal statements
   cover the process without an adversary. The one-round bounds hold for every configuration in
   the region `|B| ≤ (ε/5) n`, so the argument extends to such an adversary, but this is not
   formalized.
8. **Generic lemmas not yet in the shared core.** `expList_le_of_contract`
   (`ExpanderDrift.lean`) only uses `avg` and `expList`. The spectral lemmas of
   `ExpanderMixing.lean` (Parseval for Mathlib's eigenbasis, the spectral expansion of a
   bilinear form, and the expander mixing lemma itself) are candidates for the spectral toolkit
   of the core.

## Two-sample voting on expanders with a small imbalance (`ExpanderGeneral`, MAJ-5B)

Source: Cooper, Elsässer and Radzik, *The power of two choices in distributed voting*
(ICALP 2014, arXiv:1404.7479), Theorem 2, with Lemma 2 (Phase I), Corollary 2 and Section 7.
Numbering follows the arXiv version. The model and the definitions are those of `Expander`
above (items 1, 2 and 7 there apply unchanged).

1. **Theorem 2 needs a major correction for very small `λ_G`.** The paper claims success with
   high probability ("probability tending to 1 as `n` increases", footnote in Section 2)
   whenever `ν₀ ≥ K λ_G`, for "an `n`-vertex `d`-regular graph" and "an absolute constant `K`
   (independent of `d` and `λ_G`)" (the abstract: "for any regular graph"). Its proof goes
   through Corollary 2, whose success probability is only `1 − e^{−Θ(λ² n)}`: Lemma 2 assumes
   `α² c² n = Ω(n^ε)`, which the proof of Corollary 2 does not check when it takes `α = λ`,
   and Section 7 does not state a probability for Phase I. When `λ_G` is of order `1/√n` or
   smaller this is not `1 − o(1)`, and the printed statement does not hold: on the complete
   graph `λ_G = 1/(n − 1)`, so `A − B = K + 2` (a constant) satisfies `ν₀ ≥ K λ_G`; the first
   round already produces fluctuations of order `√n` in `A − B`, and by the symmetry between
   the two opinions the initial majority then wins with probability tending to `1/2` (with
   `A − B` of order `√n` it still loses with probability bounded away from `0`). Since
   `λ_G² ≥ (n − d)/(d (n − 1))` (the trace of `P²`), this regime only concerns dense graphs
   (`d` of order `n`). The formal theorem applies Phase I with `α = ν₀ / K ≥ λ_G` instead of
   `α = λ_G`, which gives the failure probability `(2 C log n + C) e^{−ν₀² n / C}` (plus
   `1/n`): it tends to `0` once `ν₀² n` is large compared with `log log n` (for example, for
   any fixed `ν₀ > 0`, or whenever `λ_G ≥ n^{−1/2+ε}`, the regime of Lemma 2).
2. **Explicit constants.** `K = 120` in Lemma 2, `K = 4000` and `c = 1/20` in the explicit form
   of Theorem 2. "With high probability" is the explicit failure bound above. The number of
   rounds `phaseIRounds` is the paper's `⌈log_{5/4}(1/(2ν₀))⌉ + ⌈log_{4/3}(1/(4c))⌉`.
3. **Assembly of the phases.** The paper combines Corollary 2 (with `c = 1/10`), Lemma 6 and
   Corollary 5 (Phases II and III, with `λ_G ≤ 1/6`). Here Phases II and III are Theorem 4 as
   formalized in part (a) (`two_choices_expander_explicit`, one supermartingale argument),
   applied with `ε = 1/4`, which needs `λ_G ≤ 7/20` and a minority of at most `n/20`; hence
   Phase I runs down to `c = 1/20`.
4. **Lemma 2 in "hitting" form.** The paper says that the minority "decreases to `c n` within
   `K' (log(1/ν₀) + log(1/c))` steps". `phaseI` states that at some time `t ≤ T₁` the minority
   is at most `c n` (`∃ t ≤ T₁` over prefixes `l.take t` of the rounds). The graph is not
   assumed connected (the paper's Lemma 2 assumes it, but the proof does not use it), and
   the condition `α² c² n = Ω(n^ε)` is replaced by the explicit failure bound.
5. **Concentration with mean bounds.** `gain_tail` and `loss_tail` use Chernoff bounds with a
   lower (respectively upper) bound on the mean (`avg_chernoff_lower`, `avg_chernoff_upper`);
   the paper's lower bound `𝔼 Δ_{AB} ≥ c² n / 4` used for (eq-fger2) is not needed.
6. **Model.** As in part (a): sampling with replacement, no adversary redistributing the
   opinions between rounds, and Boolean opinions with `a` the majority (the hypothesis
   `K λ_G ≤ ν₀` with `λ_G ≥ 0` forces `ν₀ ≥ 0`).
7. **Not formalized.** Theorem 1, Corollary 1 and Theorem 3 (random regular graphs, which need
   the configuration model) and the robustness Corollary 6 (`robustness`).
8. **Proof route of Lemma 2.** The one-round expectations, tails and the recursion
   (ncnwd-Appx) follow the paper. The flows `Δ_{BA}` and `Δ_{AB}` are sums of independent
   indicators over the vertices of `B` and of `A`, through the identification of a round with
   `|V|` independent uniform draws from `Fin d × Fin d` (`roundEquiv`, as in `Expander`). The
   upper bound (eq-upperOnDAB) on `𝔼 Δ_{AB}` is proved with the paper's thresholds
   `(1 + 2^j η) B/n` and the paper's size bound `|{v ∈ A : d_v^B ≥ (1 + 2^j η) dB/n}| ≤ A/4^j`
   (from the mixing hypothesis), summed as a layer cake over these upper sets instead of the
   paper's slices `C_i` (`ExpanderGeneralLoss.lean`). The paper's condition `η(1 + 4q) ≤ 1` is
   replaced by the bound `(1 + 3m) η ≤ 5` that the layer-cake sum needs, where
   `4^m ≤ n²/(ηB²) < 4^{m+1}`. The union bound over the rounds of Phase I ("for all steps
   `t = 1, …, T`") is formalized with a process frozen at the first time the minority is at
   most `c n` and a deterministic envelope `g t` for the imbalance (`(5/4)^t ν₀` up to `1/2`,
   then `1 − (3/4)^{t − t₁}/2`), via `expList_escape` (`ExpanderGeneralHitting.lean`).
9. **Composition at the hitting time.** The composition of Phase I with Theorem 4 at the (random) first
   time the minority is at most `n/20` is proved by induction on the length of Phase I
   (`not_consensus_le`, the strong Markov property for `expList`), and the `O(log n)` form is
   bookkeeping on the explicit bound (`ExpanderGeneralArith.lean`).

## Against an adaptive adversary (`Adversary`)

Theorem and lemma numbers below follow the 2009 version of the paper; the main theorem with
adversary is Theorem 1.1 of the SPAA 2011 proceedings.

1. **The adversary is a function of the rounds played so far, inside `expList`.** The paper's
   `T`-bounded adversary knows the entire history and changes the values of up to `T` nodes in
   every round. Such an adversary is not a Markov kernel on configurations (it depends on the
   history), and putting the history into the state would make it unbounded. Instead the
   randomness stays the list of independent uniform rounds averaged by `expList`, and the
   adversary is a function `A h z` of the list `h` of rounds played so far and of the output `z`
   of the median rule in the current round (`Adversary`, `runAdv`). Since the initial
   configuration is fixed, `h` determines the whole history, so this is the most general
   deterministic adaptive adversary; a randomized adversary (independent of the rounds) is a
   mixture of deterministic ones, so worst-case bounds over deterministic adversaries cover it.
   The theorems are also stated for any *perturbed run* `P` (`IsAdvRun`): a function of the
   rounds played so far that starts at the initial configuration and, after every round, differs
   from the output of the median rule in at most `F` nodes; `runAdv_isAdvRun` shows that runs
   against `F`-bounded adversaries are of this kind.
2. **When the adversary acts.** The adversary acts after the median step of each round, seeing
   that round's samples (as in Section 3 of the paper, where it changes the choices of balls
   after they are drawn; in Section 1.1 it acts at the beginning of each round). A corruption
   before the first round is covered because the initial configuration is arbitrary and, for
   many values, the legal values form a set `S` that only has to contain the values of the
   configuration (item 6). The configuration at time `t` is observed after round `t`'s
   adversary; in the paper's description it is observed before the next corruption, which
   differs in at most `F` nodes.
3. **Budget `F ≤ √n / C` with `C = 2²⁰`.** The paper allows `T ≤ √n` (Theorems 2 and 3) or
   `O(√n)` (Theorem 10). The symmetry breaking reuses the one-round contraction of the
   potential `exp (-|g| / (256 √n))` of the adversary-free proof; it survives recolourings that
   move the gap by at most `√n/512` per round, which is where the budget `√n/1024` comes from. A
   budget of order `√n` with a large constant would need a symmetry-breaking argument over
   several rounds.
4. **Almost stable consensus over a finite window.** The paper asks for a round `r` and a value
   `v` such that at every later round all but `O(T)` nodes agree on `v`. Formally
   (`notAlmostStable`), the window is the times `⌈C log n⌉, …, ⌈C log n⌉ + H` for any `H`, with a
   single value `b` for the whole window, at most `C (F + log n)` other nodes at every time, and
   a failure probability that grows linearly in `H` (each round of the window fails with
   probability at most `n⁻²`). The `log n` term is the Chernoff slack of the stable phase: with
   few corrupted nodes, `O(T)` exceptions for `T` below `log n` are not claimed. The value `b`
   is not required to be a legal value; for `K < n/2` exceptions it is the majority value.
5. **Two values: no restriction on the values written.** In `binary_almost_stable` the
   adversary may write either Boolean. This is not only more general: the reduction of item 6
   needs it, because the threshold of a run against a many-valued adversary is a binary run
   against an adversary that may write either value.
6. **Many values: `O(log n)` rounds via thresholds, at a factor `m - 1` in the failure.** The
   paper's bound with adversary and `m` values is `O(log m log log n + log n)` rounds
   (Theorems 3 and 20, through phases on groups of bins). `median_almost_stable` reaches almost
   stable consensus in `O(log n)` rounds for every `m`, a stronger time bound, through the
   threshold reduction that the paper uses only without adversary (Lemma 17): for every legal
   value `b`, the threshold `u ↦ [b ≤ x u]` of the run is a binary run against an adversary with
   the same budget (thresholding commutes with the median rule and does not increase the
   Hamming distance). If all thresholds above the minimum stay in almost consensus with `K`
   exceptions, the run stays in almost consensus with `2K` exceptions on the largest legal value
   whose threshold is in majority `true` (`notAlmostStable_le_sum`). The union bound over the
   `m - 1` thresholds makes the failure probability `(m - 1)(C log n + H)/n²`. For a constant
   number of values (Theorem 2) this is `O(log n / n²)` when `H = O(log n)`; for `m` of order
   `n` it is `O(log n / n)`, which is weaker than the paper's "with high probability" (`1 - n⁻ᶜ`
   for some `c > 1`). The adversary writes values of a set `S` of `m` legal values containing
   the values of the start (the paper: the initial values).
7. **Explicit constants and a lower bound on `n`.** As for the adversary-free theorems, "with
   high probability" is made explicit, and the theorems assume `C ≤ log n` with `C = 2²⁰`, so
   they apply only to astronomically large populations (roadmap MAJ-11).
8. **Proof route.** Two values (`Median/AdversaryBinary.lean`): escape from balance by the drift
   of the potential under recolourings (`avg_gapPot_perturbed`) and Markov's inequality, in
   `⌈2¹⁹ log n⌉` rounds with failure `2/n²`; then a chain of one-round moves, each failing with
   probability `n⁻²` for every recolouring: the gap grows from `G` to `min (9G/8) (17n/32)`
   (`adv_growth_move`; Hoeffding gives `5G/4` before the recolouring), and the minority shrinks
   from `t` to `max (15t/16) K`, `K = max (16F) (1024 log n)` (`adv_sat_move`; Bernstein gives
   `max (7t/8) (512 log n)` before the recolouring), then stays below `K`. A negative gap is
   handled by the flip symmetry.
9. **Generic lemmas not yet in `dynamics/`.** `Median/AdversaryPerturbed.lean` does not mention
   the median rule: perturbed runs of a round-based process (`Perturbed`), fixed-time drift for
   them (`expList_le_of_drift_perturbed`), chains of moves along a path
   (`expList_path_perturbed`, a perturbed path form of `Dynamics.expList_escape`), and the
   `expList` facts `expList_le_of_length`, `expList_le_of_split`. They are candidates for the
   shared core, where they would give adversarial versions of the drift and phase lemmas of
   other packages.

## Plurality consensus with `k` colours (`TwoChoices*`, roadmap MAJ-4)

Source: Elsässer, Friedetzky, Kaaser, Mallmann-Trenn and Trinker, arXiv:1602.04667 (arXiv v5
numbering: its latest version, v5, February 2017, titled *Rapid asynchronous plurality consensus*):
Theorem 1.2 (the synchronous upper bound), and in Section 2.1 Observation 2.1, Lemma 2.2 (the
distance increases), Lemma 2.3 (the coupling) and the proof of Theorem 1.2. In v1 to v4 (titled
*Efficient k-party voting with two choices*) these are Theorem 1, Observation 3, Lemma 4 and
Lemma 5.

### The model and the statements

`Median/TwoChoicesDefs.lean` (namespace `Median.TwoChoices`): colours are any type `α` with
decidable equality (the probabilistic theorems use `Fin k`); configurations and rounds are those
of the median dynamics (`Median.Config n α = Fin n → α`, `Median.Round n = Fin n → Fin n × Fin n`:
every node samples two nodes independently and uniformly, with replacement, possibly itself).
`rule own a b = if a = b then a else own`, `step`, `run`, `count x i` (the number of nodes of
colour `i`), `twice x r i` (the number of nodes whose two samples both hold `i`) and `kernel`. On
`Bool` the rule is the median (`rule_bool`, `step_bool`, `run_bool`, `count_true`), and the
indicator of a colour dominates, node by node and for the same rounds, the binary median process
started from that indicator (`run_dominates`).

`Median/TwoChoicesExpect.lean`: the one-round expectations of Section 2.1: the expectation of
`c_i'` (`expected_count`, `expected_count_mul`), Observation 2.1 (`expected_count_mono`), the
expected gap `𝔼(c_i' − c_j') = (c_i − c_j)(1 + (c_i + c_j)/n − S/n²)` with `S = ∑_j c_j²`
(`expected_gap`), the aggregation of the minority colours `S ≤ c_i² + (n − c_i) b`
(`sum_sq_le_aggregate`) and its consequence for the largest and second largest colour
(`expected_gap_ge`).

`Median/TwoChoicesPlurality.lean`: `distance_increases` (Lemma 2.2), `count_stochDom` (Lemma
2.3), `growth_round` and `growth_phase` (the growth part of the proof of Theorem 1.2),
`finish_phase`, `plurality_whp` (Theorem 1.2 without the adversary) and `plurality_whp_k`, plus
`two_colours_consensus_whp` (the case `k = 2`, from `Median.consensus_whp`) and `absorbed`
(almost-sure consensus, the "almost agreement" of the last paragraph of the proof).

`plurality_whp`: there are `z, C > 0` such that, for every `n` with `log n ≥ C`, every `k`, every
configuration `x` with colours in `Fin k` and every colour `i` that leads every other colour by
at least `z √(n log n)`, all nodes hold `i` after `⌈C (n/c_i) log n⌉` rounds with probability at
least `1 − C/n`. The proof gives `z = 128` and `C = 384`.

### Differences in the statements

1. **No bound on the number of colours.** Theorem 1.2 assumes `k = O(n^ε)` for a small constant
   `ε`. The proof uses it only in Lemma 2.2, to make the multiplicative Chernoff bounds
   applicable (`δ_i < 1` needs `a, b ≥ n^{1−ε}`). The formal statements `distance_increases`,
   `growth_round`, `growth_phase` and `plurality_whp` have no hypothesis on `k`, so they are
   stronger; item 1 of the differences in the proofs explains why none is needed.
2. **The time bound.** The theorem's bound `O((n/c₁) log n)` is `plurality_whp`; the roadmap's
   `O(k log n)` is the corollary `plurality_whp_k` (`c₁ ≥ n/k`).
3. **No adversary, and no lower bounds.** Theorem 1.2 also covers an `F = c₁(c₁ − c₂)/(8n)`-dynamic
   adversary (stabilizing near-plurality); this is not formalized (roadmap MAJ-3 has an adversary
   for two values). The `Ω(n/c₁ + log n)` part of Theorem 1.2 and Theorems 2.5 (a gap `O(√n)`
   loses with constant probability) and 2.6 are not formalized.
4. **"With high probability" made explicit.** It is `1 − C/n` for the theorems and `1 − C/n²` for
   the one-round lemmas, with `∃ C` and the regime `log n ≥ C`. The proofs give `z = 128` and
   `C = 2` (`distance_increases`, `growth_round`), `C = 128` (`growth_phase`, `finish_phase`) and
   `C = 384` (`plurality_whp`). Lemma 2.2 is stated with the paper's strict inequality and factor
   `1 + a/(4n)`, and with the hypothesis `a ≤ n/2` that its proof assumes.
5. **Lemma 2.3 as a stochastic domination.** The paper states the existence of a coupling of the
   round with a process `P'` in which `c' ≤ b'`. The formal statement `count_stochDom` is the
   stochastic domination `P(c' ≥ t) ≤ P(b' ≥ t)` for every `t`, for any two colours with
   `c ≤ b`, which is what such a coupling gives and how the proof of Theorem 1.2 uses it.

### Differences in the proofs

1. **Bernstein instead of Chernoff, so no bound on `k`.** For one round, `a' − c_j'` and `a'` are
   sums of independent per-node contributions (`Median/TwoChoicesConc.lean`). Their variances are
   bounded node by node: a node of colour `i` or `j` contributes only when it leaves its colour,
   with probability at most `S/n² ≤ a/n`, and any other node contributes with probability at most
   `2a²/n²`, so `Var(a' − c_j') ≤ 10 a²/n` (`gap_dev_le`) and `Var(a') ≤ 2a²/n` (`count_dev_le`).
   Bernstein's inequality (the shared `Dynamics.avg_bernstein`) with the deviation
   `λ = (a − b) a/(8n)` has exponent at least `(a − b)²/(1344 n) ≥ (z²/1344) log n`, so for
   `z = 128` one colour fails with probability at most `n⁻¹²` (`gap_tail_twelve`,
   `count_tail_twelve`). This holds for every `k`; the union bound runs over the at most `n`
   colours present, since an absent colour stays absent (`count_step_eq_zero`).
2. **Lemma 2.3 is not used.** In the growth step, Observation 2.1 gives `𝔼c_j' ≤ 𝔼b'` for every
   colour `j` other than the plurality colour (`b` the second largest), so the expected gap to
   every colour grows at least like the gap to `b`, by `expected_gap_ge`. Together with the
   per-colour tail bounds of item 1 this replaces the coupling. `count_stochDom` is proved
   separately, by a matching of nodes and of sample pairs: a permutation of the nodes sends the
   nodes of colour `c` to nodes of colour `b`, and for each node a permutation of the sample pairs
   embeds the pairs that make it adopt `c` into those that make its image adopt `b`; the induced
   bijection of rounds preserves the uniform distribution.
3. **Growth up to `3n/4`, then two colours.** The paper grows the gap while `a ≤ n/2` (Lemma 2.2),
   then appeals to the two-colour result of Cooper, Elsässer and Radzik once
   `a ≥ (1/2 + ε₁) n`. Formally, `growth_round` works for `a ≤ 3n/4` with the factor
   `1 + a/(8n)`: the drift `(a/n)(1 − a/n) ≥ a/(4n)` minus the deviation `a/(8n)`. It also keeps
   `a` from decreasing (`a' ≥ a`, from the drift `𝔼a' − a ≥ a g/(4n)` of the aggregation bound and
   the tail of `a'`). `growth_phase` chains these rounds with moving targets
   (`Dynamics.expList_escape`): after `⌈128 (n/a₀) log n⌉` rounds the gap would exceed `n`
   (`growth_ratio_pow_gt`) unless the plurality colour already holds `3n/4` of the nodes, where it
   then stays (`stay_three_quarters`). `finish_phase` dominates the colour by the binary median
   process (`run_dominates`), whose gap is at least `n/2`, and applies `Median.binary_consensus`.
4. **Generic lemmas not yet in `dynamics/`.** `variance_le_avg_sub` (the variance is at most the
   second moment about any point) and the scalar facts `gap_exponent_ge`, `count_exponent_ge`,
   `exp_neg_twelve_log` and `one_div_pow_twelve_le` (`Median/TwoChoicesConc.lean`) do not mention
   the dynamics.

### Remarks on the sources

* **The proof of Theorem 1.2 needs a minor correction.** Lemma 2.2 is proved for `a ≤ n/2`, while
  the hand-off to the two-colour process needs `a ≥ (1/2 + ε₁) n`, so the range between is not
  covered. The time bound `O((n/a) log n)` uses the initial `a`, while the growth factor
  `1 + a/(4n)` of Lemma 2.2 uses the current one, and the proof does not show that `a` does not
  decrease. Both are repaired by `growth_round`, which is valid up to `3n/4` and gives `a' ≥ a`
  with high probability.
* **The proof of Lemma 2.3 needs a minor correction.** Read literally (in `P'`, every node samples
  `π(v)` whenever it samples `v` in `P`, and the configuration is unchanged), the coupling does not
  give `c' ≤ b'` round by round, even under the lemma's hypotheses: for `n = 5` and colours
  `(A, A, A, B, C)`, where `π` swaps the node of `C` with the node of `B`, it fails in 2 406 250 of
  the 9 765 625 rounds. The coupling moves the samples but not the nodes, so a node of `C` that
  keeps its colour is not matched with a node of `B̂` that keeps its colour. The statement itself
  holds, as a stochastic domination (`count_stochDom`, item 5 of the differences in the statements
  and item 2 of the differences in the proofs).

## The lower bound for 2-Choices (`TwoChoicesLower`, roadmap MAJ-6 (a))

Source: Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn and Natale, *Ignore or comply? On
breaking symmetry in consensus*, PODC 2017: Theorem 5 of arXiv:1702.04921 (v1) (Section 4, proof
in Appendix A.8) and the 2-Choices half of Theorem 1 (Simplified).

### The statements

`lower_bound_strong` (Theorem 5): there is `γ₀ > 0` such that, for every `γ ≥ γ₀`, every
configuration whose colours have at most `ℓ` nodes each, `ℓ' = max {2ℓ, γ log n}` and every `T`
with `T < n/(γ ℓ')`, the probability that some colour has more than `ℓ'` nodes at some time
`t ≤ T` is at most `1/n`. The proof gives `γ₀ = 8`.

`consensus_time_lower` (Theorem 1 (Simplified), lower bound): for every `β > 0` there is `C > 0`
such that, from every configuration in which every colour has at most `β log n` nodes, the
probability that 2-Choices reaches consensus at some time `t ≤ T` is at most `1/n`, for every `T`
with `(T + 1) C log n < n`. The proof gives `C = max(8, 2β)²`.

### Differences in the statements

1. **Theorem 5.** The paper's `ℓ` is the largest support; the formal `ℓ` is any upper bound on all
   supports. "`γ` a sufficiently large constant" is "every `γ ≥ γ₀`", and the window
   "`t < n/(γ ℓ')`" is "every `t ≤ T` with `T < n/(γ ℓ')`".
2. **Theorem 1 (Simplified).** "Each colour is supported by at most `O(log n)` nodes" is "at most
   `β log n` nodes, for any `β > 0`", and "2-Choices needs `Ω(n/log n)` rounds with high
   probability" is the bound `1/n` on reaching consensus within `T` rounds when
   `(T + 1) C log n < n`. Consensus is `∃ c, run x l = fun _ => c`.

### Differences in the proofs

1. **An exponential supermartingale instead of the binomial domination.** The paper dominates the
   support of a colour by a process `P` with binomial increments and applies a Chernoff bound to
   the sum of the increments. The formal proof needs no coupling: a colour gains only nodes that
   see it twice (`count_step_le`), the number of such nodes is a sum of `n` independent Bernoulli
   variables with exponential moment `(1 + (c_i/n)²(e^θ − 1))ⁿ` (`avg_exp_twice`), and an
   induction on the horizon with `θ = 1` gives
   `P(∃ t ≤ T, c_i(t) > L) ≤ exp(−(L − c_i) + (e − 1) T L²/n)` (`colour_escape_le`). With
   `L = ℓ'`, `L − c_i ≥ ℓ'/2` and `T ℓ'²/n < ℓ'/γ`, one colour fails with probability at most
   `n⁻²` for `γ ≥ 8`, and the union bound runs over the at most `n` colours present.
2. **The expected number of changes.** `expected_see_distinct` and `expected_changed_le` make
   precise the remark of the paper's sketch that most nodes see two different colours and keep
   their own: if every colour has at most `ℓ` nodes, at most `ℓ` nodes change colour in
   expectation. They are not needed by the proof of Theorem 5.

### Remarks on the sources

* **The proof of Theorem 5 needs a minor correction of a constant.** In equation (21), the
  threshold `(1 + δ)μ = max {2μ, (γ/2) log n}` (with `μ = 𝔼B`) has `δ ≥ 1`, and the Chernoff bound
  `exp(−δμ/3)` for `δ ≥ 1` gives, since `δμ = (1 + δ)μ − μ ≥ (γ/4) log n`, only
  `exp(−(γ/12) log n)`, not the `exp(−(γ/6) log n)` written there (which uses `(1 + δ)μ` in place
  of `δμ`). The bound is attained at `δ = 1` (`ℓ' = (γ²/4) log n`), where even the full Chernoff
  bound `(e/4)^μ` gives only about `n^{−0.097γ}`. Taking `γ ≥ 36` instead of `γ ≥ 18` restores
  the `1/n³` of equation (21). The theorem is unaffected, since `γ` is any sufficiently large
  constant.
