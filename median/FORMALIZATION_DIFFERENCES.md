# Formalization differences

Where the statements and proofs of `median/` deviate from Doerr, Goldberg, Minder, Sauerwald and
Scheideler, *Stabilizing consensus with the power of two choices* (SPAA 2011), and why.

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
