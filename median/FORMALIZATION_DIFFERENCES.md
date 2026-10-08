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
