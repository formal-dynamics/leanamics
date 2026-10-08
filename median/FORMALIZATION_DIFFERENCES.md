# Formalization differences

Where the statements and proofs of `median/` deviate from Doerr, Goldberg, Minder, Sauerwald and
Scheideler, *Stabilizing consensus with the power of two choices* (SPAA 2011), and why.

Theorem and lemma numbers follow the 2009 version of the paper (Dagstuhl Seminar Proceedings 09371); in the
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
