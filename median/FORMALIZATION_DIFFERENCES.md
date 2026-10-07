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
