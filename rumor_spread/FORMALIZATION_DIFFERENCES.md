# Formalization differences

Where the statements of `rumor_spread/` deviate from their sources, and why.

## PULL and PUSH–PULL on the complete graph (`Pull*`, EPI-5)

Sources: [KSSV00] R. Karp, C. Schindelhauer, S. Shenker, B. Vöcking, *Randomized rumor
spreading*, FOCS 2000 (§1.2 model, §2 push versus pull, Theorem 2.1 for push&pull); [FG85]
A. Frieze, G. Grimmett, *The shortest-path problem for graphs with random arc-lengths*, Discrete
Appl. Math. 10 (1985) (PUSH, partner chosen among the other nodes).

1. **Partner choice excludes self-calls.** [KSSV00, §1.2] lets every player choose its partner
   uniformly among *all* players (its §2 startup analysis mentions a player "calling itself").
   We reuse the PUSH round model `Tgt n` of this package (each node calls a uniform node among
   the *other* `n - 1`, the [FG85] convention), so that PUSH, PULL and PUSH–PULL are driven by
   the same random calls. Only constants change: the exact one-round formulas have `n - 1` where
   the heuristics of [KSSV00] have `n`. For instance the expected number of uninformed nodes
   after a PULL round is `u(u-1)/(n-1)` (`pull_avg_uninformed`, with `u = n - |I|`) instead of
   `s²n = u²/n`; we state the exact form and the bound `≤ u²/n` (`pull_avg_uninformed_le`).
2. **Round count `⌈160 ln n⌉ = O(log n)`, not sharp.** [KSSV00, Thm 2.1] gives
   `log₃ n + O(log log n)` rounds for push&pull. We prove the `O(log n)` statement with an
   explicit, deliberately crude constant, chosen so that the PULL proof reuses the PUSH
   numerics `numeric_A/B/C` of `Main.lean` (`rounds_le_ceil_160`:
   `(⌈117 ln n⌉ + 23) + ⌈6 ln n⌉ ≤ ⌈160 ln n⌉`).
3. **"With high probability" with exponent 1.** In [KSSV00, footnote 1], w.h.p. means
   probability at least `1 - n^{-α}` for an arbitrary constant `α`. We prove failure probability
   at most `2/n`, the same form as `push_informs_all_whp`.
4. **Spreading time only.** [KSSV00, Thm 2.1] also bounds the number of transmissions
   (`O(n log log n)`) and stops push&pull with an age counter; we run exactly `T` rounds (their
   scheme with termination age `T`) and do not count messages. The median-counter algorithm of
   §3, robustness and the lower bounds are not formalized.
5. **PULL.** [KSSV00] discuss PULL only informally in §2 (no numbered theorem): `O(log n)`
   rounds to inform about `n/2` nodes w.h.p., then quadratic shrinking. We prove the classical
   statement "PULL informs all nodes in `O(log n)` rounds w.h.p." (`pull_informs_all_whp`) and
   the quadratic shrinking **in expectation only** (the exact one-round formula and `≤ u²/n`),
   not the w.h.p. Chernoff version used in phase 3 of the proof of Theorem 2.1, since this
   package avoids Chernoff bounds by design.
6. **Proof route for PULL.** The PUSH argument (`Growth.lean`, `Saturation.lean`, `Main.lean`)
   uses only two one-round facts: a round is good (grows the informed set by `9/8`, or starts
   above `n/2`) with probability at least `1/8`, and above `n/2` the expected uninformed count
   contracts by `2/3`. `PullPhases.lean` reruns this argument for any inflationary step
   (`notAllOf_le_two_div`), and `PullGood.lean` proves the two inputs for PULL. Unlike PUSH, a
   PULL round can inform many more than `|I|` new nodes, so the reverse-Markov argument of
   `prob_goodRound` does not apply; we use a second moment instead (`𝔼X² ≤ μ + μ²` for the
   number `X` of uninformed callers calling into `I`, by pairwise independence of the calls)
   and a Paley–Zygmund bound obtained from the pointwise inequality
   `X ≤ μ/4 + X²/(2t) + (t/2)·1[good]` with `t = 4(1 + μ)/3`, so no Cauchy–Schwarz is needed.
   The argument actually gives probability at least `3/16`; `1/8` is what the PUSH constants
   need.
7. **PUSH–PULL by domination.** With the same calls, the PUSH–PULL informed set contains both
   the PUSH and the PULL informed sets pathwise (`run_subset_pushPullRun`,
   `pullRun_subset_pushPullRun`), so `pushPull_informs_all_whp` follows from
   `pull_informs_all_whp` at the same round count.
8. **Not formalized:** the sharp PUSH bound `log₂ n + ln n` ([FG85], B. Pittel, SIAM J. Appl.
   Math. 47 (1987)).
9. **Start and size.** `n ≥ 2` throughout (for `n = 1` there is no round configuration: `Tgt 1`
   is empty); the process starts from a single, arbitrary informed node `v₀`, as in the
   sources.
