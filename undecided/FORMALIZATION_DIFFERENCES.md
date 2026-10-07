# Formalization differences

Where the statements of `undecided/` deviate from their sources, and why.

## Sequential approximate majority (`Sequential*`, roadmap UND-2)

Source: D. Angluin, J. Aspnes, D. Eisenstat, *A simple population protocol for fast robust
approximate majority*, Distributed Computing 21(2):87–102, 2008 [AAE08]. Journal manuscript:
<https://cs.yale.edu/homes/aspnes/papers/approximate-majority-abstract.html>.

### The model and the statements

`Undecided/Sequential.lean` (namespace `Undecided.Sequential`) reuses `Undecided.Op`, `Config`,
`count` and `update` from `Undecided/Basic.lean`:

* `Interaction n`: ordered pairs `(initiator, responder)` of distinct agents (a subtype of
  `Fin n × Fin n`), drawn uniformly and independently by `Dynamics.expList (Interaction n) T`.
* `step s p`: the responder `p.1.2` takes `update (s p.1.2) (s p.1.1)`; the other agents are
  unchanged. This is exactly the transition table of [AAE08, §3] under `x ↦ .a`, `y ↦ .b`,
  blank `↦ .u`.
* `run s l := l.foldl step s` (the form used by `Dynamics.Kernel.iterate_ofStep`).

`Undecided/SequentialMain.lean` states:

* `consensus_whp` [AAE08, Thm 1]: for every `c : ℕ` there is `C` such that for all `n ≥ 2`, every
  non-blank configuration `s` (`∃ v, s v ≠ .u`) and every `T ≥ C n log n`,
  `1 - C / n ^ c ≤ P[count .a = n ∨ count .b = n after T interactions]`.
* `majority_whp` [AAE08, Thm 2 and Thm 1]: for every `c : ℕ` there is `C` such that for all
  `n ≥ 2`, every configuration `s` (blanks allowed) with `C √n log n ≤ count s .a - count s .b`
  and every `T ≥ C n log n`, `1 - C / n ^ c ≤ P[count .a = n after T interactions]`.
* `approximate_majority`: the same with error `1 - C / n` (the case `c = 1`).

The explicit forms behind them (`SequentialConsensus.lean`): for `n ≥ 16`, any `L` and
`T ≥ 256L + 34576nL + 6336n`, `P[not in consensus at T] ≤ 9n e^{-L}` from a non-blank start
(`prob_notCons_le`), and `P[not all x at T] ≤ 9n e^{-L} + exp(-(x₀-y₀)²/(2(60nL + 11n)))` if
`x₀ > y₀` (`prob_notAllX_le`). The main theorems take `L = (c+2) log n` and
`C = 40000(c+2) + 16^c` (`constC`, `SequentialWhp.lean`).

### Differences in the statements

1. **Initial gap `√n · log n`, not `√(n log n)`.** [AAE08, Thm 2 and abstract] assumes an initial
   gap `ω(√n log n)`, and its proof (a coupling with a fair walk and Azuma over `Θ(n log n)`
   steps, whose fluctuation is `√(n log n · log n)`) cannot reach `√(n log n)`. We state the
   paper's hypothesis. The `ω(√(n log n))` in the ROADMAP row UND-2 is the bound of a later
   result: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Maňuch, *Approximate majority analyses
   using tri-molecular chemical reaction networks*, Natural Computing 2020 (their §1.4: "their
   [AAE] majority-consensus analysis assumes an initial gap of `√n lg n`, while ours is
   `√(n lg n)`"). That result is for initial configurations *without blanks* (`x + y = n`) and
   goes by a different route (emulating a tri-molecular chemical reaction network); it is not
   formalized here.
2. **`ω(·)` replaced by `C · (·)`**, with `C` existential (depending on `c`). This implies the
   paper's `ω` form (a gap that is `ω(√n log n)` eventually exceeds `C √n log n`) and is what the
   paper's proof establishes.
3. **"With high probability" means: for every `c : ℕ`, error `≤ C n^{-c}`.** [AAE08, Thm 1] says
   "for any fixed `c > 0`"; a natural `c` loses nothing (`n^{-⌈c⌉} ≤ n^{-c}`). The paper's
   explicit constants (`6769 n log n + 6773 c n log n + 2552 n`, error `5 n^{-c}`) and its
   "sufficiently large `n`" are absorbed into `C` (small `n` are vacuous, since then
   `1 - C / n^c ≤ 0`).
4. **Time bound in the correctness theorem.** [AAE08, Thm 2] concludes eventual convergence to
   the initial majority; `majority_whp` concludes convergence to the majority within `C n log n`
   interactions, that is Thm 2 together with Thm 1 (which is what the proof of Thm 2 shows).
5. **The majority is taken to be `x` (`Op.a`)**, without loss of generality by the `x ↔ y`
   symmetry of the protocol; the paper speaks of "the initial majority value".
6. **"Within `T` interactions" is stated as "at every time `T ≥ C n log n`"**: the two are
   equivalent because the consensus configurations are absorbing. The hitting time `τ*` (first
   time with `x = n` or `y = n`) is not defined.
7. **`2 ≤ n`**: an interaction needs two distinct agents (for `n ≤ 1` the interaction type is
   empty and `expList` would be `0`); the paper's statements are for sufficiently large `n`.
8. **Notation.** `Undecided.Op` is reused with `x ↦ .a`, `y ↦ .b`, blank `↦ .u` (so the letter `b`
   denotes opinion `y` in Lean but the blank state in the paper). The rules
   `B + X → X + X`, `B + Y → Y + Y` of the ROADMAP are unordered chemical-reaction-network
   notation; with the responder as the agent that changes, they are AAE's `(x, b) → (x, x)` and
   `(y, b) → (y, y)`, initiator first, which is what `step` implements.
9. **Probability model**: a finite horizon, with `T` i.i.d. uniform interactions via
   `Dynamics.expList`; the paper's filtration and stopping-time language does not appear in the
   statements.
10. **Not covered**: the epidemic-triggered start ([AAE08, §6], Thm 3, gap `Ω(n^{3/4+ε})`),
    Byzantine agents (§7), more than two values (§8).

### Differences in the proofs

The statements do not depend on these. Only some constants are needed, so the four-region
bookkeeping of [AAE08, §4] is replaced by six weighted supermartingales, all instances of one
generic lemma (`SequentialMartingale.lean`, `expList_exp_pathSum_le`): if
`avg_p exp(φ s p) · F(step s p) ≤ F s` for all `s`, then `E[exp(∑_path φ) · F(X_T)] ≤ F(X_0)`,
hence (Markov) `P[∑_path φ ≥ L] ≤ F(X_0) e^{-L} / min F`.

Notation: counts `x, y, b`, `u = x - y`, `v = x + y`; per-step indicators `I_vb` (interactions
`xb`, `yb`), `I_xy` (`xy`, `yx`), `I_ch = I_vb + I_xy`; regions (for `n ≥ 16`):
`R_b : 8v ≤ n`, `R_x : 8x ≥ 7n ∧ x < n`, `R_y` symmetric, `R_c : 8v > n ∧ 8x < 7n ∧ 8y < 7n`.

| bound | weight `φ` | potential `F` |
| --- | --- | --- |
| P1: state-changing steps ([AAE08, §4.4]; `stepSC`) | `(I_vb/5 - I_xy/6)/n` | `1/(u² + 4n)` |
| PC: central steps, `P[change] ≥ 1/128` (`stepC`) | `(R_c - 256 I_ch)/256` | `1` |
| PB: blank corner (`stepB`) | `(5/(16n))(R_b - 64 I_xy)` | `1/v` |
| PX: `x` corner (`stepX`) | `(5/(32n))(R_x - 128 I_ch)` | `3y + b + 1` |
| PY: `y` corner (`stepY`) | symmetric | `3x + b + 1` |
| PM: `u` stays positive, for Thm 2 (`stepM`) | `-(λ²/2) I_ch` | `exp(-λ max(u, 0))` |

Deterministic glue: `b_T - b_0 = S_xy - S_vb` (so `S_xy ≤ S_vb + n`); non-consensus is absorbing
backwards (not in consensus at `T` implies that all `T` steps were non-consensus steps); and
`notCons ≤ R_c + R_b + R_x + R_y`. Off the six bad events (total probability
`≤ 9n e^{-L} + e^{-u₀²/(2N)}`), `S_ch < N := 60nL + 11n` and the number of non-consensus steps is
`< 256L + 34576nL + 6336n`. Then `L = (c+2) log n` and `λ = u₀/N`.

11. **Potentials and constants.** P1 uses `1/(u² + 4n)` instead of the paper's `1/(u² + 2n)`
    (this makes the `xy`-to-`vb` ratio `5/6 < 1` with simple constants); the central region is
    handled by a Bernoulli-type supermartingale (`P[change] ≥ 1/128` there) instead of
    [AAE08, Lemma 5]; the corners use `8v ≤ n` and `8x ≥ 7n` as in [AAE08, Table 1], with our own
    weights. The constants are far larger than the paper's (`C = 40000(c+2) + 16^c`), which the
    `∃ C` statements allow; simulations suggest `≈ 4 n log n` interactions.
12. **No stopping times.** The horizon `T` is fixed; consensus is absorbing, so "not in consensus
    at `T`" means that every one of the `T` interactions happened outside consensus, and the
    counters only count interactions in non-consensus regions (`R_x` requires `x < n`).
13. **Theorem 2 via PM** instead of the coupling with a fair walk and Azuma ([AAE08, §5]): while
    `u ≥ 0`, `P[u increases] - P[u decreases] = g b u ≥ 0` with `g = 1/(n(n-1))`, and
    `cosh λ ≤ exp(λ²/2)`.
