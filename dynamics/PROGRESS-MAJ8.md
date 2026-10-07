# PROGRESS: MAJ-8, first half (drift hitting-time lemma, DGM+11 Claim 2.9)

Source: `ROADMAP.md`, row MAJ-8 (only the lemma; the symmetry-breaking application to
`3-majority/` is NOT part of this job). Branch `maj8-drift-hitting`. Write scope: `dynamics/` and
`PINNED.txt` at the repository root.

Paper: Doerr, Goldberg, Minder, Sauerwald, Scheideler, *Stabilizing consensus with the power of
two choices*, SPAA 2011, pp. 149–158, doi:10.1145/1989493.1989516. Text read from a local
extraction (`~/repos/vibe-proving/scheideler_problem/refs/SelfStabilizing.txt`, lines 822–870).
Claim 2.9, verbatim (proof omitted in the paper, "due to space constraints"):

> Let `(X_t)_{t=1}^∞` be a Markov Chain with state space `{0, …, q}` that has the following
> properties:
> * there are constants `c1 > 1` and `c2 > 0`, such that for any `t ∈ ℕ`,
>   `Pr[X_{t+1} ≥ min{c1 X_t, q}] ≥ 1 − e^{−c2 X_t}`,
> * `X_t = 0 ⇒ X_{t+1} ≥ 1` with probability `c3` which is a constant greater than 0.
>
> Let `c4 > 0` be an arbitrary constant and `T := min{t ∈ ℕ : X_t ≥ c4 log q}`. Then for every
> constant `c6 > 0` there is a constant `c5 = c5(c4, c6) > 0` such that
> `Pr[T ≤ c5 · log q + log_{c1}(c4 log q)] ≥ 1 − q^{−c6}`.

Use in the paper (Lemma 2.8): `Υ_τ = ⌊Δ_{t+τ−1}/(c√n)⌋`, `q = ⌊(n/2)/(c√n)⌋`; the first property
comes from Lemma 2.7 (Chernoff, only for `6√n ≤ Δ ≤ c√(n log n)`), the second from Lemma 2.5
(CLT). Survey: Becchetti, Clementi, Natale, *Consensus dynamics: an overview*, SIGACT News 51(1),
2020 (hal-02507613), §4 Case 3, only cites the claim (`Z_t = ⌊s/(γ√n)⌋`, target `α log q`).
Related: Clementi, Ghaffari, Gualà, Natale, Pasquale, Scornavacca, arXiv:1707.05135, Lemma 4.5
("a variant of Claim 2.9 … we were not able to find a published proof"), stated for a finite
chain with an observable `f : Ω → [0, n]` and proved with an exponential potential. DGM+11's
Claim 3.4 is a different variant (absorbing `{0, q}`), out of scope.

## Status

* **Phase 1 (pin statements): done (2026-10-07).** `lake build Dynamics` succeeds; the only
  warnings are `declaration uses 'sorry'` (two, `DriftHitting.lean` lines 39 and 56).
* **Phase 2 (proofs): done (2026-10-07).** Both pinned theorems are proved, with no `sorry`.
  `lake build Dynamics` has no warnings. `python3 ../scripts/check_axioms.py` passes
  (23 declarations in `Audit.lean`, 3 of them new). A scratch `#print axioms` over the pinned
  declarations and the main helpers shows only `propext`, `Classical.choice`, `Quot.sound`.
  The text of every pinned declaration up to `:=` (docstrings included) is byte-identical
  to the phase-1 commit `481ced3` (checked by script); `DriftHittingDefs.lean` is unchanged.

## Pinned (see `PINNED.txt` at the repository root; text up to `:=` is frozen)

Namespace `Dynamics.Kernel`. `universe u` is declared in `DriftHitting.lean` (the theorems
quantify `∀ {α : Type u}` *inside* `∃ c₅`, so `c₅` is uniform over chains and `q`).

| Declaration | File | Statement in words |
| --- | --- | --- |
| `hitProb` (def) | `Dynamics/DriftHittingDefs.lean` | `K.hitProb B n a = P_a(∃ s ≤ n, X_s ∈ B)` (= `P_a(T_B ≤ n)`), defined as `K.trajectory n a` of the indicator "history or endpoint in `B`" (classical decidability) |
| `drift_hitting` | `Dynamics/DriftHitting.lean` | Claim 2.9: `1 < c₁`, `0 < c₂, c₃, c₄, c₆` ⇒ `∃ c₅ > 0, ∀ α K (X : α → ℕ) q`, `X ≤ q`; growth `1 − exp(−c₂ X a) ≤ P_{K a}(min (c₁ X a) q ≤ X b)` at every `a` with `X a < c₄ log q`; escape `X a = 0 → c₃ ≤ P_{K a}(1 ≤ X b)`; `c₄ log q ≤ q` ⇒ `∀ a₀ t, c₅ log q + logb c₁ (c₄ log q) ≤ t → 1 − q^(−c₆) ≤ K.hitProb (c₄ log q ≤ X ·) t a₀` |
| `drift_hitting_log` | same | same hypotheses, `∃ C > 0`, conclusion for every `t ≥ C log q` |

Checked in scratch files (in `/tmp`, not in the repo): `#check` shows real casts everywhere,
`q ^ (-c₆)` is `Real.rpow`; the source's literal setting (`α = Fin (q + 1)`, `X = Fin.val`,
escape hypothesis only at `0`) follows from `drift_hitting.{0}` in a few lines;
`hitProb B 0 a = if B a then 1 else 0` and
`hitProb B 1 a = (K a).expect (fun b => if B a ∨ B b then 1 else 0)` by `simp`.

## Proved

Files (all in `dynamics/Dynamics/`):

* `DriftHittingDefs.lean` (28 lines, unchanged): `hitProb` (pinned).
* `DriftHittingStop.lean` (134 lines, new, reusable): `hitProb_of_mem`, `hitProb_zero_of_not_mem`,
  `hitProb_succ_of_not_mem` (the recursion of `hitProb`); `stopped` (unpinned def),
  `stopped_of_mem`, `stopped_of_not_mem`; `iterate_stopped_eq_one_sub_hitProb` and
  `one_sub_hitProb_eq_event_stopped` (`P(T_B > n)` = event `¬B` of the stopped chain);
  **`one_sub_hitProb_le_of_drift`** (geometric drift `K V ≤ ρ V` off `B` ⇒
  `P_a(T_B > t) ≤ ρ^t V(a)/Vmin`, by FND-5's `multiplicative_drift` on the stopped chain).
* `DriftHittingAux.lean` (305 lines, new): `Distribution.prob_mono`,
  `Distribution.expect_le_of_prob` (`f ≤ M`, `f ≤ m` on `E`, `P(E) ≥ s` ⇒
  `𝔼f ≤ M − (M − m)s`); `exp_neg_le_quarter`, `exists_threshold` (choice of `x₀`),
  `low_drift_ineq`, `high_drift_ineq` (the two drift inequalities as standalone algebra),
  **`exists_potential`** (`ρ < 1` and antitone `g` with `½e^{−c₂x/2} ≤ g ≤ 1` and the
  low- or high-level drift at each level), **`apply_potential_le`** (one chain step lowers
  `V = g ∘ X` by the factor `ρ` below the target), `two_mul_pow_mul_exp_le` (final exp/log
  arithmetic).
* `DriftHitting.lean` (152 lines): the two pinned proofs (`drift_hitting` ≈ 85 lines,
  `drift_hitting_log` 14 lines).

Proof route: the paper omits the proof, so this is our own, following plan steps 1–6 below
almost exactly. Implementation details that differ from the plan:
* The `hitProb` API consists of case lemmas (`_of_mem`, `_succ_of_not_mem`) with no
  `DecidablePred` argument, which avoids decidability-instance mismatches with the classical
  `hitProb`, `event` and `prob`. The stopped-chain bridge is proved for any observable `f` with
  `f = 0` on `B` and `f = 1` off `B` (`iterate_stopped_eq_one_sub_hitProb`), and is then
  specialized to `event`.
* `x₀` comes from `exists_threshold` as an opaque natural number. A `set x₀ := max N₁ N₂`
  made elaboration time out. `e^{−u} ≤ 1/4` uses `u ≥ 3` and `e^u ≥ 1 + u`, so no logarithms
  are needed.
* `D = max 0 (−log_{c₁}(c₄ log 2))`, `c₅ = (1 + c₂c₄/2 + c₆)/log(1/ρ) + D/log 2` as planned;
  `drift_hitting_log` takes `C = c₅ + c₄/log c₁` (`Real.log_le_self`).
* The case "started on the target" is split off first (`hitProb = 1`). Otherwise
  `0 ≤ X a₀ < c₄ log q` forces `log q > 0`, hence `q ≥ 2`, so no separate `q ≤ 1` analysis is
  needed.

Before phase 2 the truth of the pinned statements was also checked numerically: for the worst-case chain (failure resets to 0), the decay rate of
`P_0(T > t)` converges as the target grows, e.g. `t/log q → ≈ 448 c₆` for
`(c₁, c₂, c₃) = (1.5, 0.3, 0.05)`; for harsh parameters the constant is huge
(`≈ 1.3·10¹²` for `(1.05, 0.05, 0.2)`) but finite.

## Remaining

Nothing inside `dynamics/`. Docs were done in phase 2: README module table (three rows),
blueprint section "Hitting times" (`def:hitprob`, `lem:hitdrift`, `thm:drifthitting`; every
`\lean{}` name was checked to resolve), and `Audit.lean` (`one_sub_hitProb_le_of_drift`,
`drift_hitting`, `drift_hitting_log`).

Outside the write scope (left for the maintainer): the ROADMAP MAJ-8 status (first half done)
and a PROVENANCE entry. For the latter: no published proof exists (DGM+11 omit it; CGPS17 say
they could not find one); own proof by a potential function plus FND-5's multiplicative drift;
the constant `c₅` is explicit but astronomically large for small `c₁ − 1`, `c₂` (it comes from
`p^{x₀}`). The second half of MAJ-8 (symmetry breaking for 3-majority/2-Choices) is open; it
needs the CLT-type escape bound (paper's Lemma 2.5) and the growth bound (Lemma 2.7) as the
hypotheses of `drift_hitting`.

## Errors / notes

* `hitProb` is defined with `:= by classical exact …` (no pattern matching), so the
  "up to `:=`" gate reads it correctly (cf. the `iterateSeq` wrinkle in `PROGRESS-FND5.md`).
* The outer hypotheses `hc₁ … hc₆` are named: phase 2 must use each of them (the
  `unusedVariables` linter would otherwise warn, and renaming to `_hc` changes the frozen text).
  The plan below uses all of them (`hc₄` for `c₄ log 2 > 0`, `hc₆` for `0 < c₅`). The hypotheses
  inside `∃` are anonymous arrows (no lint).
* `Dynamics/Concentration.lean` is not needed: the claim's hypotheses are already
  probabilities (concentration enters only in the application, Lemma 2.7).
* Phase 2: all of `hc₁ … hc₆` are used. The anonymous hypothesis `∀ a, X a ≤ q` is not
  needed by the proof (states with `X > q` are on the target anyway); it stays as the source's
  "state space `{0, …, q}`".
* `λ` is a reserved token in Lean 4 (`hλ` does not parse); `Real.exp_lt_one` and
  `Real.log_two_pos` do not exist in this Mathlib (use `Real.exp_lt_exp` with `exp_zero`, and
  `Real.log_pos one_lt_two`).
* Unfolding `Kernel.event` exposes `Classical.propDecidable`, while a restated `if ¬B b`
  elaborates with `instDecidableNot`. Characterize indicators propositionally (see
  `iterate_stopped_eq_one_sub_hitProb`) rather than restating them.

## Plan (phase 2), carried out

Files: `Dynamics/DriftHittingAux.lean` (helpers, imported by `DriftHitting.lean`), keep
`DriftHittingDefs.lean` unchanged except for unpinned API lemmas appended after `hitProb`.

1. **`hitProb` API.** `hitProb_zero`; `hitProb_succ : K.hitProb B (n+1) a = if B a then 1 else
   (K a).expect (K.hitProb B n)` (induction on the `trajectory` recursion, generalizing the
   functional: `∃ x ∈ a :: l, B x ↔ B a ∨ ∃ x ∈ l, B x`); `hitProb_of_mem` (`= 1` if `B a`),
   `hitProb_nonneg`, `hitProb_le_one`, `hitProb_mono` in `n`.
2. **Stopped kernel** (unpinned def): `stopped K B a := if B a then point a else K a`
   (classical). Bridge: `1 - K.hitProb B n a = (K.stopped B).event (fun b => ¬ B b) n a`
   (same recursion; `B` absorbing in the stopped chain).
3. **Geometric drift ⇒ hitting tail** (reuses FND-5): if `V ≥ 0`, `V = 0` on `B`,
   `Vmin ≤ V` off `B` (`Vmin > 0`), `K.apply V a ≤ ρ V a` for `a ∉ B`, then
   `1 - K.hitProb B t a₀ ≤ ρ^t V a₀ / Vmin`. Proof: `multiplicative_drift` on `K.stopped B`
   with `Ψ = V`, `δ = 1 - ρ` (on `B` the stopped kernel is a point mass, `apply V = 0`), and
   `{0 < V} = {¬B}`.
4. **Potential for Claim 2.9.** `L := c₄ log q`, `p := min c₃ (1 - exp (-c₂)) ∈ (0, 1)`,
   `β := c₂ / 2`. Choose `x₀ : ℕ` with `p ^ x₀ ≤ 1/2`, `exp (-β (c₁ - 1) x₀) ≤ 1/4`,
   `exp (-c₂ x₀) ≤ 1/4` (so `x₀ ≥ 1`). `η := 1 / (2 (p^{-x₀} - 1)) ∈ (0, 1/2]`,
   `ρ := 1 - (1 - p) η / 2 ∈ [3/4, 1)`.
   `g x := 1 - η (p^{-x} - 1)` for `x ≤ x₀` (decreasing from `1` to `g x₀ = 1/2`),
   `g x := (1/2) exp (-β (x - x₀))` for `x ≥ x₀`; `V a := if L ≤ X a then 0 else g (X a)`.
   * Small levels `x < x₀`, `x < L`: success (prob `≥ p`: `c₃` at `0`, `1 - e^{-c₂ x} ≥
     1 - e^{-c₂}` at `x ≥ 1`) gives `X' ≥ x + 1` (as `min (c₁ x) q > x` because `x < L ≤ q`),
     so `𝔼V' ≤ p g(x+1) + 1 - p ≤ ρ g x`. Check: the gap is
     `(1-ρ)(η p^{-x} - 1) + η(ρ - p) ≥ η(ρ - p) - (1-ρ)(1-η) ≥ 0` since
     `1 - η/2 ≥ (1 - η)/2`.
   * High levels `x₀ ≤ x < L`: success gives `X' ≥ min (c₁ x) q` (target if `≥ L`), so
     `𝔼V' ≤ g(c₁ x) + e^{-c₂ x} ≤ (e^{-β(c₁-1)x₀} + 2 e^{-c₂ x₀}) g x ≤ (3/4) g x ≤ ρ g x`.
   * `V ≤ 1`; off target `V ≥ (1/2) e^{-βL} = (1/2) q^{-β c₄}`. Hence
     `1 - hitProb ≤ 2 ρ^t q^{β c₄} ≤ q^{-c₆}` once `t log(1/ρ) ≥ log 2 + (β c₄ + c₆) log q`.
5. **Constants.** `D := max 0 (-(logb c₁ (c₄ log 2)))`,
   `c₅ := (1 + β c₄ + c₆) / log (1/ρ) + D / log 2`. For `q ≥ 2`:
   `logb c₁ (c₄ log q) ≥ logb c₁ (c₄ log 2) ≥ -D` (uses `hc₁`, `hc₄`), and `log q ≥ log 2`
   turns `t ≥ c₅ log q - D` into the bound of step 4. For `q ≤ 1`: `log q = 0`, the target
   `0 ≤ X b` holds everywhere, `hitProb = 1`, and `1 - q^{-c₆} ≤ 1` (`rpow` of `q ≥ 0` is
   `≥ 0`).
6. **`drift_hitting_log`.** `C := c₅ + c₄ / log c₁`, using
   `logb c₁ y ≤ (y - 1) / log c₁ ≤ y / log c₁` (`Real.log_le_sub_one_of_pos`) for `y > 0`.

## Deviations from the paper

1. **General finite chain with an observable.** The paper states the claim for a Markov chain
   on `{0, …, q}`; we state it for a `Dynamics.Kernel` on any finite `α` and an observable
   `X : α → ℕ` with `X ≤ q`, the hypotheses holding from every state (i.e. conditionally on the
   whole state). The paper's chain is `α = Fin (q + 1)`, `X = Fin.val` (checked). Reason: the
   application (Lemma 2.8, survey §4 Case 3) uses `Υ = ⌊Δ/(c√n)⌋`, a function of the
   configuration that is not itself a Markov chain; CGPS17's Lemma 4.5 uses the same form.
2. **Time-homogeneous kernel.** The paper's "for any `t ∈ ℕ`" allows time dependence, and
   Lemma 2.8 applies the claim with a `√n`-bounded (adaptive) adversary. A kernel covers
   adversaries that are functions of the current state; time- or history-dependent ones need
   that information in the finite state (as FND-5 deviation 3). A `_seq` version would need a
   time-dependent `hitProb`.
3. **Added hypothesis `c₄ log q ≤ q`** (the target is a possible value of `X`). Without it the
   claim is false: for `c₄ = 10`, `q = 2` the target `10 log 2 > 2` is never hit, while
   `1 - 2^{-c₆} > 0`. The paper is asymptotic in `q`, where this holds.
4. **Growth only below the target** (generalization): the first property is assumed only at
   states with `X a < c₄ log q`, since `T` depends only on the chain before hitting. This
   matters for the application: Lemma 2.7 gives growth only for `Δ ≤ c√(n log n)`.
5. "`X_{t+1} ≥ 1` with probability `c3`" is read as "with probability at least `c₃`".
6. **`c₅` depends on `c₁, c₂, c₃` too** (written `c5(c4, c6)` in the paper, where `c1, c2, c3`
   are fixed constants of the chain). Necessary: the waiting time at `0` alone is `≈ 1/c₃`
   steps, and numerically `c₅` can be `≈ 10¹²` (see Proved).
7. **Natural logarithms** (`Real.log`); the paper does not fix the base. A base change is a
   constant factor absorbed by `c₄` (universally quantified) and `c₅` (existential).
   `log_{c₁}` is `Real.logb c₁`.
8. **Time origin.** The paper's chain starts at `X_1` and `T = min{t ∈ ℕ : X_t ≥ c4 log q}`;
   we start at time `0` and `hitProb … t a₀` counts the states at times `0, …, t` (`t`
   transitions). The two readings differ by one step, which `c₅` absorbs (`log q ≥ log 2` for
   `q ≥ 2`; for `q ≤ 1` the target `c₄ log q = 0` is hit at time `0`). The bound is stated for
   every integer `t ≥ c₅ log q + log_{c₁}(c₄ log q)`, equivalent to `T ≤` that real number.
9. Deterministic start `a₀`; a random start follows by averaging.
10. **Edge cases** `q ∈ {0, 1}`: Lean's `Real.log 0 = Real.log 1 = 0` makes the target `0`,
    hit at time `0`; the statements hold trivially there.
11. **Extra corollary** `drift_hitting_log` (not in the paper): the `O(log q)` form used by
    applications; `log_{c₁}(c₄ log q) ≤ c₄ log q / log c₁` is absorbed into the constant.
12. `hitProb` is a thin wrapper over the existing `Kernel.trajectory` (expectation of a path
    indicator); no new expectation, probability or distribution notion is introduced.
