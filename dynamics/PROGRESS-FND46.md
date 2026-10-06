# PROGRESS: FND-4 (finite-horizon optional stopping) and FND-6 (time reversal)

Source: `ROADMAP.md`, rows FND-4 and FND-6. Branch `fnd4-optional-stopping`.

## Status (2026-10-06)

* **Phase 1 (pin statements): done** (commit 459e3e6).
* **Phase 2 (proofs + refactor): done.** No `sorry`; `lake build Dynamics`, `lake build Voter`,
  `lake build Moran` succeed with **no warnings**; `python3 ../scripts/check_axioms.py` passes in
  all three packages (only `propext`, `Classical.choice`, `Quot.sound`); pinned text up to `:=`
  verified identical to the phase-1 commit for all 74 entries of `PINNED.txt`.

## Pinned (see `PINNED.txt`; text up to `:=` is frozen)

New (`dynamics/`, namespace `Dynamics.Kernel` unless noted), all **proved**:

| Declaration | File | Statement in words |
| --- | --- | --- |
| `event_error_of_invariant` | `Dynamics/OptionalStopping.lean` | Finite time `T`: if `φ = φA` on `A`, `φ = φB` on `B`, `m ≤ φ − φB ≤ M` off `A ∪ B` and `K.iterate T φ x₀ = φ x₀`, then `m·P_T(S) ≤ φ x₀ − φB − (φA − φB)·P_T(A) ≤ M·P_T(S)`, `S = ¬A ∧ ¬B` |
| `tendsto_event_of_invariant` | same | If moreover `φA ≠ φB`, `∀ T, K.iterate T φ x₀ = φ x₀`, and `P_T(S) → 0`, then `P_T(A) → (φ x₀ − φB)/(φA − φB)` |
| `iSup_event_of_invariant` | same | Same hypotheses plus `A` absorbing (`∀ a, A a → (K a).prob A = 1`): `⨆ T, P_T(A) = (φ x₀ − φB)/(φA − φB)` |
| `Dynamics.expList_comp_reverse` | `Dynamics/Reverse.lean` | `expList α T (F ∘ List.reverse) = expList α T F` |
| `iterate_ofStep_foldr` | same | `(ofStep step).iterate T f s = expList R T (fun l => f (l.foldr (fun r t => step t r) s))` |

Here `P_T(E) = K.event E T x₀`. No new definitions were introduced. Frozen existing
declarations: the README results of `voter/` and `moran/`, the definitions they mention, and
`Dynamics.Kernel.exists_stationary`; all unchanged.

## Proved / changed (phase 2)

`dynamics/`:
* `Kernel.lean`: `event_eq_iterate` (`event` with any `Decidable` instance).
* `Distribution.lean`: `prob_eq_expect` (same for `prob`).
* `OptionalStopping.lean` (134 lines): `eq_add_target_add_survival` (pointwise decomposition
  `φ − φB = (φA − φB)·1_A + (φ − φB)·1_S`, no disjointness needed), `iterate_eq_event_add`
  (its expectation at time `T`), then the three pinned theorems.
* `Reverse.lean` (52 lines): `reverse_ofFn` (`(ofFn ω).reverse = ofFn (ω ∘ Fin.rev)`), then the
  two pinned theorems (reindex `Fin T → α` by `Fin.revPerm` in `expList_eq_avg_ofFn`).
* `Audit.lean`, `README.md` (module table), blueprint (`thm:optional-stopping`, `thm:reverse`).

`moran/` (net −170 lines in `Moran/`):
* `fixation_eq_of_invariant` (name kept: `PROVENANCE.md` cites it) is now a wrapper of
  `iSup_event_of_invariant` with **weaker hypotheses**: harmonic `ψ`, `ψ(all mutant) = 1`,
  `ψ(all resident) = 0`, absorbing all-mutant, survival → 0. No sandwich bounds on `ψ`.
* Bridges: `iterate_allMutant`, `unfixed_eq`, `iterate_unfixed` (indicators as `Kernel.event`).
* Callers `isothermal`, `isothermal_neutral`, `push_fixation`, `pull_fixation` now pass the
  values at the two constant configurations and `moran_unfixed_tendsto`/`pull_unfixed_tendsto`.
* Removed (only served the old inline sandwich argument, unpinned, no other users):
  `fixation_mono`, `fixation_le_one`, `fixation_tendsto`, `moranPsi_bounds`, `moranPsi_sandwich`,
  `neutralPsi_bounds`, `neutralPsi_sandwich`, `allMutant_le_one`, `allMutant_false`,
  `pushRatio_sandwich`, `pullRatio_sandwich`, `pushValue_nonneg`, `pushValue_le`,
  `pullValue_nonneg`, `pullValue_le`. Blueprint `\lean{}` lists updated (all names resolve).

`voter/`:
* `whiteProbability_error` (pinned) is now `event_error_of_invariant` with the two consensus
  configurations as targets, `m = 0`, `M = 1`, the bounds off the targets taken from the pinned
  Lemma 2.2 sandwich `whiteMass_bounds`. `whiteProbability_tendsto` keeps its squeeze from it.
* Bridges: `survival_eq`, `iterate_survival` (in `Absorption.lean`), `whiteMass_const`,
  `colorProbability_eq_event` (in `Main.lean`).
* README, blueprint (library restatement `thm:optional-stopping`, used by `lem:22`),
  `FORMALIZATION_DIFFERENCES.md` (line anchors recomputed, proof route described).

## Remaining

* Nothing in `dynamics/`, `voter/`, `moran/`.
* Outside the allowed directories (left for the maintainer): mark FND-4 and FND-6 as done in
  `ROADMAP.md`; optionally mention `Dynamics.Kernel.iSup_event_of_invariant` next to
  `fixation_eq_of_invariant` in `PROVENANCE.md`.

## Errors / notes

* `K.event` / `prob` use classical decidability, while package indicators (`allMutant`, `allColor`,
  `unfixed`, `survival`) use other instances (e.g. the pi-type `DecidableEq`), so bridges are
  `congr` proofs, not `rfl` (`event_eq_iterate`, `prob_eq_expect` encapsulate this).
* `Kernel (Config V)` needs `Fintype (V → Bool)`, hence `DecidableEq V`: do not `omit` it.
* Voter: proving `whiteProbability_error`/`_tendsto` without any lemma that needs `[Nonempty V]`
  triggers the unused-section-variable linter on the **pinned** signatures. Adding
  `omit [Nonempty V] in` would silently change their elaborated statements, so instead the
  off-target bounds come from `whiteMass_bounds` (which genuinely uses `Nonempty V`), and
  `whiteProbability_tendsto` keeps the squeeze through `whiteProbability_error`.
* `simp [List.foldl_eq_foldr_reverse]` loops; plain `simp` closes the foldr goal.
* Moran/voter `.lean` lines over 100 columns (`Isothermal.lean:316`, `Main.lean:98`,
  `dynamics/Dynamics/Absorption.lean:82`) are pre-existing and were left untouched.

## Deviations from the source (roadmap rows)

1. **Targets are events, not states.** `A`, `B : α → Prop` with `φ` constant (`φA`, `φB`) on
   each; the roadmap's `φ(A)`, `φ(B)` for states `a`, `b` is the case `A = (· = a)`,
   `B = (· = b)`. Strictly more general; matches `Kernel.event`.
2. **"Absorption probability" without path space.** The library has no hitting times, so the
   conclusion is stated (i) as the limit of `P(X_T ∈ A)` (no absorption hypothesis needed) and
   (ii) as the supremum `⨆ T, P(X_T ∈ A)` when `A` is absorbing, which is how `Moran.fixation`
   and `Voter.eventualColor` define it. No new definition was added (ground rules).
3. **Invariance hypothesis read literally:** `∀ T, K.iterate T φ x₀ = φ x₀` (only from `x₀`).
   A harmonic `K.apply φ = φ` gives it via `Kernel.iterate_invariant`.
4. **Survival → 0 is a hypothesis** on `K.event (¬A ∧ ¬B)` at `x₀`, as in the roadmap; for
   chains it is supplied by `Kernel.finite_absorption`.
5. **No boundedness or disjointness hypotheses:** `φ` is bounded since `α` is finite, and
   `A ∩ B = ∅` is implied by `φA ≠ φB` (the finite-time bound needs neither).
6. **Additions:** the quantitative finite-time bound `event_error_of_invariant` (generalizes
   `Voter.whiteProbability_error`), and the corollary `iterate_ofStep_foldr` of FND-6.
7. **FND-6 needs no `Nonempty α`:** for empty `α` both sides are `0` (`avg` convention) when
   `T > 0`, and equal `F []` when `T = 0`.
8. **Phase 2 (refactor, not a statement deviation):** the unpinned
   `Moran.fixation_eq_of_invariant` changed its hypotheses (weaker: no sandwich bounds; survival
   limit passed directly), and 15 unpinned helper lemmas that only served the old argument were
   removed (listed above).
