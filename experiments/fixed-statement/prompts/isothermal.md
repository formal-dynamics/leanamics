# Task: complete the proofs in `moran/Moran/Isothermal.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The new
Lake package `moran/` depends on the sibling path package `dynamics/`. Toolchain and Mathlib
are pinned and **already built**; no network access is needed and none should be attempted.

`moran/Moran/Isothermal.lean` defines the Birth–death Moran process on a graph and states
eight theorems (kernel well-definedness, invariance, absorption, the isothermal theorem, its
neutral case, and Moran's formula), proved by `sorry`. **Your job: replace every `sorry` with
a complete proof.**

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** The definitions (`Config`, `mutants`, `fitness`,
   `totalFitness`, `target`, `pairDist`, `moranKernel`, `allMutant`, `unfixed`, `fixation`) must
   stay byte-identical, and each of the eight theorems must keep exactly its current text up to
   its `:=`. You may edit only the proofs after `:=`. Adding `omit … in` before a theorem to
   drop an unused section instance is allowed.
2. You **may** add new helper definitions and lemmas (with new names) in
   `moran/Moran/Isothermal.lean`, or in new files under `moran/Moran/` imported from
   `Isothermal.lean`.
3. Do **not** modify any other existing file (nothing in `dynamics/`, `voter/`, `moran/Audit.lean`,
   `moran/Moran.lean`, lakefiles, manifests, CI). You may *read* `voter/` for proof patterns, but
   `moran/` must not import it.
4. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, or options that
   weaken kernel checking. Raising `maxHeartbeats` locally is allowed if really needed.
5. Do **not** run writing git commands (`commit`, `checkout`, `reset`, `stash`, `clean`, …) and
   do not run `lake update` or `lake exe cache get`.

## Commands

```bash
cd moran
lake build Moran.Isothermal         # fast check of the file you are editing
lake build                          # whole package, must succeed
python3 ../scripts/check_axioms.py  # must end with "only standard Lean axioms"
```

Aim for a build **without warnings** (use `omit … in` for theorems that do not need an instance
from the `variable` line).

## Progress file (important)

Keep `moran/MORAN_PROGRESS.md` up to date: which theorems are proved, which remain, current
errors, and your plan. If you run out of turns, this file is how the work continues.

## Mathematical plan (informal proof to formalize)

Notation: `n = Fintype.card V`, `M = {i | s i = true}` the mutant set, `k = mutants s = |M|`,
`F = totalFitness r s`. A step picks `(u, w)` with weight `fitness u / F * target u w` and moves
to `Function.update s w (s u)`.

1. **`pair_weight_nonneg`**: `fitness ≥ 0` (as `r > 0`), `F ≥ 0` (sum of nonnegatives),
   `target ≥ 0`; combine `div_nonneg`, `mul_nonneg`.
2. **`pair_weight_sum_one`**: sum over pairs = `∑ u, fitness u / F * ∑ w, target u w`
   (`Fintype.sum_prod_type`). For each `u`, `∑ w, target u w = 1`: if `degree u = 0` it is a point
   mass; otherwise the sum is `(neighborFinset u).card * (degree u)⁻¹ = 1`
   (`SimpleGraph.card_neighborFinset_eq_degree`). Then `∑ u, fitness u / F = F / F = 1`, with
   `F > 0` because every fitness is positive and `V` is nonempty.
3. **`moran_potential_invariant`** (the key identity): write `apply f s` as
   `∑ p, weight p * f (update s p.2 (s p.1))` (`Distribution.map_expect`). The update leaves `s`
   unchanged when `s p.2 = s p.1`; when `s u = true`, `s w = false` it gives `k + 1` mutants, and
   when `s u = false`, `s w = true` it gives `k - 1`. With `W↑ = ∑_{u ∈ M, w ∉ M} weight` and
   `W↓ = ∑_{u ∉ M, w ∈ M} weight`,
   `apply f s = (1/r)^k + (1/r)^k * ((1/r - 1) * W↑ + (r - 1) * W↓)`.
   On a `d`-regular graph: if `d = 0` every target is the parent itself, so nothing changes; if
   `d > 0`, `W↑ = r * e / (F * d)` and `W↓ = e / (F * d)` where `e` counts adjacent pairs
   `(u ∈ M, w ∉ M)` (for `W↓` swap the roles using `G.adj_comm`). So `W↑ = r * W↓` and the bracket
   is `W↓ * (r * (1/r - 1) + (r - 1)) = 0`.
4. **`moran_mutants_invariant`**: the same computation with `f = mutants`, `r = 1`:
   `apply f s = k + W↑ - W↓`, and `W↑ = W↓` on a regular graph.
5. **`moran_unfixed_tendsto`**: apply `Dynamics.Kernel.finite_absorption` with `f = unfixed`:
   `unfixed` takes values in `{0, 1}`; `apply unfixed ≤ unfixed` since constant configurations are
   absorbing (every update of a constant configuration is the same constant configuration) and
   `unfixed ≤ 1`; accessibility: if `s` is not constant, both types occur, so by connectivity some
   mutant `u` is adjacent to a resident `w`, and the move `update s w true` has positive weight
   (`r > 0`, `F > 0`, `target u w = (degree u)⁻¹ > 0`) and strictly increases `k`. By induction on
   the number of residents, a positive-probability path reaches the all-mutant configuration,
   where `unfixed = 0`; conclude `iterate m unfixed s < 1` for some `m`. The file
   `voter/Voter/Absorption.lean` (`possible_positive`, `expect_lt_one`, `reachable_success`,
   `consensus_tendsto`) is a good template.
6. **`isothermal`**: let `ρ = (1/r)^n` (`ρ ≠ 1` because `r ≠ 1`, `r > 0`) and
   `ψ t = (1 - (1/r)^(mutants t)) / (1 - ρ)`. By 3 and `Kernel.iterate_invariant`,
   `iterate T ψ s = ψ s` for all `T`. Pointwise: `ψ = allMutant` on the two constant
   configurations (`ψ = 1` for all mutants, `ψ = 0` for none), and `0 ≤ ψ ≤ 1` elsewhere (since
   `0 ≤ mutants ≤ n`, whether `r > 1` or `r < 1`). Hence `|ψ t - allMutant t| ≤ unfixed t`, so
   `|ψ s - iterate T allMutant s| ≤ iterate T unfixed s → 0` by 5. Finally
   `iterate T allMutant s` is monotone in `T` (the all-mutant configuration is absorbing) and
   bounded by `1`, so its supremum `fixation` equals its limit `ψ s`. The file
   `voter/Voter/Main.lean` (`colorProbability_mono`, `colorProbability_tendsto`,
   `whiteMass_bounds`, `whiteProbability_error`, `consensus_probability`) has the same structure.
7. **`isothermal_neutral`**: as 6 with `ψ t = mutants t / n` and invariance from 4.
8. **`moran_formula`**: `⊤` is connected (`SimpleGraph.connected_top`) and `(n - 1)`-regular;
   apply 6.

Useful existing API: `Dynamics.Distribution.{expect, map, map_expect, expect_mono, expect_const,
expect_add, expect_sub, expect_mul, expect_sum, nonneg, sum_one}`, `Dynamics.Kernel.{apply,
iterate, iterate_succ, iterate_zero, iterate_invariant, iterate_mono, iterate_const, iterate_add,
iterate_mul, iterate_add_time, iterate_antitone, finite_absorption}`, Mathlib's
`SimpleGraph.{degree, neighborFinset, card_neighborFinset_eq_degree, mem_neighborFinset,
adj_comm, Connected}`. Read `dynamics/Dynamics/*.lean` and `voter/Voter/*.lean` for exact
statements before relying on them.

When all eight theorems are proved, `lake build` succeeds and `check_axioms.py` passes, write a
short final summary (what you proved, any helper lemmas you added, anything noteworthy).
