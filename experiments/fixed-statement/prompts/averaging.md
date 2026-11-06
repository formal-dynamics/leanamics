# Task: complete the proofs in `averaging/Averaging/Basic.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The Lake
package `averaging/` (Mathlib only) is pinned and **already built**; no network access is needed
and none should be attempted.

The file defines the averaging dynamics on a finite simple graph (every node takes the average of
its neighbours' values) and states five theorems proved by `sorry`. **Your job: replace every
`sorry` with a complete proof.**

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** The definitions `avgStep`, `avgIter`, `degAvg` must stay byte-identical, the
   `namespace`/`open`/`variable` lines must not change, and each theorem must keep exactly its
   current text up to its `:=`. You may edit only the proofs after `:=`. Adding `omit … in`
   before a theorem to drop an unused section instance is allowed.
2. Do not modify any other existing file. You may add helper lemmas (new names) in `Basic.lean` or in
   new files under its directory imported from it.
3. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, or options that
   weaken kernel checking. Raising `maxHeartbeats` locally is allowed if really needed.
4. Do **not** run writing git commands and do not run `lake update` or `lake exe cache get`.

## Commands

```bash
cd averaging
lake build Averaging.Basic          # fast check of the file you are editing
lake build                          # whole package, must succeed without warnings
python3 ../scripts/check_axioms.py  # must end with "only standard Lean axioms"
```

Keep `averaging/PROGRESS.md` up to date (proved / remaining / current errors / plan).

## Mathematical plan

1. **`degree_weighted_sum_step`**: `deg v · (∑_{u ~ v} x u)/deg v = ∑_{u ~ v} x u` (also when
   `deg v = 0`: both sides are `0`), and `∑_v ∑_{u ~ v} x u = ∑_u deg u · x u` by double counting
   (symmetry of adjacency, `Finset.sum_comm`).
2., 3. **Maximum/minimum principle**: an average of values `≤ M` over a nonempty set is `≤ M`.
4. **`tendsto_degAvg`** (the main result). A suggested route:
   - `avgIter t x v = ∑_u W t v u * x u` with `W t v u ≥ 0`, `∑_u W t v u = 1` (no isolated nodes, as
     `G` is connected; if `V` has a single node there is no odd closed walk), and `W t v u > 0`
     whenever there is a walk of length exactly `t` from `v` to `u`.
   - From connectedness and an odd closed walk: there is `L` such that every two nodes are joined by
     a walk of length exactly `L` (go to the odd closed walk, use it to fix the parity, and pad with
     back-and-forth steps along an edge). Hence `W L v u ≥ δ > 0` for all `v, u`.
   - Doeblin contraction: for a stochastic `W` with all entries `≥ δ`,
     `max (W y) - min (W y) ≤ (1 - |V|δ)(max y - min y)`. With 2.–3. (max nonincreasing, min
     nondecreasing) every `avgIter t x v` converges to a common limit `c`.
   - Identify `c`: by 1. the degree-weighted sum is the same at every `t`, so
     `(∑ deg v) · c = ∑ deg v · x v`, i.e. `c = degAvg G x` (`∑ deg v > 0`).
   Other proofs are welcome if they are complete.
5. **`not_tendsto_of_colorable`**: take a proper 2-colouring `C` and `x v = 1` or `-1` according
   to `C v`. Every node has a neighbour (connected, at least two nodes) and all its neighbours have
   the other colour, so `avgStep G x = -x`, hence `avgIter G t x v = (-1)^t * x v` with `x v ≠ 0`,
   which has no limit.

When all five theorems are proved, `lake build` succeeds without warnings and `check_axioms.py`
passes, write a short final summary.
