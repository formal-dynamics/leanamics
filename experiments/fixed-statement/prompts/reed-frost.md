# Task: complete the proofs in `epidemics/Epidemics/ReedFrost.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The Lake
package `epidemics/` depends on the sibling path package `dynamics/`. Toolchain and Mathlib are
pinned and **already built**; no network access is needed and none should be attempted.

`epidemics/Epidemics/ReedFrost.lean` defines the Reed–Frost (Independent Cascade) epidemic with one
coin per edge, the percolated graph `perc G ω`, the distance `setDist` from the initial set, and
Bernoulli coins, and states seven theorems proved by `sorry`. **Your job: replace every `sorry`
with a complete proof.**

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** The definitions `perc`, `SIR`, `step`, `run`, `setDist`,
   `bernoulli`, `coins` must stay byte-identical, and each of the seven theorems must keep exactly
   its current text up to its `:=`. You may edit only the proofs after `:=`. Adding `omit … in`
   before a theorem to drop an unused section instance is allowed.
2. Do not modify any other existing file. You may add helper lemmas (new names) in
   `ReedFrost.lean` or in new files under `epidemics/Epidemics/` imported from `ReedFrost.lean`.
3. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, or options that
   weaken kernel checking. Raising `maxHeartbeats` locally is allowed if really needed.
4. Do **not** run writing git commands and do not run `lake update` or `lake exe cache get`.

## Commands

```bash
cd epidemics
lake build Epidemics.ReedFrost      # fast check of the file you are editing
lake build                          # whole package, must succeed without warnings
python3 ../scripts/check_axioms.py  # must end with "only standard Lean axioms"
```

## Progress file

Keep `epidemics/EPI1_PROGRESS.md` up to date (proved / remaining / current errors / plan).

## Mathematical plan

Write `H = perc G ω` and `d v = setDist H I₀ v` (an `ℕ∞`, `⊤` when `v` is not connected to `I₀`).
Useful Mathlib facts: `SimpleGraph.edist` (`edist_eq_zero_iff`, `edist_ne_top_iff_reachable`,
`edist_triangle`, the existence of a walk of length `edist` when reachable, and that a walk of
length `k` gives `edist ≤ k`); `iInf` over a `Finset` membership in `ℕ∞` is attained when `I₀` is
nonempty (and is `⊤` when `I₀ = ∅`).

1. **`infected_iff` and `recovered_iff`**: prove both together by induction on `t` (the statement
   for `t + 1` uses both for `t`). Base: `run … 0 = ⟨I₀, ∅⟩`, and `d v = 0 ↔ v ∈ I₀`. Step: by
   definition `v` is infected at `t + 1` iff `v` is neither infected nor recovered at `t` (i.e.
   `d v ≥ t + 1`, using the induction hypotheses) and some `u` with `d u = t` is adjacent to `v` in
   `H` (the edge condition in `step` is exactly `H.Adj u v`). The key distance facts: if `H.Adj u v`
   then `d v ≤ d u + 1`; and if `d v = t + 1` there is `u` with `H.Adj u v` and `d u = t` (the
   second-to-last vertex of a shortest walk from the closest node of `I₀`). Recovered at `t + 1` =
   recovered or infected at `t` = `d < t ∨ d = t` = `d < t + 1`.
2. **`extinct_of_dist_lt`**: from `infected_iff`, an infected node at round `t` would have
   `d v = t ≠ ⊤`, hence `d v < t` by hypothesis, a contradiction.
3. **`extinct`**: finite distances are `≤ card V - 1` (a shortest walk is a path, so it has fewer
   than `card V` edges); apply `extinct_of_dist_lt`.
4. **`final_recovered_iff`**: `recovered_iff` at `t = card V`, plus `d v ≠ ⊤ ↔ ∃ u ∈ I₀, H.Reachable u v`
   and the bound of 3.
5. **`coins_prob_open`**: unfold `prob`/`coins`; `Dynamics.Distribution.independent_expect_eval`
   reduces it to the Bernoulli expectation of the indicator of `true`, which is `p`.
6. **`prob_infected_eq_prob_connected`**: the two events are equal for every `ω` by 4., so the
   probabilities agree (`congr`/`funext` with `propext`).

When all seven theorems are proved, `lake build` succeeds without warnings and `check_axioms.py`
passes, write a short final summary.
