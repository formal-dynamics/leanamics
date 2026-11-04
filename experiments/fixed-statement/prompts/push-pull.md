# Task: complete the proofs in `moran/Moran/PushPull.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The Lake
package `moran/` depends on the sibling path package `dynamics/`. Toolchain and Mathlib are
pinned and **already built**; no network access is needed and none should be attempted.

`moran/Moran/PushPull.lean` defines the death–Birth (pull) kernel and states seven theorems
about push (neutral Birth–death, `moranKernel G 1 one_pos` from `Moran/Isothermal.lean`) versus
pull (`pullKernel G`) on arbitrary graphs, proved by `sorry`. **Your job: replace every `sorry`
with a complete proof.**

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** The definitions `pullWeight`, `pullDist`, `pullKernel`,
   `pushValue`, `pullValue` must stay byte-identical, and each of the seven theorems must keep
   exactly its current text up to its `:=`. You may edit only the proofs after `:=`. Adding
   `omit … in` before a theorem to drop an unused section instance is allowed.
2. **Do not modify `moran/Moran/Isothermal.lean`** (the definitions there, such as
   `moranKernel`, `target`, `unfixed`, `fixation`, are part of the specification), nor any other
   existing file except `PushPull.lean`. You may add helper lemmas (new names) in `PushPull.lean`
   or in new files under `moran/Moran/` imported from `PushPull.lean`.
3. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, or options that
   weaken kernel checking. Raising `maxHeartbeats` locally is allowed if really needed.
4. Do **not** run writing git commands and do not run `lake update` or `lake exe cache get`.

## Commands

```bash
cd moran
lake build Moran.PushPull           # fast check of the file you are editing
lake build                          # whole package, must succeed without warnings
python3 ../scripts/check_axioms.py  # must end with "only standard Lean axioms"
```

## Progress file

Keep `moran/VOT4_PROGRESS.md` up to date (proved / remaining / current errors / plan).

## Mathematical plan

`Moran/Isothermal.lean` already contains most of the infrastructure; **reuse it** (all its
lemmas are public). In particular:

- `target_nonneg`, `target_sum_one` give 1. and 2. (`pullWeight = (1/n) * target`).
- `fixation_eq_of_invariant K ψ hstepU hacc hinv hsand habs s : fixation K s = ψ s` works for any
  kernel `K` on configurations. For push use `K = moranKernel G 1 one_pos` and
  `ψ = pushValue G · / pushValue G (fun _ => true)`; for pull use `K = pullKernel G` and
  `ψ = pullValue G · / pullValue G (fun _ => true)`. You need: the invariance (3. or 4.), the
  sandwich `allMutant ≤ ψ ≤ allMutant + unfixed` (ψ is 1 on the all-mutant configuration, 0 on the
  all-resident one, in `[0, 1]` elsewhere; the denominators are positive because a connected
  graph with at least two vertices has all degrees `≥ 1`), and the absorption facts
  (`unfixed_step`, `unfixed_access`, `moran_constant`, `allMutant_step` or analogues). For push
  (`r = 1`) the Moran absorption lemmas apply directly; for pull (5.) you need analogues.

3. **`push_value_invariant`**: write `apply f s = ∑ p, weight p * f (update s p.2 (s p.1))`. Only
   pairs `(u, w)` with `u` adjacent to `w` and `s u ≠ s w` change the configuration. An adjacent
   pair `(u mutant, w resident)` has weight `1/(n · deg u)` and raises `pushValue` by `1/deg w`;
   the reversed pair `(w, u)` has weight `1/(n · deg w)` and lowers it by `1/deg u`. The two
   contributions `1/(n · deg u · deg w)` cancel, edge by edge (isolated parents change nothing).
4. **`pull_value_invariant`**: a pair `(u, w)` sets `u` to the type of `w`. An adjacent pair with
   `u` resident and `w` mutant has weight `1/(n · deg u)` and raises `pullValue` by `deg u`, i.e.
   contributes `+1/n`; with `u` mutant and `w` resident it contributes `-1/n`. Summing over
   ordered adjacent discordant pairs, each edge contributes `+1/n - 1/n = 0`.
5. **`pull_unfixed_tendsto`**: `Dynamics.Kernel.finite_absorption` with `f = unfixed`: constant
   configurations are absorbing under pull; from a mixed configuration on a connected graph some
   resident `u` is adjacent to a mutant `w`, and the move where `u` copies `w` has positive weight
   and increases the number of mutants; induct on the number of residents (as in
   `unfixed_access`).
6., 7. **`push_fixation`, `pull_fixation`**: apply `fixation_eq_of_invariant` as described above.

When all seven theorems are proved, `lake build` succeeds without warnings and
`check_axioms.py` passes, write a short final summary.
