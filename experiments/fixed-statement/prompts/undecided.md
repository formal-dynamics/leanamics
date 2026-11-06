# Task: complete the proofs in `undecided/Undecided/Basic.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The Lake
package `undecided/` depends on the sibling path package `dynamics/` (finite probability layer:
`Dynamics.avg`, `Dynamics.Kernel`, `Kernel.ofStep`, `Kernel.finite_absorption`, ...). Toolchain and
Mathlib are pinned and **already built**; no network access is needed and none should be attempted.

The file defines the synchronous binary undecided-state dynamics on `n` nodes (each node samples
one node uniformly, with replacement) and states six theorems proved by `sorry`. **Your job:
replace every `sorry` with a complete proof.**

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** The definitions `Op`, `update`, `Config`, `step`, `count`, `Mono`, `notMono`, `kernel` must stay byte-identical, the
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
cd undecided
lake build Undecided.Basic          # fast check of the file you are editing
lake build                          # whole package, must succeed without warnings
python3 ../scripts/check_axioms.py  # must end with "only standard Lean axioms"
```

Keep `undecided/PROGRESS.md` up to date (proved / remaining / current errors / plan).

## Mathematical plan

Write `a, b, q` for `count x .a, count x .b, count x .u` (so `a + b + q = n`).

1.–3. **Expectations.** `count y o = ∑ v, [y v = o]`, so by linearity (`Dynamics.avg_sum` etc.) it
   suffices to compute, for each node `v`, the average over `r : Fin n → Fin n` of the indicator of
   `update (x v) (x (r v)) = o`. That indicator depends only on `r v`, and `r v` is uniform on
   `Fin n` (the average over all functions of `g (r v)` equals the average over `Fin n` of `g`). An
   `a`-node stays `a` unless it samples a `b`-node (probability `b/n`); an undecided node becomes `a`
   with probability `a/n`; a `b`-node never becomes `a`. Summing over nodes:
   `a(1 - b/n) + q·a/n = a(n - b + q)/n`. Symmetrically for `b`. A node is undecided afterwards iff it
   was undecided and sampled an undecided node, or was decided and sampled the other opinion:
   `q·q/n + a·b/n + b·a/n`.
4. **`expected_bias`** follows from 1. and 2. (`avg_sub`) and `a(n - b + q) - b(n - a + q) = (a - b)(n + q)`.
5. **`step_of_mono`**: if every node holds `o`, then `update o o = o` for each of the three cases.
6. **`absorbed`**: apply `Dynamics.Kernel.finite_absorption` with `f = notMono` (values in `{0, 1}`).
   Step condition: from a monochromatic configuration the kernel stays there (5.), so
   `apply notMono x = 0`; otherwise `apply notMono x ≤ 1`. Accessibility within two rounds: if some
   node `w` holds `a` (or `b`), the round in which every node samples `w` has positive probability;
   after it every node holds `a` or `u` and `w` still holds `a`, and a second such round makes
   everybody `a`; if no node is decided the configuration is already monochromatic. Use
   `Kernel.apply_ofStep`/`Kernel.iterate_ofStep` to turn kernel iterates into averages over rounds.

When all six theorems are proved, `lake build` succeeds without warnings and `check_axioms.py`
passes, write a short final summary.
