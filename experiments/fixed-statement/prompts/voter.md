# Task: complete the proofs in `voter/Voter/Coalescence.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The Lake
package `voter/` depends on the sibling path package `dynamics/`. Toolchain and Mathlib are
pinned and **already built**; no network access is needed and none should be attempted.

`voter/Voter/Coalescence.lean` states the voter model / coalescing random walks duality and a
consensus-time bound on the complete graph with self-loops, with seven theorems proved by
`sorry`. **Your job: replace every `sorry` with a complete proof.**

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** The four definitions (`runRounds`, `backward`,
   `disagreement`, `wfKernel`) must stay byte-identical, and each of the seven theorems must keep
   exactly its current text up to its `:=`. Do not rename, generalize, specialize or reorder
   their hypotheses. You may edit only the proofs after `:=`.
2. You **may** add new helper definitions and lemmas (with new names) in
   `voter/Voter/Coalescence.lean`, or in new files under `voter/Voter/` (then import them from
   `Coalescence.lean`; `voter/Voter.lean` already imports `Voter.Coalescence`).
3. Do **not** modify any other existing file (in particular nothing in `dynamics/`,
   `voter/Audit.lean`, lakefiles, manifests or CI files).
4. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, or options that
   weaken kernel checking. Raising `maxHeartbeats` locally is allowed if really needed.
5. Do **not** run writing git commands (`commit`, `checkout`, `reset`, `stash`, `clean`, …) and
   do not run `lake update` or `lake exe cache get`.

## Commands

```bash
cd voter
lake build Voter.Coalescence        # fast check of the file you are editing
lake build                          # whole package, must succeed
python3 ../scripts/check_axioms.py  # must end with "only standard Lean axioms"
```

Aim for a build of `Voter.Coalescence` **without warnings** (the unused-section-variable
linter is on: use `omit … in` for theorems that do not need an instance from the `variable`
line).

## Progress file (important)

Keep `voter/VOT3_PROGRESS.md` up to date as you go: which theorems are proved, which remain,
the current errors, and your plan. If you run out of turns, this file is how the work
continues.

## Mathematical plan (informal proof to formalize)

Notation: `n = Fintype.card V`; a round is `r : V → V`; rounds are listed first-round-first.

1. **`runRounds_eq_comp`**: induction on `l` generalizing `s`. `runRounds s (r :: l) =
   runRounds (step s r) l = (s ∘ r) ∘ backward l = s ∘ (r ∘ backward l)`, and
   `backward (r :: l) = r ∘ backward l` by `List.foldr`. Base case: `s ∘ id = s`.
2. **`disagreement_runRounds_eq_zero`**: by 1, `runRounds s l = s ∘ backward l`, which is
   constant when `backward l` is constant (use an element of `V` from `Nonempty V`).
3. **`disagreement_eq_survival`**: both are the same classical `if` (unfold both).
4. **`iterate_wfKernel_eq_expList`**: induction on `T` generalizing `s`.
   `Kernel.iterate_succ` gives `(transition H).apply (iterate T f) s`; `transition_apply` turns
   it into `round H s _ = (Distribution.independent H).expect (fun r => _ (step s r))`. For
   `H = wfKernel V` every row is `Distribution.uniform V`, so `Distribution.independent H` is the
   uniform distribution on `V → V` (weights `∏ 1/n = 1 / card (V → V)`); relate its `expect` to
   `Dynamics.avg` (see `Distribution.uniform_expect`). Then `Dynamics.expList_succ` and the
   induction hypothesis at `step s r` finish, since `runRounds s (r :: l) = runRounds (step s r) l`.
5. **`expList_backward_ne`**: induction on `T`, generalizing over the pair (state a version for
   arbitrary `x y : V`, with value `0` if `x = y`). Base: `expList … 0 F = F []`, and
   `backward [] = id`. Step: `expList (T+1) F = avg (fun r => expList T (fun l => F (r :: l)))`,
   and `backward (r :: l) u = r (backward l u)`. Swap the outer `avg` over `r` with `expList T`
   (finite sums commute; prove a small lemma `avg (fun a => expList T (G a)) =
   expList T (fun l => avg (fun a => G a l))` by induction on `T`). For fixed `x ≠ y`,
   `avg (fun r : V → V => if r x = r y then 0 else 1) = 1 - 1/n` (the coordinates `r x`, `r y`
   are independent and uniform: count functions, or use a product decomposition as in
   `Dynamics.avg_prod_pi` / `Dynamics.avg_eval`, which are stated for `Fin n → γ` and may need a
   version for `V → V`); for `x = y` it is `0`. Hence the step multiplies by `(1 - 1/n)`.
6. **`iterate_disagreement_le`**: fix `u₀ : V`. Pointwise, `disagreement (runRounds s l) ≤
   ∑ v ∈ univ.erase u₀, (if backward l v = backward l u₀ then 0 else 1)` (if every backward
   walk meets `u₀`'s, the map is constant and 2. applies). Take `expList`, use 4., linearity and
   monotonicity of `expList` (`Dynamics.expList_le_expList`, and a sum rule), then 5. for each of
   the `n - 1` terms.
7. **`voter_consensus_whp`**: from 6. If `n = 1` the bound is `≤ 0 ≤ 1`. Otherwise
   `(1 - 1/n)^T ≤ exp(-T/n)` (from `Real.add_one_le_exp`), `exp(-T/n) ≤ exp(-2 log n) = 1/n²`
   by `hT`, and `(n - 1)/n² ≤ 1/n`.

Useful existing API: `Voter.step`, `Voter.round`, `Voter.transition`, `Voter.transition_apply`,
`Voter.survival`, `Dynamics.Kernel.iterate`, `Dynamics.Kernel.iterate_succ`,
`Dynamics.Distribution.{expect, uniform, uniform_expect, independent, independent_expect_prod,
independent_expect_eval, map_expect}`, `Dynamics.{avg, expList, expList_succ, expList_zero,
expList_add, expList_const_mul, expList_le_expList, avg_sum, avg_const}`. Read `voter/Voter/*.lean`
and `dynamics/Dynamics/*.lean` for their exact statements before relying on them.

When all seven theorems are proved, `lake build` succeeds and `check_axioms.py` passes, write a
short final summary (what you proved, any helper lemmas you added, anything noteworthy).
