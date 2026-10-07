# PROGRESS — EPI-3: supercritical giant component (Krivelevich–Sudakov DFS)

Source: M. Krivelevich, B. Sudakov, *The phase transition in random graphs: a simple proof*,
Random Structures & Algorithms 43 (2013) 131–138, arXiv:1201.6529 (v4 read in full).
Numbering used below is the arXiv v4 one: Lemma 1 (parts 1, 2), Theorem 1 (parts 1, 2),
Discussion items 1–8, Theorem 2 (Discussion item 3).

Branch `epi3-giant`; only `epidemics/` (plus `PINNED.txt` at the repo root, phase 1) changes.

## Status

* **Phase 1 (pin the statements): done.**
* **Phase 2 (proofs): done.** No `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/
  `extern`/`set_option` anywhere in `epidemics/`. `lake build Epidemics` is warning-free. The
  pinned text (docstring through `:=`) of all 11 `PINNED.txt` entries is byte-identical to the
  phase-1 commit `31d0cf9`. `#print axioms` of the five pinned theorems:
  `[propext, Classical.choice, Quot.sound]`. `python3 ../scripts/check_axioms.py` passes
  (14 declarations, including the 5 pinned theorems, are in `Audit.lean`).
* No pinned statement turned out to be false.

## Pinned (see `PINNED.txt`)

| Declaration | File | Content |
| --- | --- | --- |
| `exists_long_path` | `Epidemics/Giant.lean` | K–S Theorem 1(2): `∃ ε₀ > 0, ∀ ε ∈ (0, ε₀], ∃ C, ∀ V p, p n = 1 + ε →` `P(perc ⊤ ω has a path with ≥ ε² n / 5 edges) ≥ 1 - C / n` |
| `exists_giant_component` | `Epidemics/Giant.lean` | K–S Theorem 2: same quantifiers, `P(∃ component with ≥ ε n / 2 vertices) ≥ 1 - C / n` |
| `exists_linear_component` | `Epidemics/Giant.lean` | Erdős–Rényi (K–S abstract), every `ε > 0`: `∃ c > 0, ∃ C, P(∃ component ≥ c n) ≥ 1 - C / n` |
| `reedFrost_large_outbreak_explicit` | `Epidemics/GiantEpidemic.lean` | `∃ ε₀ > 0, ∀ ε ∈ (0, ε₀], ∃ C, ∀ V p v`: Reed–Frost on `K_n`, `p n = 1 + ε`, from `{v}`: `P(final size ≥ ε n / 2) ≥ ε / 2 - C / n` |
| `reedFrost_large_outbreak` | `Epidemics/GiantEpidemic.lean` | `∀ R₀ > 1, ∃ c > 0, ∃ q > 0, ∃ n₀, ∀ V (n ≥ n₀) p v, p n = R₀ →` `P(final size from {v} ≥ c n) ≥ q` |

Also pinned (EPI-1 definitions that the statements depend on): `perc`, `SIR`, `step`, `run`,
`bernoulli`, `coins` in `Epidemics/ReedFrost.lean` (unchanged).

Constants obtained: Theorem 1(2) with `ε₀ = 1/100`; Theorem 2 and the explicit epidemic statement
with `ε₀ = 1/10`; `C` explicit in the proofs (`core_path`, `core_component`), of order
`n₁ + e^{δ²/3} / (δ² η λ)³`.

## Files (phase 2), lines / declarations

| File | Lines | Decls | Content |
| --- | --- | --- | --- |
| `GiantCoins.lean` | 310 | 20 | `prob_*` basics (`prob_mono`, `prob_congr`, `prob_not`, `prob_or_le`, `prob_exists_le_sum`, `one_sub_le_prob`); cylinders `prob_forall_eval_eq`; **deferred decisions** `queryAnswers`, `FreshUpTo`, `queryAnswers_eq_iff`, `prob_queryAnswers_eq`, `expect_queryAnswers`, `prob_queryAnswers`; symmetry `permSym2`, `coins_prob_perm` |
| `GiantDFS.lean` | 1264 | 103 | the search (`State`, `pending`, `move`, `answer`, `settle`, `ofAnswers`, `nextQuery`); invariant `State.Inv` (16 clauses) and its preservation; frame/monotonicity (`State.Le`); termination `move_settle`; epochs per settle (`epochs_settle_le`, `comp_settle_of_epochs_eq`, `comp_settle_of_lt`); counting (`card_queried_found`, `card_found_le`); exported properties (`fresh_nextQuery`, `mem_found_iff_of_queryAnswers`, `queried_of_mem_done_of_mem_unvisited`, `stack_chain_ofAnswers`, `length_stack_le`, `count_true_add_epochs`, `card_union_append_le`, `count_drop_le_card_comp`, `exists_of_epochs_lt`, …) |
| `GiantAnalysis.lean` | 362 | 17 | deterministic analysis: `card_mul_card_le` (`|A||B| ≤ #queries`), `three_mul_explored_lt` ("`|S| < n/3` at `N₀`", first-time argument), `le_length_stack` (long stack, concavity), `exists_epoch_start`, `le_card_comp` (large epoch), `exists_path_of_stack`, `card_comp_le_ncard` |
| `GiantProb.lean` | 159 | 8 | `count_take_ofFn`, window tails `prob_count_take_le/ge`, **Lemma 1(2)** `prob_count_take_far`, `Good`, `prob_not_good_le`, `pow_three_mul_exp_neg_le` |
| `Giant.lean` | 600 | 15 | `tail_le_div`; the paper's inequalities for large `n` (`ineq_explored`, `ineq_contr`, `ineq_count`, `ineq_mean_lo`, `ineq_path_lo/one/two`); `exists_component_of_good`, `exists_path_of_typical`; parametric cores `core_component`, `core_path`; the 3 pinned graph theorems |
| `GiantEpidemic.lean` | 197 | 7 | `card_final_recovered`, `percPermIso`, `ncard_supp_perm`, `prob_component_ge_eq`, `prob_component_ge`; the 2 pinned epidemic theorems |

Also updated: `Epidemics.lean` (imports), `Audit.lean` (7 new `#print axioms`), `README.md`
(EPI-3 section), `blueprint/src/content.tex` (EPI-3 section; all 69 `\lean{}` names checked to
exist).

## Proof architecture (as implemented)

1. **Coins.** `coins p = independent (fun _ => Distribution.bernoulli p)` by `rfl`
   (`coins_eq_independent`), so FND-3's Chernoff bounds apply. Deferred decisions: the event
   "answers = `L`" is the cylinder `∀ k, ω (next (L.take k)) = L[k]` on distinct coordinates.
2. **DFS fed with answers** (`ofAnswers V l`), with the completion phase so that the strategy is
   fresh for all `n(n-1)/2` pairs; on `ω` the answers are `queryAnswers (nextQuery e₀) ω t` and
   the found pairs are open edges of `perc ⊤ ω`.
3. **Parametric cores.** `core_component (λ θ η δ c)`: `N₀ = ⌊θ n²⌋` queries, window
   `t₁ = ⌊η n²⌋`, typical event `Good` (counts at `N₀`, `t₁` at most `(1+δ)` times the mean, and at
   least `(1-δ)` times the mean at every `t ∈ [t₁, N₀]`); conditions
   `θ < (2/3)(1/3 - (1+δ)λθ)`, `(1-δ)λ(1-λθ) > 1`, `c < ((1-δ)θ - (1+δ)η)λ`.
   `core_path (λ θ δ ℓ)`: conditions `θ < (2/3)(1/3 - (1+δ)λθ)`,
   `θ < ((1-δ)λθ - ℓ)(1 - (1-δ)λθ)`, `θ < (2/3)(1/3 - ℓ)`.
   Small `n` (below an explicit `n₁`) is absorbed in `C`; the failure probability
   `(N₀+3) e^{-δ² t₁ p/3}` is turned into `C/n` with `x³ e^{-κx} ≤ 6/κ³`.
4. **Parameters.** Thm 1(2): `λ = 1+ε, θ = ε/2, δ = ε/20, ℓ = ε²/5`, `ε ≤ 1/100`.
   Thm 2: `θ = ε/2, δ = ε/10, η = ε²/10, c = ε/2`, `ε ≤ 1/10`. Every `ε > 0`:
   `δ = ε/(2(1+ε)), θ = ε/(10(1+ε)²), η = θ/4, c = ((1-δ)θ - (1+δ)η)λ/2`.
5. **Epidemic.** Final outbreak from `{v}` = component of `v` (EPI-1 `final_recovered_iff`);
   symmetry of `K_n` (`coins_prob_perm` + graph isomorphism) gives
   `P(|C(v)| ≥ k) ≥ (k/n) P(∃ component ≥ k)`.

## Changes to unpinned phase-1 helpers

* `DFS.State` gained a field `pushes` (vertices pushed by positive answers).
* `DFS.card_done_append_le` (`|S|` grows by `≤ |U| + 2` per query) was replaced by
  `DFS.card_union_append_le` (`|S ∪ U|` grows by `≤ 2` per query) and `DFS.card_union_nil_le`,
  which is what the first-time argument needs.
* `coins_prob_mono` (monotone coupling) was dropped: the every-`ε` theorem is obtained from the
  parametric core with `θ` small instead (the DFS argument works for every `λ > 1`).
* `prob_count_take_far` moved from `Giant.lean` to `GiantProb.lean`.

## Errors / open issues

None. Notes for maintainers: the heartbeat budget is per declaration, so the cores are split into
small lemmas (`exists_component_of_good`, `exists_path_of_typical`, `ineq_*`); floors are
introduced through `obtain` (opaque naturals) to avoid expensive unfolding.

## Remaining (outside `epidemics/`, not allowed in this job)

`PROVENANCE.md` entry and `ROADMAP.md` status for EPI-3 (repository root).

## Deviations from the paper

1. **Finite, quantitative "whp".** The paper's "with high probability" (probability → 1) is stated
   as "probability at least `1 - C / n`" with `∃ C` depending on `ε` (the rate requested for this
   job). The proofs actually give exponentially small failure probabilities (paper's Discussion,
   item 1), turned into `C / n`.
2. **"`ε > 0` a small enough constant"** is `∃ ε₀ > 0, ∀ ε ∈ (0, ε₀]`, with `C` chosen after `ε`;
   the proofs take `ε₀ = 1/100` (Theorem 1(2)) and `ε₀ = 1/10` (Theorem 2).
3. **`G(n, p)` as bond percolation on `K_n`**: `perc ⊤ ω`, `ω ~ coins p`, one coin per element of
   `Sym2 V` (the diagonal coins are ignored since `⊤` has no loops); the vertex set is any finite
   type `V` with `n = |V|` rather than `[n]`.
4. **`p = (1 + ε)/n` is written `p * n = 1 + ε`** (with `0 ≤ p ≤ 1` as hypotheses, required by
   `coins`). Equivalent for `n ≥ 1`; it excludes `n = 0`, where Lean's `C / 0 = 0` would make
   `1 - C / n ≤ P(…)` false for the empty graph. `p ≤ 1` forces `n ≥ 1 + ε`.
5. **Path length in edges.** Theorem 1(2) is pinned and proved as "a path (`Walk.IsPath`) with
   `Walk.length ≥ ε² n / 5` edges"; the proof shows `|U| ≥ ε² n / 5 + 1` vertices (slightly
   stronger than the paper's `|U| ≥ ε² n / 5`), using the slack of the paper's final inequality.
6. **Lemma 1(2) by Chernoff (FND-3) instead of Chebyshev**, with a relative deviation `δ N₀ p`
   instead of `n^{2/3}` (paper's Discussion, item 1).
7. **Theorem 2's windows.** The paper uses `t ∈ [n^{7/4}, N₀]` with deviations `n^{2/3}`, `n^{5/6}`;
   the formalization uses `t ∈ [⌊η n²⌋, N₀]` with relative deviations `δ t p` (union bound over
   `≤ N₀ + 1` times, each exponentially small in `n`). The contradiction "an epoch starting at
   time `τ` in the window" is the paper's `t ≥ |S|(n - |S|)` computation.
8. **"`|S| < n/3` at time `N₀`"**: the paper looks at the moment when `|S| = n/3` exactly; with
   queries as time steps `S` can jump, so the formal argument takes the first query time at which
   `3 |S ∪ U| ≥ n` (`|S ∪ U|` grows by at most `2` per query) and concludes `3 |S ∪ U| < n` at `N₀`.
9. **Floors and ceilings**, omitted in the paper, are explicit (`N₀ = ⌊θ n²⌋`, `t₁ = ⌊η n²⌋`).
10. **DFS details.** (a) The fixed order `σ` is replaced by an arbitrary deterministic choice
    (`DFS.pick`, `Classical.choose`); the analysis never uses `σ`. (b) The coupling goes the other
    way: the coins on the pairs come first and the search reads them adaptively; the paper's
    "fed with i.i.d. `X̄`, the graph is distributed as `G(n, p)`" becomes the principle of deferred
    decisions (`prob_queryAnswers`). (c) Each query is one step of `ofAnswers`; moves without query
    are grouped by `settle`. (d) The completion phase is kept, so the strategy is fresh for all
    `n(n-1)/2` pairs.
11. **Statements added beyond the paper.** `exists_linear_component` covers every `ε > 0` (the paper
    proves only small `ε`); it is obtained by the same DFS argument with `N₀ = ⌊θ n²⌋`, `θ` small in
    terms of `ε`. The epidemic corollaries are the roadmap's reading via EPI-1; `R₀ = p n` as in the
    roadmap (the mean number of secondary infections caused by the first case is `p (n - 1)`). The
    explicit form follows from Theorem 2 by vertex symmetry of `K_n` (`prob_component_ge`).
12. **Not formalized**: Theorem 1(1) and Lemma 1(1) (subcritical; roadmap EPI-2), Theorems 3–6
    (digraphs, minimum-degree hosts, pseudo-random hosts, Maker–Breaker).
