# MOR-3 (first item): exact fixation on the star (progress)

## Status

Phase 1 (pin the statements): **done** (2026-10-06).
Phase 2 (proofs): **done** (2026-10-06). All 9 pinned theorems are proved, the pinned text is
unchanged (checked against the phase-1 commit), `lake build Moran` is warning-free, and
`#print axioms` (scratch file in `/tmp`, and `python3 ../scripts/check_axioms.py` on
`Audit.lean`) reports only `propext`, `Classical.choice`, `Quot.sound` for every one of them.
No pinned statement turned out to be false.

## Pinned

Definitions (`moran/Moran/StarDefs.lean`):

* `leafMutants c s`: number of mutants other than the centre `c`.
* `starRatio n r = (n + r) / (r (n r + 1))` (the `q` of Broom–Rychtář 2008, §5).
* `starCentreWeight n r = (n r + 1) / (r (n + r))` (`κ = 1/(r² q)`).
* `starPotential c n r s = q ^ leafMutants c s * (if s c then κ else 1)`.

Theorems (`moran/Moran/Star.lean`), all on `starGraph c` (Mathlib) over `V` with
`Fintype.card V = n + 1`, kernel `moranKernel (starGraph c) r hr`:

* `star_potential_invariant` (all `r > 0`): `K.apply Φ s = Φ s`.
* `star_fixation` (`r ≠ 1`): `fixation K s = (1 - Φ s) / (1 - Φ (fun _ => true))`.
* `star_fixation_leaf` (`r ≠ 1`, `v ≠ c`): `(1 - q) / (1 - κ q^n)`.
* `star_fixation_centre` (`r ≠ 1`): `(1 - κ) / (1 - κ q^n)`.
* `star_fixation_uniform` (`r ≠ 1`): `(n (1 - q) + (1 - κ)) / ((n + 1) (1 - κ q^n))`.
* `star_fixation_uniform_sum` (all `r > 0`): Broom–Rychtář's displayed formula
  `(n·nr/(nr+1) + r/(r+n)) / ((n+1)(1 + n/(n+r) ∑_{j ∈ Ico 1 n} q^j))`.
* `star_amplifier` (`n ≥ 2`, `r > 1`): Moran `(1 - 1/r)/(1 - (1/r)^card V)` `<` uniform-start
  fixation.
* `star_amplifier_deleterious` (`n ≥ 2`, `0 < r < 1`): reverse strict inequality.
* `star_fixation_uniform_tendsto` (`r > 1`): on `Fin (n+1)` centred at `0`, uniform-start
  fixation `→ 1 - 1/r^2` as `n → ∞`.

`PINNED.txt` at the repository root lists all 13 declarations.

## Proved

Files (all imported by `Moran.Star`, itself imported by `Moran.lean`):

| File | Lines | Content |
| --- | --- | --- |
| `Moran/StarDefs.lean` | 43 | pinned definitions `leafMutants`, `starRatio`, `starCentreWeight`, `starPotential` |
| `Moran/StarKernel.lean` | 269 | the step on the star; invariance of the potential |
| `Moran/StarAlgebra.lean` | 348 | real-number facts: signs of `q`, `κ`; amplifier inequality; BR sum identity; limit |
| `Moran/StarFixation.lean` | 222 | fixation via `fixation_eq_of_invariant`; single mutants; uniform averaging |
| `Moran/Star.lean` | 148 | the 9 pinned theorems, each a short proof from the helpers |

Main lemmas:

* `StarKernel`: `star_degree_centre`, `star_target_centre_leaf` / `_leaf_centre` /
  `_leaf_leaf`, **`star_sum_pairs`** (a pair sum supported on star edges is
  `∑_ℓ (g c ℓ + g ℓ c)`), `leafMutants_update_centre` / `_gain` / `_loss`,
  `star_balance_leaf` / `_centre` (the two rational identities), **`star_edge_cancel`**,
  **`starPotential_apply`** (invariance).
* `StarFixation`: **`sandwich_of_bounds`** (generic sandwich for `fixation_eq_of_invariant`),
  `fixation_true`, **`star_uniform_expect`**, **`neutral_uniform_fixation`** (any connected graph:
  neutral uniform-start fixation is `1/N`, from `push_fixation`), `starPotential_bounds_of_gt` /
  `_of_lt`, `starPsi_bounds`, **`star_fixation_eq`**, `star_fixation_single_leaf` / `_centre`,
  `star_fixation_uniform_eq`.
* `StarAlgebra`: `starRatio_pos`, `starRatio_le_one`, `one_le_starRatio`,
  `starCentreWeight_lt_one`, `one_lt_starCentreWeight`, `star_denom_ne_zero`,
  **`geom_gap_pos`**, **`star_delta_pos`** (Bernoulli step), **`star_amplifier_sign`**
  (`0 < (1 - 1/r)(ρ_unif - ρ_Moran)`, both amplifier directions at once), `starRatio_ne_one`,
  **`star_closed_eq_sum`**, `star_sum_neutral`, `starRatio_le_inv`, **`star_closed_tendsto`**.

Reusable beyond the star: `star_sum_pairs` (any computation on a star), `sandwich_of_bounds` and
`fixation_true` (any invariant-method fixation proof), `neutral_uniform_fixation` (any connected
graph), `geom_gap_pos` (an elementary polynomial inequality).

Also updated inside `moran/`: `Audit.lean` (9 new `#print axioms` lines; the checker now
reports 19 declarations), `README.md` (results table, provenance note), blueprint
`content.tex` (new section "Exact fixation on the star", 6 entries; all 25 `\lean{}` names
checked to exist).

## Checks done while pinning (outside Lean)

Scripts in `/tmp/mor3-scripts/` (not part of the repo; recreate if needed):

* The closed forms were checked **exactly** (sympy rationals) against the full `2^(n+1)`-state
  chain built literally from `moranKernel` (parent ∝ fitness, offspring to a uniform neighbour)
  for `n = 1..7` and `r ∈ {2, 3/2, 1/3, 7/5, 5/4, 3}`: leaf and centre values agree.
* `starPotential` is exactly invariant under the full kernel, symbolically in `r`, for
  `n = 1..7`, in every configuration.
* Closed form = Broom–Rychtář sum form for `n ∈ {0,1,2,3,7,20}` and several `r`; the sum form
  gives `1/(n+1)` at `r = 1`; the limit `1 - 1/r²` is approached numerically.
* Amplifier inequality: no counterexample for `n = 2..59, 100, 1000, 10^5`, `r` from
  `1 + 10^-11` to `10^29` (and the reverse for `r ∈ (0, 1)`), at 80 digits.

## Plan for phase 2 (proofs) (executed as written, except where noted under Errors)

Helper files `Moran/Star*.lean` imported by `Moran/Star.lean` (definitions stay in
`StarDefs.lean`).

1. **Kernel on the star.** Degrees: `degree_starGraph_center` (`= card V - 1 = n`),
   `degree_starGraph_of_ne_center` (`= 1`). Expand `Kernel.apply` as the sum over pairs
   `(u, w)` (`Distribution.map_expect`, as in `apply_affine` / `push_value_invariant`).
2. **Invariance** (`star_potential_invariant`). Hand computation (verified):
   * centre resident, `i` mutant leaves: a mutant leaf fires onto the centre (total weight
     `r i / F`), `Φ: q^i → κ q^i`; the centre fires onto a mutant leaf (`(1/F)(i/n)`),
     `Φ: q^i → q^(i-1)`; net change `(i q^(i-1)/F) (r q (κ - 1) + (1 - q)/n) = 0` since
     `r q κ = 1/r` and `n + r = q r (n r + 1)`.
   * centre mutant: a resident leaf fires onto the centre (`(n - i)/F`), `κ q^i → q^i`; the
     centre fires onto a resident leaf (`(r/F)(n - i)/n`), `κ q^i → κ q^(i+1)`; net change
     `((n-i) q^i / F)((1 - κ) + r κ (q - 1)/n) = 0` since `κ (n + r) = n + 1/r`.
   * all other pairs leave `s` unchanged. Easiest formalization: per pair `(u, w)`, show
     `Φ (update s w (s u)) - Φ s` and sum, like `push_increment` + `sum_swap_neg` in
     `PushPull.lean`; or pair each edge `{c, ℓ}` in both orientations.
3. **`star_fixation`**: `fixation_eq_of_invariant` with
   `ψ = (1 - Φ) / (1 - Φ full)`; `unfixed_step`, `unfixed_access` (`connected_starGraph c`),
   `allMutant_step` from `Isothermal.lean`. Sandwich: need `0 ≤ ψ ≤ 1` on mixed states, i.e.
   `Φ full ≤ Φ s ≤ 1` (r > 1, `q, κ ∈ (0, 1)`) or reversed (r < 1, `q, κ > 1`). Note
   `Φ full = κ q^n = q^(n-1)/r²`; monotonicity of `Φ` in the mutant set holds since
   `q, κ < 1` (resp. `> 1`) and `κ q ≥ ...`: check `κ ≤ 1` and `q ≤ 1` for `r ≥ 1`
   (`κ ≤ 1 ⟺ nr + 1 ≤ rn + r² ⟺ 1 ≤ r²`; `q ≤ 1 ⟺ n ≤ r² n`).
4. **Leaf / centre / uniform**: evaluate `Φ` on single mutants (`leafMutants` = 1 resp. 0) and
   average: `(uniform V).expect f = avg f` (`uniform_expect`); split `univ` into `c` and the
   `n` leaves.
5. **Sum form**: for `r ≠ 1`, geometric sum `∑_{j ∈ Ico 1 n} q^j = (q - q^n)/(1 - q)`
   (`geom_sum_Ico` / `Finset.geom_sum_Ico_mul`) and algebra (use `1 - q = n(r²-1)/(r(nr+1))`,
   `1 - κ = (r²-1)/(r(n+r))`, `κ q^n = q^(n-1)/r²`). For `r = 1`: `push_fixation`
   (`PushPull.lean`) with `pushValue` = `∑_{mutants} 1/deg`; both sides equal `1/(n+1)`.
6. **Amplifier** (elementary; derived by hand). Put `s = 1/r`, `t = (1 + n s)/(n + s)`, so
   `q = s t`. Let `A = n²/(n+s) + 1/(1+ns)` so that `ρ_unif = (1 - s²) A / ((n+1) D)` with
   `D = 1 - s² q^(n-1) = 1 - κ q^n`, and `ρ_M = (1 - s)/(1 - s^(n+1))`.
   `ρ_unif > ρ_M` (r > 1) and `ρ_unif < ρ_M` (r < 1) both reduce (signs of `1-s`, `D`,
   `1-s^(n+1)` flip together) to `B (1 - s^(n+1)) > 1 - s² q^(n-1)` with
   `B = (1+s)A/(n+1) = 1 + s²(n-1)²/((n+s)(1+ns))`, i.e. to
   `(n-1)²(1 - s^(n+1)) / ((n+s)(1+ns)) > s^(n-1) (1 - t^(n-1))` (divide by `s²`).
   Using `1 - t = (n-1)(1-s)/(n+s)` and Bernoulli (`1 - t^(n-1) ≤ (n-1)(1-t)` for `t ≤ 1`,
   resp. `t^(n-1) - 1 ≥ (n-1)(t-1)` for `t ≥ 1`), it suffices that
   `∑_{k=0}^n s^k > s^(n-1) + n s^n` for `s < 1` (resp. `<` for `s > 1`), true termwise since
   `n ≥ 2` gives at least one term `s^k`, `k ≤ n - 2`.
7. **Limit**: closed form with `q_n → 1/r²`, `κ_n → 1`, `q_n^n → 0` (eventually
   `q_n ≤ (1 + 1/r²)/2 < 1`).
8. **Audit / docs** (after the proofs): add the 9 theorems to `moran/Audit.lean` (not done in
   phase 1: `scripts/check_axioms.py` would reject `sorryAx`), and update `moran/README.md`,
   the blueprint and ROADMAP row MOR-3.

## Errors

None outstanding. Issues met and fixed during phase 2 (for the record):

* `rw [← hl]` in the equal-type cases of `star_edge_cancel` also rewrote the other `false`;
  fixed with per-update helper equations.
* `nlinarith` needed the product hint `n (r - 1)(r + 1) ≥ 0` for `q ≤ 1`.
* `field_simp` could not see that `q - 1 ≠ 0` in the Broom–Rychtář identity; fixed by
  rewriting `q - 1 = -(n (r² - 1))/(r (n r + 1))` first.
* The sign facts on `q`, `κ` were moved from `StarFixation` to `StarAlgebra` so that the latter
  depends only on `StarDefs`.

Not done (outside `moran/`, which phase 2 may not touch): ROADMAP row MOR-3 still says "open";
it should record that its first item (exact fixation on the star) is done.

## Deviations from the paper

* **Graph encoding.** The star is Mathlib's `starGraph c` on any finite type `V` with
  `Fintype.card V = n + 1` (any labelling), instead of vertices `0, …, n` with centre `0`
  (Broom–Rychtář 2008, §5). Only the limit theorem fixes `V = Fin (n + 1)`, centre `0`.
* **Fixation probability** is the supremum of the finite-time fixation probabilities
  (`fixation`, as in MOR-1/MOR-2), not the absorption probability of a path-space measure; the
  same in the finite setting.
* **Closed form instead of the geometric sum.** Broom–Rychtář give
  `P_1 = 1 / (1 + n/(n+r) ∑_{j=1}^{n-1} q^j)` (centre mutant, one mutant leaf) and the average
  `φ`; we sum the geometric series: `ρ_leaf = (1 - q)/(1 - κ q^n)`,
  `ρ_centre = (1 - κ)/(1 - κ q^n)`. Their displayed `φ` is also pinned verbatim
  (`star_fixation_uniform_sum`, with `∑_{j=1}^{n-1}` written `∑ j ∈ Ico 1 n`). Their notation
  `P⁰ᵢ` denotes a *mutant* centre (from their (5.1) and boundary conditions).
* **`r ≠ 1`** in the closed forms (they are `0/0` at `r = 1`). The neutral case is covered by
  `star_fixation_uniform_sum` (valid for all `r > 0`) and by VOT-4's `push_fixation`.
* **General configurations** (`star_fixation`) and the **potential invariance**
  (`star_potential_invariant`) are not stated in the sources: they are our invariant-based
  characterization (the method of MOR-2), from which the single-mutant formulas follow.
* **Amplifier for all `n ≥ 2`.** Lieberman–Hauert–Nowak assert amplification for large stars
  and Broom–Rychtář observe numerically that average fixation is always increased for
  `r > 1`; we state it for every `n ≥ 2` and every `r > 1` (we have an elementary proof, plan
  item 6). `n ∈ {0, 1}` is excluded: then the star is complete (`K_1`, `K_2`) and equality
  holds. Following LHN's definition of an amplifier (advantageous mutants favoured,
  disadvantageous ones disfavoured), we also pin the reverse inequality for `r < 1`
  (`star_amplifier_deleterious`). Moran's formula is written explicitly,
  `(1 - 1/r)/(1 - (1/r)^N)` with `N = Fintype.card V`, as in `isothermal`.
* **Large-`n` behaviour.** LHN's `(1 - 1/r²)/(1 - 1/r^(2N))` is an approximation, not an
  identity; we pin its exact content as a limit, `1 - 1/r²` as `n → ∞`, for `r > 1`.

## Build

Phase 2 (2026-10-06): `lake build Moran` in `moran/`: `Build completed successfully`, no
warnings. Phase 1: `StarDefs` had no warnings, `Star` had 9 `sorry` warnings (one per theorem). Elaborated statements were printed
(`#check`, `pp.coercions`) and checked: casts are `(↑n + r)`, `(↑n + 1)`; concrete values
`starPotential (0 : Fin 3) 2 2` are `2/5` (one mutant leaf) and `1/10` (all mutant), giving
`ρ_leaf = 2/3`, the exact chain value.
