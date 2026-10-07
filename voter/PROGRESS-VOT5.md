# PROGRESS: VOT-5, consensus time of the lazy voter via conductance

Job: roadmap row VOT-5. Source: Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on
the voter model in dynamic networks*, ICALP 2016, arXiv:1603.01895 (BGKM16), read from the arXiv
LaTeX source (`VoterModel.tex`, v of 2016-05-30). Numbering (shared counter per section):
Theorem 1.1 = upper bound (`thm:voter`), Lemma 2.1 = `lem:technical-st` (potential drop),
Lemma 2.2 = `lem:two-op-const-prob` (drift ⟹ time, already FND-5's `drift_absorption`),
Lemma 2.3 = `fraction` (κ-opinion phases), Lemma 2.4 = `lem:forsecondpart` (`n log n / φ²`, not
in scope).

## Status

* **Phase 1 (pin statements): done.** 14 pinned declarations (8 theorems, 6 definitions) in
  `PINNED.txt` at the repo root. `lake build Voter` succeeds; the only warnings are the 8
  `declaration uses 'sorry'`.
* **Phase 2 (proofs): done** (2026-10-07). Every `sorry` is replaced; no pinned statement was
  false. `lake build Voter` is warning-free (each `Conductance*.lean` also recompiled alone
  with no message). The pinned text (docstring + declaration up to `:=`) is byte-identical to
  the phase-1 commit `a6c99e9` (`/tmp/vot5-scratch/cmp_pinned.py`). All pinned theorems and
  the main helpers depend only on `propext`, `Classical.choice`, `Quot.sound`
  (`/tmp/vot5-scratch/Axioms.lean`; `Audit.lean` extended by the 8 pinned theorems,
  `python3 ../scripts/check_axioms.py`: 36 declarations, only standard axioms). No
  `sorry`/`admit`/`axiom`/`native_decide`/`set_option` in the VOT-5 files.

## Pinned (frozen up to `:=`), namespace `Voter`

`voter/Voter/Conductance.lean` (definitions; imports `Voter.Lazy`, `Voter.Coalescence`,
`Mathlib.Combinatorics.SimpleGraph.Density`)
* `vol G S : ℕ := ∑ u ∈ S, G.degree u`.
* `conductance G : ℝ := ⨅ U : {U : Finset V // 0 < vol G U ∧ vol G U ≤ #E}, #(G.interedges U Uᶜ) / vol G U`
  (Mathlib's `SimpleGraph.interedges`; `0` if the index is empty, `Real.iInf_of_isEmpty`).
* `discordant G s u : ℕ` = `λ_u` = #neighbours of `u` with an opinion `≠ s u` (any colour type
  with `DecidableEq`).
* `minority G s : Finset V` (Bool configurations): the `false` class if
  `vol(false class) ≤ vol(true class)`, else the `true` class (paper: `s_t = v^(0)` on ties).
* `potential G s : ℝ := √(vol G (minority G s))` = `Ψ(s_t)`.
* `dynamicLazy G hd t : Kernel (Config V C) := fun x => transition (lazyNeighbor (G t x) (hd t x)) x`
  for `G : ℕ → Config V C → SimpleGraph V` (adaptive adversary seeing the current configuration).

`voter/Voter/ConductanceDrift.lean`
* `potential_drift` (**Lemma 2.1**, corrected, see Deviations): `hd`, `(minority G s).Nonempty` ⟹
  `(transition (lazyNeighbor G hd)).apply (potential G) s ≤
   potential G s - (∑ u ∈ minority G s, λ_u * d_u) / (32 * potential G s ^ 3)`.
* `potential_drift_conductance` (display at the start of the proof of Lemma 2.2): same
  hypotheses ⟹ `… ≤ potential G s - G.minDegree * conductance G / (32 * potential G s)`.

`voter/Voter/ConductanceTime.lean` (imports `Dynamics.Drift`)
* `lazy_consensus_of_minority` (**Lemma 2.2, static**): `hd`,
  `128 * vol G (minority G s) ≤ G.minDegree * conductance G * T` ⟹
  `(transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / 2`.
* `lazy_consensus_conductance` (**Theorem 1.1 (i), static, κ = 2**): `hd`,
  `128 * #E ≤ G.minDegree * conductance G * T` ⟹ same conclusion.
* `lazy_expected_consensus_time` (restarting): `hd`, `128 * #E ≤ d_min φ T₀` ⟹ `∀ N,
  ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s ≤ 2 * T₀`.
* `dynamic_consensus_conductance` (**Lemma 2.2, dynamic graphs, κ = 2**): `G : ℕ → Config V Bool →
  SimpleGraph V`, `hd : ∀ t x v, 0 < (G t x).degree v`, `hdeg : ∀ t x v, (G t x).degree v =
  (G 0 s).degree v`, `hφ : ∀ t x, φ t ≤ conductance (G t x)`,
  `128 * vol (G 0 s) (minority (G 0 s) s) ≤ (G 0 s).minDegree * ∑ t ∈ range T, φ t` ⟹
  `Kernel.iterateSeq (dynamicLazy G hd) T disagreement s ≤ 1 / 2`.

`voter/Voter/ConductanceMany.lean` (κ opinions, any finite colour type, `[Nonempty V]`)
* `lazy_expected_consensus_time_many`: `∃ b, ∀ V C … G hd s T₀, b * #E ≤ d_min φ T₀ → ∀ N,
  ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s ≤ T₀`.
* `lazy_consensus_conductance_many` (**Theorem 1.1 (i), static, any κ**): `∃ b, ∀ V C … G hd s T,
  b * #E ≤ d_min φ T → (transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / 2`.

Existing (not new) definitions used by the statements: `lazyNeighbor` (VOT-2, `(I + D⁻¹A)/2`),
`transition`, `disagreement` (VOT-3, `0` at consensus, `1` otherwise), `Kernel.iterate`,
`Kernel.iterateSeq` (FND-5), Mathlib `SimpleGraph.minDegree`, `SimpleGraph.interedges`.

## Proved (phase 2): files and proof structure

All 8 pinned theorems. Constants obtained: `b = 7000` (expectation, κ opinions) and
`b = 14000` (probability `1/2`, κ opinions); two opinions use the explicit `128`.

| File | Lines | Content |
| --- | --- | --- |
| `Conductance.lean` | 78 | pinned definitions (unchanged) |
| `ConductanceIndep.lean` | 283 | independent coordinates: `independent_expect_update` (resampling), `independent_expect_mul_of_update`, `independent_expect_sum_sq`, `independent_expect_sum_cube`, `independent_expect_comp_sum_le` (Lemma A.1), two-point moments `expect_ite_eq`, `expect_bernoulli_sq`, `expect_bernoulli_cube` |
| `ConductanceBasic.lean` | 354 | `vol_univ`, `vol_pos`, `exists_minority_eq`, `vol_minority_le(_edges)`, `minority_eq_empty_iff`, `potential_eq_zero_iff`, `disagreement_eq_potential`, `potential_congr`, `minDegree_congr`, cut counting (`card_interedges_class(_compl)`), `conductance_mul_vol_le`, `conductance_nonneg`, `conductance_le_one`, `lazyNeighbor_expect(_ne_self/_discordant)`, `sqrt_add_le_taylor` (`(t-r)⁴(t²+4tr+5r²) ≥ 0`), `sqrt_chord` |
| `ConductanceDriftAux.lean` | 338 | Lemma 2.1 ingredients: `vol_class_step`, `expect_sqrt_le_comp` (replacement `X → Y`), `sum_mean_compVar` (cut symmetry), `expect_compSum_sq_ge`, `expect_compSum_cube_le`, `expect_taylor`, `drift_arith` |
| `ConductanceDrift.lean` | 101 | `potential_drift`, `potential_drift_conductance` |
| `ConductanceLevels.lean` | 157 | `sum_iterate_le_of_block` (expected time in a part of a non-re-enterable set), `iterate_finset_sum`, `transition_iterate_constant`, `transition_disagreement_le` |
| `ConductanceTime.lean` | 158 | Lemma 2.2 via `Kernel.drift_absorption` / `drift_absorption_seq`, restart via `sum_iterate_le_of_block` |
| `ConductanceManyAux.lean` | 341 | `iterate_le_of_closed` (comparison on a support-closed set), `opinions`, `disagreement_eq_opinions`, `card_big_le`, `half_le_iterate_resolved` (projection by `iterate_project` + Lemma 2.2), `phase_count`, `phase_step` (Lemma 2.3) |
| `ConductanceManyTime.lean` | 330 | `phaseThreshold` `θ_j = n(5/6)^j`, `sum_inv_phaseThreshold_le` (`∑ 1/θ_j ≤ 3`), `levels_le`, `levelInd`/`aboveInd`, `level_time_le`, `disagreement_le_sum_levelInd`, `expected_time_many_bound` (`6930 m/(d_min φ)`) |
| `ConductanceMany.lean` | 77 | the two κ-opinion theorems (Markov + antitonicity for the `1/2` form) |

Proofs follow the plan below, with two simplifications: the replacement lemma and the moments
use one resampling identity (reindexing `(x, a) ↦ (x[i ↦ a], x i)`), and the κ-opinion phase
argument uses the occupation-time lemma `sum_iterate_le_of_block` per level instead of
expected numbers of phases.

Docs updated in `voter/`: README table (4 VOT-5 rows), blueprint section "Consensus time via
conductance (VOT-5)" (28 `\lean{}` names, all resolve), `Audit.lean` (+8).

## Phase-1 checks

* Elaborated types inspected (`#check`, `/tmp/vot5-scratch/Check.lean`): casts are where
  intended (`128 * ↑(vol …) ≤ ↑G.minDegree * conductance G * ↑T`).
* Non-degeneracy, proved in the scratch file without `sorry`: `conductance ⊤ = 1` on `Fin 2`
  (so the time hypotheses are satisfiable: `K₂`, `T ≥ 128`); on `K₃`, `vol univ = 6`,
  `minority ![true, false, true] = {1}`, `discordant … 1 = 2`, `potential … = √2`.
* Exact numerics (`/tmp/vot5-check/*.py`, plain Python, product of independent flips with
  `P(u flips) = λ_u / (2 d_u)`):
  * corrected Lemma 2.1 holds for every two-opinion configuration of 14 graphs with ≤ 8
    vertices (stars, paths, cycles, `K₄`, `K₃,₃`, lollipop, barbell, random), also with the
    other side on volume ties;
  * the **printed Lemma 2.1 is false** on the star `K_{1,k}`, `k ≥ 15`, minority = one leaf
    (`Ψ = 1`): exactly, `𝔼[Ψ'] = ½(1 - 1/(2k)) + (√(k-1) + √k)/(4k)` (only the leaf and the hub
    can flip), e.g. `k = 15`: `𝔼[Ψ'] = 0.6102 > 1 - (1 + 15)/32 = 0.5`; `k = 40`: `0.5723` vs.
    `-0.2812`. The corrected bound `1 - 1/32` holds;
  * conductance form of the drift and the two-opinion time bound hold on `C₆`, `P₆`, star,
    `K₃,₃`, barbell (worst-case `P(no consensus at ⌈128 m/(d_min φ)⌉) ≤ 10⁻⁴²`; the true
    worst-case median times are 4–20 rounds, so the constant is very loose).

## Remaining

* Nothing for VOT-5 inside `voter/`. (`FORMALIZATION_DIFFERENCES.md` compares Hassin–Peleg
  only and was left untouched; the BGKM16 deviations are recorded here and in the blueprint.)
* Outside `voter/` (not editable here): mark ROADMAP row VOT-5 done; add a `PROVENANCE.md` row
  (BGKM16 Lemmas 2.1–2.3, Theorem 1.1 (i); corrected Lemma 2.1; constants 128 / 7000 / 14000;
  proofs by Claude under the pinned-statement protocol).
* Optional: move the reusable helpers listed below to `dynamics/`; the alternative bound
  `n log n / φ²` (Lemma 2.4, `multiplicative_drift` is already in FND-5) and κ opinions on
  dynamic graphs were not in scope.

## Errors

None open. Phase-2 hiccups (all fixed): `ring` failing on `if`s whose decidability instances
differed up to unfolding `step` (fixed by `split_ifs`); `exact_mod_cast` not seeing through
`set` abbreviations; `Σ` is reserved syntax; unused-section-variable linter warnings (fixed with
`omit … in`).

## Plan (phase 2)

Helper files (names suggested): `ConductanceBasic.lean`, `ConductanceIndep.lean`,
`ConductanceTaylor.lean`, `ConductanceLevels.lean`.

1. **Basic facts** (`ConductanceBasic.lean`). `vol_univ : vol G univ = 2 #E`
   (`sum_degrees_eq_twice_card_edges`); `vol` of the two classes adds up to `vol univ`;
   `minority G s` is one of the two classes and `vol G (minority G s) = min …`, hence
   `≤ #E`; under `hd`, `vol S = 0 ↔ S = ∅`; `minority G s = ∅ ↔ ∃ c, s = fun _ => c`;
   `potential_nonneg`, `potential G s = 0 ↔ consensus`, so
   `disagreement s = if potential G s = 0 then 0 else 1`; for a colour class `S`,
   `#(G.interedges S Sᶜ) = ∑ u ∈ S, discordant G s u` and also `= ∑ u ∈ Sᶜ, discordant G s u`
   (`SimpleGraph.card_interedges_comm` style double counting); `conductance_nonneg`,
   `conductance_le_one` (`cut ≤ vol`), `conductance_mul_vol_le : 0 < vol U → vol U ≤ #E →
   φ * vol U ≤ #(interedges U Uᶜ)` (`ciInf_le`, `Set.finite_range … |>.bddBelow`);
   `vol`, `minority`, `potential`, `minDegree` depend on `G` only through the degrees.
2. **Independence** (`ConductanceIndep.lean`, candidates for `dynamics/`): resampling one
   coordinate of `Distribution.independent p`:
   `(independent p).expect F = (independent p).expect (fun x => (p i).expect (fun a =>
   F (Function.update x i a)))`; consequences: factorization `E[A · g(x i)] = E[A] E[g]` when
   `A` ignores coordinate `i`, and for `Z = ∑ i, Z_i (x i)` with `E Z_i = 0`:
   `E[Z²] = ∑ E[Z_i²]`, `E[Z³] = ∑ E[Z_i³]` (induction over a `Finset` of coordinates, or
   `Distribution.independent_expect_prod` term by term).
3. **Lemma 2.1** (`potential_drift`). Let `S = minority G s` = class of opinion `b`, `P = vol S > 0`.
   (a) `potential G t ≤ √(vol of the b-class of t)` for every `t` (min ≤ either side).
   (b) `transition_apply`, `round`: `𝔼 = (independent H).expect (fun r => …(step s r))`, new
   opinion of `u` is `s (r u)`; `vol(b-class of step s r) = P + ∑ u, X_u (r u)` with
   `X_u w = d_u (1[s w = b] - 1[s u = b])`.
   (c) Replacement (BGKM16 Lemma A.1 `lem:replaceRV`, whose printed proof drops a factor `1/2`
   that cancels): for `u ∉ S` replace `X_u` by `Y_u w = λ_u 1[w ≠ u]` (note `H u u = 1/2`
   exactly, no self-loops in a `SimpleGraph`), one coordinate at a time with the resampling
   identity; the one-coordinate step is
   `½√z + (1/(2d))(λ√(z+d) + (d-λ)√z) ≤ ½√z + ½√(z+λ)` for `z ≥ 0`, `0 ≤ λ ≤ d`
   (concavity of `√`); all partial sums stay `≥ P - ∑_{v∈S} d_v = 0`.
   (d) Taylor: for `a > 0`, `a + x ≥ 0`:
   `√(a + x) ≤ √a (1 + x/(2a) - x²/(8a²) + x³/(16a³))`. Proof: `y = √(1 + x/a) ≥ 0`,
   `16 (1 + x/2 - x²/8 + x³/16 - y) = y⁶ - 5y⁴ + 15y² - 16y + 5 = (y - 1)⁴ (y² + 4y + 5)`
   (checked by hand and numerically), `(y+2)² + 1 > 0`.
   (e) Moments of `Δ' = ∑ u, Y_u (r u)` (`Y_u = X_u` on `S`): `E Δ' = ∑_{u∉S} λ_u/2 - ∑_{u∈S}
   λ_u/2 = 0` (both sums count the cut); `E Δ'² = ∑ Var Y_u ≥ ∑_{u∈S} (λ_u d_u/2 - λ_u²/4) ≥
   ∑_{u∈S} λ_u d_u / 4`; `E Δ'³ = ∑ (third central moments) ≤ 0` (`u ∉ S`: symmetric two-point,
   `0`; `u ∈ S`: `-d³ p(1-p)(1-2p)` with `p = λ/(2d) ≤ 1/2`).
   (f) Assemble: `𝔼Ψ' ≤ √P (1 + 0 - E Δ'²/(8P²) + E Δ'³/(16P³)) ≤ √P - ∑_{S} λd / (32 P^{3/2})`.
4. **`potential_drift_conductance`**: `∑_{u∈S} λ_u d_u ≥ d_min ∑_{u∈S} λ_u = d_min #cut(S) ≥
   d_min φ vol S = d_min φ Ψ²` (using `0 < vol S ≤ #E`), divide by `32 Ψ³`.
5. **`lazy_consensus_of_minority`**: `Kernel.drift_absorption` with `Ψ = potential G`,
   `c = d_min φ / 32 ≥ 0`; `habs` from `transition_constant` (`Ψ = 0` ⟹ consensus ⟹ fixed);
   `4 Ψ(s)² = 4 vol(s_0) ≤ c T`; conclude with `disagreement = 1 - 1[Ψ = 0]`
   (`Kernel.iterate_add`/`iterate_const`, or `iterateSeq_one_sub`).
   **`lazy_consensus_conductance`**: `vol(minority) ≤ #E`.
6. **`lazy_expected_consensus_time`**: for every state `x`,
   `iterate T₀ disagreement x ≤ ½ disagreement x` (consensus states: `0`; others: step 5);
   `Kernel.geometric_blocks` (dynamics `Absorption.lean`) gives `iterate (k T₀) ≤ 2^{-k}`;
   `Kernel.iterate_antitone` (`K disagreement ≤ disagreement`) bounds each block of `T₀` terms;
   `∑_k T₀ 2^{-k} ≤ 2 T₀`. (`T₀ = 0` forces `#E = 0`, so `V` is empty under `hd`.)
7. **`dynamic_consensus_conductance`**: `Kernel.drift_absorption_seq` with
   `Ψ = potential (G 0 s)` (equal to `potential (G t x)` by `hdeg`) and
   `c t = (G 0 s).minDegree * max (φ t) 0 / 32` (`conductance ≥ 0`, so `max (φ t) 0 ≤
   conductance (G t x)`; `minDegree (G t x) = minDegree (G 0 s)` by `hdeg`); the hypothesis
   gives `4 Ψ² ≤ ∑ c t`.
8. **κ opinions** (`ConductanceMany.lean`). Prove the expectation form first, then the
   probability form: `P(T_cons > T) ≤ (1/(T+1)) ∑_{t ≤ T} P(T_cons > t)` (antitone) `≤ 1/2` once
   `T + 1 ≥ 2 T₀`; take `b_prob = 2 b_exp`, `T₀ = ⌈T/2⌉`.
   Expectation form (cleaned BGKM16 Lemma 2.3 + Part 1):
   * `ℓ(x) = #(univ.image x)` (opinions present), `ℓ = 1 ↔` consensus; support of
     `transition H x` ⊆ `{step x r}`, so the opinion set only shrinks. Generic helper:
     if `Q` is closed under the support of `K` and `f ≤ g` on `Q`, then `iterate n f ≤ iterate n g`
     on `Q`.
   * Projection: `iterate_project` with `colorIndicator i`; opinion `i` "resolved" (vanished or
     prevailed) at `t` iff the projected Bool configuration is at consensus; by
     `lazy_consensus_of_minority` on the projection (minority volume ≤ `vol(class i)`), `i` is
     resolved at time `B` with probability `≥ 1/2` if `128 vol(class i) ≤ d_min φ B`.
   * Phase step: let `θ` be real with `5θ/6 < ℓ(x) ≤ θ`, `ℓ(x) ≥ 2`. Fewer than `θ/3` present
     opinions have volume `> 3 vol(V)/θ`; the others (`|S| ≥ ℓ(x) - θ/3`) are resolved within
     `B = ⌈384 vol(V) / (θ d_min φ)⌉` rounds w.p. `≥ 1/2` each; reverse Markov
     (`R ≤ |S|`, `E R ≥ |S|/2`) gives `P(R ≥ |S|/4) ≥ 1/3`; on that event (support reasoning)
     `ℓ(X_B) ≤ max 1 (ℓ(x) - |S|/4) ≤ 5θ/6` (the paper says "w.p. 1/2 by Markov"; it is `1/3`).
   * Generic level lemma (candidate for `dynamics/`): if `K 1_{A'} ≤ 1_{A'}`, `D ⊆ A'`,
     `p > 0`, `B ≥ 1` and `iterate B 1_{A'} x ≤ 1 - p` for all `x ∈ D`, then for all `N`, `x`:
     `∑_{t<N} iterate t 1_D x ≤ B / p`. Proof by strong induction on `N` with
     `g_N = ∑_{t<N} iterate t 1_D`: `g_N ≤ N 1_{A'}`; outside `D`, `g_N = K g_{N-1} ≤ B/p`;
     on `D`, `g_N ≤ B + iterate B g_{N-B} ≤ B + (B/p)(1-p)`. (With `D = A'` = non-consensus it is
     also the restart argument of step 6.)
   * Levels `θ_j = (5/6)^j n`, `A'_j = {ℓ > θ_{j+1}}`, `D_j = {θ_{j+1} < ℓ ≤ θ_j}`; `{ℓ ≥ 2} ⊆
     ⋃_{j < J} D_j` with `θ_J < 2`; `∑_j B_j ≤ J + 384 · 2m · 3 / (d_min φ)`
     (`∑_{θ_j ≥ 2} 1/θ_j ≤ 3`); with `p = 1/3` the expected time is
     `≤ 3J + 6912 m/(d_min φ)`; absorb `J ≤ log_{6/5} n + 1` using `φ ≤ 1` and `n d_min ≤ 2m`,
     so `m/(d_min φ) ≥ n/2`. Any `b ≥ 7000` should do; the statement only asks `∃ b`.

## Deviations from the paper / roadmap

* **Lemma 2.1 sums over the minority side.** BGKM16 prints
  `𝔼[Ψ(S_{t+1}) | S_t = s_t] ≤ Ψ(s_t) - ∑_{u ∈ V} λ_{u,t} d_u / (32 Ψ(s_t)³)`. That is false: on
  the star `K_{1,15}` with one leaf in the minority the hub contributes `λ d = 15` (numbers
  above). The proof in the paper ends with `-∑_{u ∈ v^(0)} λ_u d_u / (32 Ψ³)` (sum over the
  minority side `s_t = v^(0)`), and Lemma 2.2 only uses that sum. We pin the corrected form with
  the paper's constant `32`.
* **λ_u**: the paper's definition has typos ("neighbours of `u` in `V ∖ v^1(t)`" for
  `u ∈ v^(0)`); the intended meaning, used in the proof, is the number of neighbours with the
  other opinion (`discordant`).
* **Constant 128 instead of 129** (Lemma 2.2: `τ* = min{t' : ∑ φ_i ≥ 129 vol(s_t̂)/d_min}`):
  FND-5's drift lemma gives `4 · 32 = 128`, which is stronger. The statements are "for every
  `T` with `128 vol ≤ d_min φ T`, `P(no consensus at time T) ≤ 1/2`", equivalent to
  `P(T_cons ≤ T) ≥ 1/2` because consensus is absorbing; no stopping times or path space. The
  paper's "with a probability of 1/2" is read as "at least 1/2".
* **Theorem 1.1 static, κ = 2, explicit constant**: `128 m / (d_min φ)` (from
  `vol(s_0) ≤ m`). The alternative bound `n log n / φ²` (part 2, Lemma 2.4) is not pinned (not
  required).
* **No connectivity hypothesis; `hd : ∀ v, 0 < G.degree v` instead.** `hd` is needed to define
  the lazy voter (`uniformNeighbor` needs a neighbour to sample), as in VOT-2. Connectivity is
  not needed: a disconnected graph without isolated vertices has `φ = 0` (a component of
  volume `≤ m` has empty cut), so the hypotheses force `m = 0` and the statements are vacuous.
* **Conductance**: defined exactly by the paper's formula, with `∑_{u ∈ U} λ_u` written as
  `#(G.interedges U Uᶜ)` (ordered pairs `(u, w)`, `u ∈ U`, `w ∉ U`, adjacent: one per cut
  edge). Convention `φ = 0` when no `U` has `0 < vol U ≤ m` (only for graphs without edges).
* **Expected time**: stated as `∑_{t < N} P(T_cons > t) ≤ 2 T₀` for every horizon `N`, i.e.
  `𝔼[min(T_cons, N)] ≤ 2 T₀`, which gives `𝔼[T_cons] ≤ 2 T₀` by monotone convergence. A `tsum`
  statement would be vacuous for non-summable series (`∑' = 0` in Mathlib), so it is avoided.
* **Dynamic graphs**: two opinions only (Lemma 2.2's generality, not Theorem 1.1's κ). The
  adversary chooses `G t x` from the time and the *current* configuration, not from the whole
  history as in the paper (a history-dependent adversary is not a kernel on configurations). The
  degrees are fixed (`hdeg`, relative to the first graph `G 0 s`; the paper fixes a degree
  sequence `d_1, …, d_n`), and `φ t` must bound the conductance of every graph the adversary may
  use at time `t` (the paper fixes the sequence `φ_t` in advance). Start time `t̂ = 0`; a later
  start is the same statement for the shifted family `fun t => G (t̂ + t)`. `vol(s_0)` and
  `d_min` are computed in `G 0 s` (they only depend on the degrees). `φ t` may be negative;
  this only weakens the hypothesis.
* **κ opinions**: static graph only; constant `∃ b` (the paper: "`b > 0` a suitable chosen
  constant"); `[Nonempty V]` is assumed, because with `V` and the colour type both empty the
  empty configuration has no consensus colour in `disagreement`'s convention while the
  hypothesis `b · 0 ≤ 0` holds. The paper's "`κ ≤ n` opinions" is automatic (any finite colour
  type; only the opinions present matter). The expectation form `lazy_expected_consensus_time_many`
  corresponds to the paper's `𝔼[T] ≤ b m / (4 d_min)` (in phases) in the proof of Part 1.
* **Opinions** are `Bool` for two opinions (`false` = the paper's opinion `0`, which wins ties
  of `minority`).

## Candidates for `dynamics/` (written as `voter/` helpers)

* `ConductanceIndep.lean` (all of it): resampling one coordinate of `Distribution.independent`,
  factorization, second/third moments of sums of independent centred coordinates, the
  concave-comparison lemma, two-point moments.
* `ConductanceLevels.lean`: `sum_iterate_le_of_block` (occupation time / restarting),
  `iterate_finset_sum`, `apply_finset_sum`.
* `ConductanceManyAux.lean`: `iterate_le_of_closed`, `iterate_const_sub`.
* `ConductanceBasic.lean`: `sqrt_add_le_taylor`, `sqrt_chord` (real analysis); the cut and
  conductance facts would belong next to a future `SimpleGraph` conductance in Mathlib.
