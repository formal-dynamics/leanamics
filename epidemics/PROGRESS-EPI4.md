# EPI-4 progress: COBRA ⇔ BIPS duality

Source: Cooper, Radzik, Rivera, *The coalescing-branching random walk on expanders and the dual
epidemic process*, PODC 2016, arXiv:1602.05768. Formalized: Theorem 4 (Section 2) and its case
`C = {u}`, equation (2) (Section 1, overview of the proof of Theorem 1). The cover-time bound
(Theorems 1–3, roadmap size L) is out of scope for this job.

Paper's statement (Theorem 4): *Let G be a connected regular graph and consider the COBRA and BIPS
processes on G with parameter k ≥ 1. For each v ∈ V, C ⊆ V and t ≥ 0,
P̂(Hit_C(v) > t | C₀ = C) = P(C ∩ A_t = ∅ | A₀ = v).* The proof's base case ("trivial if v ∈ C,
since both probabilities are 0") fixes `Hit_C(v) = min {s ≥ 0 : v ∈ C_s}` (time 0 included).

## Status

Phase 1 (pin the statements): **done** (2026-10-06).
Phase 2 (prove them): **done** (2026-10-06). `lake build Epidemics` is warning-free; no `sorry`,
`admit`, `axiom` or options; `python3 ../scripts/check_axioms.py` checks 12 declarations, all on
`propext`, `Classical.choice`, `Quot.sound` only. Pinned headers (text up to `:=`) are
byte-identical to phase 1, and the elaborated signatures are unchanged.

## Pinned (`PINNED.txt` at the repository root)

`epidemics/Epidemics/Cobra.lean` (model, namespace `Epidemics`):
* `Choices G k := (x : V) → Fin k → G.neighborSet x`: one round, every vertex samples `k`
  neighbours (uniform element = independent uniform choices with replacement).
* `instFintypeChoices`: its `Fintype` instance (used implicitly by every `expList (Choices G k)`).
* `choices_nonempty`: connected `G` with `Nontrivial V` ⇒ `Nonempty (Choices G k)` (the model is
  well defined on the paper's graphs; `expList` over it has total mass 1).
* `cobraStep D r = D.biUnion (fun x => univ.image fun i => ↑(r x i))`; `cobraRun C l` = foldl.
* `bipsStep v A r = insert v (univ.filter fun u => ∃ i, ↑(r u i) ∈ A)`; `bipsRun v A₀ l` = foldl.

`epidemics/Epidemics/CobraDuality.lean`:
* `cobra_hit_iff_bips_reverse` (pathwise duality): `(∃ s ≤ l.length, v ∈ cobraRun C (l.take s))
  ↔ (C ∩ bipsRun v {v} l.reverse).Nonempty`, for every list of rounds `l`.
* `cobra_bips_duality` (Theorem 4): `expList (Choices G k) t (fun l => if ∀ s ≤ t, v ∉ cobraRun C
  (l.take s) then 1 else 0) = expList (Choices G k) t (fun l => if C ∩ bipsRun v {v} l = ∅ then 1
  else 0)`.
* `cobra_bips_duality_singleton` (equation (2)): same with `C = {u}` and right side `u ∉ A_t`.

## Proved

All pinned theorems, plus the helpers below.

| File | Lines | Content |
| --- | --- | --- |
| `Epidemics/Cobra.lean` | 72 | model; `choices_nonempty` (via `Preconnected.exists_adj_of_nontrivial`) |
| `Epidemics/CobraReverse.lean` | 45 | `reverse_ofFn`, `revEquiv`, `expList_reverse` (FND-6), `expList_congr_length` |
| `Epidemics/CobraLemmas.lean` | 53 | `mem_cobraStep`, `mem_bipsStep`, `cobraRun_nil/cons`, `bipsRun_append_singleton`, `hits_cons` |
| `Epidemics/CobraDuality.lean` | 72 | pathwise lemma (induction on the rounds), Theorem 4, equation (2) |

Also updated inside `epidemics/`: `Epidemics.lean` (imports), `Audit.lean` (5 new `#print axioms`),
`README.md` (EPI-4 section), `blueprint/src/content.tex` (two sections, `\lean{}` tags).

Before pinning, the statements were also checked by brute force (Python, exhaustive over round
sequences where feasible) on P₃, K₃, K₁,₃, C₄ and an irregular 5-vertex graph, `k ∈ {1, 2}`,
`t ≤ 3`: zero mismatches.

## Remaining

Nothing inside `epidemics/`. Outside the allowed scope of this job (repository root), for the
maintainer: a `PROVENANCE.md` entry and the EPI-4 status in `ROADMAP.md` (duality done; the
cover-time bound of Theorems 1–3, size L, stays open). `expList_reverse` could be upstreamed to
`dynamics/Dynamics/Equivalence.lean` as roadmap FND-6 and `Choices` to `dynamics/` as part of
FND-7 (both live in `epidemics/` because this job may only change that package).

## Errors

None open. Fixed during phase 2: the `nil` case of the pathwise lemma needed a split on `v ∈ C`
(`by_cases hv : v ∈ C <;> simp [bipsRun, hv]`); `Finset.singleton_inter_eq_empty` does not exist,
used `← Finset.disjoint_iff_inter_eq_empty` and `Finset.disjoint_singleton_left` instead. In
scratch: `rw [← expList_reverse]` rewrites the COBRA side, so use `conv_rhs`; `push_neg` is
deprecated in this Mathlib, use `push Not`.

## Proof route (as implemented)

1. Pathwise lemma by induction on the rounds `l`, generalizing `C`: `hits_cons` unfolds the first
   COBRA round; `List.reverse_cons` and `bipsRun_append_singleton` unfold the last BIPS round of
   the reversed list; the two one-round membership lemmas match the chains.
2. FND-6: through `Dynamics.expList_eq_avg_ofFn`, reversal is `ω ↦ ω ∘ Fin.rev` on `Fin T → α`
   (`List.ofFn_eq_map`, `List.finRange_reverse`), and `Dynamics.avg_equiv` with `revEquiv`.
3. Theorem 4: reverse the BIPS side (`conv_rhs => rw [← expList_reverse]`), compare pointwise on
   lists of length `t` (`expList_congr_length`) with the pathwise lemma.
4. Equation (2): Theorem 4 and `{u} ∩ A = ∅ ↔ u ∉ A`.

## Deviations from the paper

1. **Hypotheses dropped (statement strengthened).** The paper (and the roadmap row) assume `G`
   connected and regular and `k ≥ 1`. `cobra_bips_duality`, `cobra_bips_duality_singleton` and
   the pathwise lemma hold for every finite simple graph and every `k` (including `k = 0`), so they
   are pinned without these hypotheses. Reasons: the paper's proof uses none of them (it only
   matches each vertex's choice law in the two processes; regularity is never used, and the
   brute-force check confirms the identity on irregular graphs); and unused hypotheses in a pinned
   statement would trigger the unused-variables linter once proved, blocking a warning-free build.
   The paper's hypotheses appear in `choices_nonempty`: on a connected graph with at least two
   vertices the round type is nonempty, so both sides are genuine probabilities. On a graph with an
   isolated vertex and `k ≥ 1` (where neither process is defined) the round type is empty and both
   sides are `0` for `t ≥ 1` by the `avg` convention, so the statement is vacuous there.
2. **Conditioning on the initial state.** `P̂(· | C₀ = C)` and `P(· | A₀ = v)` are expressed by
   starting the round-driven processes at `C` and `{v}` and averaging over `t` i.i.d. uniform
   rounds with `Dynamics.expList` (finite probability layer, no path space). Both processes read
   the same round type, a coupling of the two per-vertex sampling laws; each ignores the choices
   it does not use (COBRA: vertices outside `C_s`; BIPS: the source `v`), as in the paper's
   model.
3. **Hitting time as an event.** `Hit_C(v)` is not defined as a random variable; `Hit_C(v) > t`
   is written as `∀ s ≤ t, v ∉ C_s` with `C_s = cobraRun C (l.take s)`, time 0 included (the
   convention fixed by the paper's base case).
4. **Extra pathwise result and proof route.** The pathwise identity `cobra_hit_iff_bips_reverse`
   is not stated in the paper (its intuition paragraph sketches it for `k = 1`). The proof of
   Theorem 4 goes through it and time reversal of i.i.d. rounds (FND-6), instead of the paper's
   induction on `t` with one-step conditioning; the statement is the same.
5. **Generalized BIPS start.** `bipsRun` takes any initial infected set `A₀`; the theorems use the
   paper's `A₀ = {v}`.
6. **Round type local to the package.** `Choices` is defined in `epidemics/` because the
   graph-indexed round types of FND-7 do not exist yet in `dynamics/`; it can be upstreamed later.
