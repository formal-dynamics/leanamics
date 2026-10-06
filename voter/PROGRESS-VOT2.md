# PROGRESS: VOT-2, neutral Wright–Fisher and the lazy voter

Job: roadmap row VOT-2. Source: Hassin, Peleg, *Distributed probabilistic polling and
applications to proportionate agreement*, Inf. Comput. 171 (2001): Theorem 2.1, Section 2.3,
Corollary 2.2 and the **Remark on p. 254** (quoted in `FORMALIZATION_DIFFERENCES.md` §2.6:
"one can always add self-loops, with arbitrary chosen weights (even to a single node) … In this
case Theorem 2.1 holds without the requirement that the graph is nonbipartite"). The lazy
kernel `(I + D⁻¹A)/2` is the one of VOT-5 (Berenbrink–Giakkoupis–Kermarrec–Mallmann-Trenn).

## Status

* **Phase 1 (pin statements): done.** 11 pinned declarations (9 theorems, 2 definitions),
  listed in `PINNED.txt` at the repo root.
* **Phase 2 (proofs): done.** Every `sorry` is replaced. `lake build Voter` gives no warnings.
  All 11 pinned declarations depend only on `propext`, `Classical.choice`, `Quot.sound`
  (`#print axioms` in `/tmp/vot2/Axioms.lean`, and `python3 ../scripts/check_axioms.py`
  passes on the extended `Audit.lean`: 28 declarations). Pinned text up to `:=` was checked to
  be byte-identical to phase 1 (`/tmp/vot2/cmp.py`). No pinned statement was false.
* Phase-1 numerical cross-check (exact rationals, `/tmp/vot2check/check.py`): lazy voter on
  bipartite `K_2`, `P_3`, `K_{1,3}`, `C_4`, `P_5`; a single self-loop with random weights on
  bipartite graphs; Wright–Fisher `n ≤ 5`. All absorption probabilities matched the theorems.

## Pinned (frozen up to `:=`), all in namespace `Voter`, all proved

`voter/Voter/LazyLoop.lean` (Remark p. 254, the roadmap's "optional extension")
* `consensus_probability_of_selfLoop`: `G` connected (bipartite allowed), `H` charges every edge
  of `G`, `∃ v, 0 < (H v).weight v`, `p` stationary for `H` ⟹
  `eventualColor H true s = whiteMass p s`.
* `color_consensus_probability_of_selfLoop`: same hypotheses, any finite palette ⟹
  `eventualColor H c s = p.prob (fun i => s i = c)`.

`voter/Voter/Lazy.lean`
* `lazy K` (def): kernel `(I + K)/2`. `lazyNeighbor G hd = lazy (uniformNeighbor G hd)`, i.e.
  `(I + D⁻¹A)/2`. `lazy_weight`, `lazyNeighbor_weight`: entry formulas (`rfl`).
* `lazy_stationary_iff`: `(lazy K).Stationary p ↔ K.Stationary p`.
* `lazy_consensus_probability`: `G` connected, `H` charges every edge, `p` stationary for `H` ⟹
  `eventualColor (lazy H) c s = p.prob (fun i => s i = c)`.
* `lazyNeighbor_consensus_probability`: `G` connected, `hd` ⟹ consensus in `c` with probability
  `∑ i with s i = c, deg i / (2 |E|)`.

`voter/Voter/WrightFisher.lean` (kernel: the existing `wfKernel V`)
* `wrightFisher_fixation_of_three_le`: `3 ≤ |V|` ⟹ allele `a` fixes w.p. `#{i | s i = a} / |V|`,
  proved from the existing `color_consensus_probability` on `⊤` (no use of the extension).
* `wrightFisher_fixation`: the same for every nonempty `V`, via the extension.

## Proof structure (phase 2)

* `voter/Voter/LazyPropagation.lean` (new, 129 lines), the only real new argument:
  `KernelPossible H s t` (a round in the support of `H`), `exists_weight_pos` (every finite
  distribution charges a point), `kernelPossible_positive` and
  `reachable_success_of_kernelPossible` (as `possible_positive` / `reachable_success`),
  `propagate_kernel_region` (Lemma 2.1 propagation through the kernel support: a monochromatic
  region whose vertices charge a vertex of the region grows to consensus; reuses
  `boundary_edge`), `kernelPossible_consensus_of_selfLoop` (start from `{v}`, `v` its own
  internal neighbour), `consensus_tendsto_of_selfLoop` (via `Kernel.finite_absorption`).
* `LazyLoop.lean`: `eventualColor_eq_whiteMass_of_tendsto` (Lemma 2.2 in graph-free form:
  vanishing nonconsensus probability ⟹ eventual white probability = stationary white mass;
  reusable by any future absorption result), then the two pinned theorems; the colour version
  projects with `eventualColor_project` exactly as `color_consensus_probability`.
* `Lazy.lean`: `lazy_selfLoop_pos`, `lazy_weight_pos`; the lazy theorems are 3–4 line
  corollaries (`degree_stationary`, `degree_weight`, `uniformNeighbor_support` reused).
* `WrightFisher.lean`: `wfKernel_pos`, `wfKernel_stationary`, `uniform_prob_eq_card` (via
  `Dynamics.avg_indicator` and `Distribution.uniform_expect`), `top_not_colorable_two`; each
  pinned theorem is a single `rw`.
* Docs updated inside `voter/`: README table and paragraph, `FORMALIZATION_DIFFERENCES.md` §2.6
  (the Remark is now formalized), blueprint section "Self-loops, the lazy voter and
  Wright–Fisher (VOT-2)" (all 83 `\lean{}` names resolve), `Audit.lean` (+8 entries).

## Remaining

Nothing for VOT-2 inside `voter/`. Outside `voter/` (not editable in this job): mark ROADMAP
row VOT-2 done and add a `PROVENANCE.md` row (Hassin–Peleg Thm 2.1 / §2.3 / Remark p. 254;
lazy voter; Wright–Fisher). Optional cleanups: `Examples.wrightFisher_stationary` duplicates
`wfKernel_stationary` on `Fin 3` (left untouched); `uniform_prob_eq_card` and
`exists_weight_pos` are generic and could move to `dynamics/`.

## Errors

None open. Phase-2 hiccup fixed: `uniformNeighbor_support` lives in `Voter.Corollaries`, so
`Lazy.lean` imports that instead of `Voter.Uniform`.

## Deviations from the paper / roadmap

* **Wright–Fisher is modelled with labelled individuals** (the synchronous voter with kernel
  `wfKernel V`, each offspring picks a uniform parent with replacement), not as the classical
  count chain `X_{t+1} ~ Bin(n, X_t/n)`. The count chain is the lumping of this one and has
  the same fixation event; stating it on labelled configurations is what makes it a corollary
  of the voter theorem, as the roadmap asks. Population size is `n = Fintype.card V` for an
  arbitrary finite type `V` rather than `Fin n` (more general; `Fin n` is a special case).
* **Wright–Fisher for all `n ≥ 1`** (`wrightFisher_fixation`) is pinned in addition to the
  requested `n ≥ 3` version, because the self-loop extension (needed anyway for the lazy voter)
  gives it for free; the `n ≥ 3` version is kept to record that the existing theorem suffices
  there.
* **Lazy voter on any connected graph needs the Remark p. 254.** The existing theorem requires
  `¬ G.Colorable 2`, and for `(I + D⁻¹A)/2` on a bipartite `G` every loopless graph `G'` with
  `G'.Adj i j → 0 < H i j` is a subgraph of `G`, hence bipartite, so the bipartite case cannot
  be obtained from the existing theorem by choosing another graph. The roadmap's optional
  extension is therefore pinned (`*_of_selfLoop`) and the lazy results go through it. Our
  extension is slightly more general than the Remark: as in the existing theorem, `H` may
  charge non-edges too (only
  `G.Adj i j → 0 < H i j` is assumed), and one positive diagonal entry suffices, as the Remark
  says ("even to a single node").
* **The lazy voter needs `hd : ∀ i, 0 < G.degree i`** (every vertex has a neighbour to sample),
  as `uniformNeighbor` does. For a connected graph this excludes only the one-vertex graph,
  where the statement is trivial. Laziness is fixed at `1/2`, as in the roadmap and VOT-5.
* **Only the many-colour forms are pinned for the lazy voter** (`lazy_consensus_probability`,
  `lazyNeighbor_consensus_probability`); the Boolean form is the instance `C = Bool`,
  `c = true`, whose right side is literally the one of `uniform_consensus_probability`.
* `eventualColor` is, as elsewhere in the package, the supremum of the finite-time consensus
  probabilities (no path space); see `FORMALIZATION_DIFFERENCES.md`.
