# PROGRESS: FND-5 (expectation-level drift lemma) and FND-7 (graph-indexed rounds)

Source: `ROADMAP.md`, rows FND-5 and FND-7. Branch `fnd5-drift`.

Paper for FND-5: Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model
in dynamic networks*, ICALP 2016, arXiv:1603.01895 (LaTeX source read: `VoterModel.tex`).
Numbering (`\newtheorem{lemma}[theorem]`, theorems numbered within sections; Section 2 is
"Analysis of the Voter Model"):

* Lemma 2.1 (`lem:technical-st`): `𝔼[Ψ_{t+1} | S_t] ≤ Ψ_t − ∑_u λ_u d_u / (32 Ψ_t³)`,
  `Ψ = √vol(minority)`.
* **Lemma 2.2** (`lem:two-op-const-prob`): with `τ* = min{t' : ∑_{i=t̂}^{t'} φ_i ≥ 129 vol(s_t̂)/d_min}`,
  `P(T ≤ τ* + t̂) ≥ 1/2`. Proof: drift `c_t = d_min φ_t / 32` (from 2.1 and conductance),
  Jensen gives `𝔼[Ψ_{t+1}] ≤ 𝔼[Ψ_t] − c_t P(T>t)² / 𝔼[Ψ_t]`, contradiction once
  `∑ φ_t > 128 vol/d_min`, i.e. `∑ c_t > 4 Ψ₀²`.
* Lemma 2.3 (`fraction`): phases for `κ > 2` opinions.
* Lemma 2.4 (`lem:forsecondpart`): multiplicative drift
  `𝔼[Ψ_{t+1}] ≤ (1 − φ_t²/(32n)) 𝔼[Ψ_t]`, then Markov with `Ψ_min ≥ 1`.

## Status

* **Phase 1 (pin statements): done.**
* **Phase 2 (proofs): done (2026-10-07).** All 18 pinned theorems are proved; `lake build
  Dynamics` is warning-free; `python3 ../scripts/check_axioms.py` passes (20 declarations in
  `Audit.lean`, 8 of them new) and a scratch `#print axioms` over all 18 pinned theorems shows
  only `propext`, `Classical.choice`, `Quot.sound` (`edgeRound_nonempty`: no axioms). The text
  of every pinned declaration up to `:=` is byte-identical to the committed phase-1 version
  (checked by script, also with the strict "up to the first `:=`" reading, see Errors/notes).

## Pinned (see `PINNED.txt` at the repository root; text up to `:=` is frozen)

All in `dynamics/`. Drift files: namespace `Dynamics.Kernel`; graph rounds: namespace `Dynamics`.

| Declaration | File | Statement in words |
| --- | --- | --- |
| `iterateSeq` (def) | `Dynamics/DriftSeq.lean` | time-dependent chain: expected `f` after steps `K 0, …, K (n-1)`; recursion `iterateSeq K (n+1) f = iterateSeq K n ((K n).apply f)` |
| `iterateSeq_const` | same | `iterateSeq (fun _ => K) n f = K.iterate n f` |
| `drift_absorption_seq` | `Dynamics/Drift.lean` | Lemma 2.2, time-dependent: `Ψ ≥ 0`; for `t < T`: `0 ≤ c t`, `(K t).apply Ψ x ≤ Ψ x − c t / Ψ x` if `Ψ x > 0`, `(K t).apply Ψ x = 0` if `Ψ x = 0`; `4 Ψ(x₀)² ≤ ∑_{t<T} c t` ⇒ `1/2 ≤ P_T(Ψ = 0)` (as `iterateSeq` of the indicator) |
| `drift_absorption` | same | Lemma 2.2, one kernel: same with constant `c ≥ 0`, `4 Ψ(x₀)² ≤ c T` ⇒ `1/2 ≤ K.event (Ψ = 0) T x₀` |
| `multiplicative_drift_seq` | same | Lemma 2.4 argument, time-dependent: `Ψ ≥ 0`, `Ψmin > 0` below every nonzero value, `(K t).apply Ψ x ≤ (1 − δ t) Ψ x` for `t < T` and all `x` ⇒ `P_T(Ψ > 0) ≤ ∏_{t<T}(1 − δ t) Ψ(x₀)/Ψmin` |
| `multiplicative_drift` | same | one kernel: `K.event (0 < Ψ) T x₀ ≤ (1 − δ)^T Ψ(x₀)/Ψmin` |
| `NeighborRound` (abbrev) | `Dynamics/GraphRounds.lean` | `∀ v : V, G.neighborSet v` (every vertex picks a neighbour) |
| `EdgeRound` (abbrev) | same | `G.Dart` (one oriented edge) |
| `avg_neighborSet` | same | `avg` over `N(v)` = `(∑ u ∈ G.neighborFinset v, g u) / G.degree v` |
| `neighborRound_nonempty` | same | no isolated vertex ⇒ `Nonempty (NeighborRound G)` |
| `card_neighborRound` | same | `card = ∏ v, G.degree v` |
| `avg_neighborRound_prod` | same | independence: `avg (∏ v, f v (r v)) = ∏ v, avg_{N(v)} (f v)` (no hypothesis) |
| `avg_neighborRound_eval` | same | marginal (no isolated vertex): `avg (g (r v)) = avg_{N(v)} g` |
| `avg_neighborRound_mul` | same | `v ≠ w`, no isolated vertex: `avg (g (r v) * h (r w)) = avg_{N(v)} g * avg_{N(w)} h` |
| `avg_neighborRound_sum` | same | no isolated vertex: `avg (∑ v, f v (r v)) = ∑ v, avg_{N(v)} (f v)` |
| `avg_vertex_neighborRound` | same | no isolated vertex: `avg_{(v,r) : V × NeighborRound G} F v (r v) = avg_v avg_{N(v)} F v` |
| `edgeRound_nonempty` | same | `G.Adj u v` ⇒ `Nonempty (EdgeRound G)` |
| `avg_edgeRound_symm` | same | `avg (F d.snd d.fst) = avg (F d.fst d.snd)` |
| `avg_edgeRound` | same | `avg (F d.fst d.snd) = (∑ v, ∑ u ∈ N(v), F v u) / (2 |E|)` |
| `avg_edgeRound_edge` | same | `avg (g d.edge) = avg_{e : G.edgeSet} g e` |
| `avg_edgeRound_fst` | same | `avg (g d.fst) = (∑ v, deg v · g v) / (2 |E|)` |

Instance arguments were checked with `#check` (the `unusedSectionVars` linter is active and only
fires once a proof exists): `edgeRound_nonempty` takes no instances; `avg_neighborSet`,
`neighborRound_nonempty`, `avg_edgeRound_symm` take `[Fintype V] [DecidableRel G.Adj]` only; the
others also `[DecidableEq V]`. Phase 2 must keep the `section`/`variable` layout of
`GraphRounds.lean` (it determines these arguments).

## Proved

Files (all in `dynamics/Dynamics/`):

* `DriftSeq.lean` (114 lines): `iterateSeq`, `iterateSeq_const` (pinned); unpinned API
  `iterateSeq_zero` (simp), `iterateSeq_succ`, `apply_add`, `apply_mul`, `apply_const`,
  `iterateSeq_mono`, `_add`, `_mul`, `_const_fun`, `_nonneg`, `_lin`, `_one_sub`, and
  `event_eq_iterateSeq` (bridge from `Kernel.event`, any decidability instance, by `congr!`).
* `DriftAux.lean` (164 lines, new helper file): `ind_eq_zero_eq`, `ind_pos_le_div` (Markov),
  `exists_pos_mul_ind_le` (least positive value of `Ψ`), `apply_ind_pos_le`,
  `iterateSeq_ind_pos_antitone` (survival antitone), `apply_le_lin` (linearized drift),
  `iterateSeq_le_sub_of_drift` and `iterateSeq_le_prod_of_drift` (the two inductions on
  `𝔼[Ψ_t]`).
* `Drift.lean` (138 lines): the four pinned drift theorems, each a short proof from the helpers.
* `GraphRounds.lean` (189 lines): the 13 pinned graph-round theorems, plus the unpinned helper
  `nonempty_neighborSet`.

Proof routes:

* **Drift lemma (Lemma 2.2).** The paper's Jensen step `𝔼[1/Ψ] ≥ P(Ψ>0)²/𝔼[Ψ]` is replaced by
  the pointwise bound `1/y ≥ 2λ − λ²y` (from `(1 − λy)² ≥ 0`), with the fixed multiplier
  `λ = q/Ψ(x₀)`, `q = P_T(Ψ > 0)`. Then `K_t Ψ ≤ (1 + c_t λ²) Ψ − 2 c_t λ 1_{Ψ>0}` pointwise, and
  since `𝔼[Ψ_t] ≤ Ψ(x₀)` and `P_t(Ψ>0) ≥ q` for `t ≤ T`, each step lowers `𝔼[Ψ]` by `c_t λ q`.
  So `m q ≤ 𝔼[Ψ_T] ≤ Ψ(x₀)(1 − 4q²)` with `m > 0` the least positive value of `Ψ`, forcing
  `q ≤ 1/2`. Only monotonicity and linearity of `iterateSeq` are used (no Cauchy–Schwarz, no law
  of `X_t` as a `Distribution`). Same constant as the paper's proof.
* **Multiplicative drift (Lemma 2.4).** If `Ψ ≢ 0`, `hdrift` at a state with `Ψ > 0` forces
  `1 − δ_t ≥ 0`; induction gives `𝔼[Ψ_T] ≤ ∏(1 − δ_t) Ψ(x₀)`; Markov `1_{Ψ>0} ≤ Ψ/Ψmin`.
  If `Ψ ≡ 0` both sides vanish.
* **Graph rounds.** `avg_neighborRound_prod`: dependent `Fintype.prod_sum`, `Fintype.card_pi`,
  `prod_div_distrib`; marginals by specializing to indicator-style products
  (`Fintype.prod_ite_eq'`, `prod_eq_single`, `prod_eq_mul`); darts: `avg_equiv` with
  `Dart.symm_involutive.toPerm`, `sum_fiberwise` + `dart_fst_fiber` + `dartOfNeighborSet_injective`,
  `dart_edge_fiber_card`, `dart_card_eq_twice_card_edges`.

Reusable pieces: the `iterateSeq` API (time-dependent chains), `event_eq_iterateSeq`,
`iterateSeq_ind_pos_antitone` (absorbing zero set ⇒ survival antitone), `ind_pos_le_div`
(Markov for a potential with a gap), and all of `GraphRounds`.

Docs: `README.md` module table (`DriftSeq`, `Drift`, `GraphRounds`), blueprint section "Drift
and graph rounds" (all `\lean{}` names checked to resolve), `Audit.lean` (8 new entries).

## Remaining

Nothing inside `dynamics/`. Outside this job's write scope (left for the maintainer): ROADMAP
rows FND-5/FND-7 status, and a PROVENANCE entry (published proof followed for Lemma 2.4; for
Lemma 2.2 the Jensen step is replaced by its linearized form, same constant).

## Errors / notes

* `unusedSectionVars` linter is active: an automatically included instance not used by the
  statement or proof gives a warning that could only be fixed by `omit … in` (changing the
  signature). The statements were arranged so this cannot happen, with one wrinkle: in
  `section Edge`, `[DecidableEq V]` is in fact not needed by `avg_edgeRound`, `avg_edgeRound_edge`,
  `avg_edgeRound_fst` (this Mathlib's `Fintype (Sym2 V)` instance needs no `DecidableEq`), so
  these frozen statements carry a superfluous (harmless) instance argument. The chosen proofs
  use it (fiberwise over `d.fst`, `Finset.filter` on edges), so there is no warning. A future
  restatement could drop that `variable` line.
* `iterateSeq` is defined by pattern matching, so its text contains no `:=`; a gate reading "up
  to the first `:=`" runs into the next declaration. Hence `iterateSeq_const` must stay directly
  after the definition (the API lemmas come after it, and its proof uses `show`, not
  `iterateSeq_succ`).
* `K.event` uses classical decidability; the `_seq` statements use the default instances of
  `ℝ`. Bridge: `event_eq_iterateSeq` (`congr!`).
* `push_neg` is deprecated in this Mathlib (warning); use `not_le.mp`, `not_forall.mp`.
* The phase-1 subagent that wrote the drift proofs in `/tmp` was cut off by a usage limit after
  finishing them; they were integrated and split into `DriftAux.lean` in phase 2.

## Plan

Done. Possible follow-ups (not requested): a restart corollary (geometric tail
`P_{kT}(Ψ > 0) ≤ 2^{-k}` when `4 max Ψ² ≤ c T`, via `geometric_blocks`) and the expected-time
bound for VOT-5.

## Deviations from the paper

FND-5:

1. **Generic potential.** The paper states Lemma 2.2 for the two-opinion voter model with
   `Ψ = √vol(minority)`, its drift coming from Lemma 2.1 and the conductance bound. We state the
   abstract drift lemma for any nonnegative `Ψ` on a finite chain with drift `c_t / Ψ`; the
   voter instance (`c_t = d_min φ_t / 32`) belongs to VOT-5.
2. **Constant 4 (the paper's 128, not 129).** The statement uses
   `∑ φ ≥ 129 vol(s)/d_min`, the proof needs only `128`, which in drift units
   `c_t = d_min φ_t/32` is `∑_{t<T} c_t ≥ 4 Ψ₀²`. We state the proof's (slightly stronger)
   threshold, non-strict.
3. **Time-dependent chains** are modelled by a family `K : ℕ → Kernel α` (new definition
   `iterateSeq`). The paper's adversary may choose `G_{t+1}` knowing the past; a family of kernels
   covers adversaries depending on the time and the current state (a kernel is a function of the
   state); a history-dependent adversary needs the relevant history in the (finite) state.
4. **Start time.** The paper starts at an arbitrary time `t̂` with `s_t̂` fixed; we start at
   time `0` from `x₀` (shift the family: `fun t => K (t̂ + t)`).
5. **Absorption is `Ψ = 0`**, as in the paper (`T` = first time `s_t = ∅`, i.e. `Ψ_t = 0`), and
   is an explicit hypothesis `habs` (`K.apply Ψ x = 0` when `Ψ x = 0`); in the paper it is
   implicit (consensus is absorbing, used as `𝔼[Ψ_t | T ≤ t] = 0`). It cannot be dropped: a
   chain alternating between `Ψ = 1` and `Ψ = 0` satisfies the drift but is absorbed at no even
   time.
6. Hypotheses are required only for the steps `t < T` (a generalization).
7. **Multiplicative drift.** The paper's Lemma 2.4 is voter-specific (`δ_t = φ_t²/(32n)`,
   `Ψ_min ≥ 1`, `Ψ₀ ≤ n`) and concludes `P(T ≤ τ') ≥ 1 − 1/n²` via AM–GM and `exp`. We state the
   generic bound `∏_{t<T}(1 − δ_t) Ψ₀ / Ψmin` (`(1 − δ)^T Ψ₀/Ψmin` for one kernel); the `exp`
   form follows from `Real.one_sub_le_exp_neg`-type lemmas. No hypothesis on `δ` is needed (if
   `1 − δ_t < 0`, `hdrift` forces `Ψ ≡ 0`). Source typos noticed: the statement of Lemma 2.4
   reads `Pr(T ≤ τ') ≥ 1/n²` (the proof gives `1 − 1/n²`), and its chain of inequalities ends
   with `exp(+∑ φ_i²/32n)` instead of `exp(−∑ φ_i²/32n)`.

FND-7:

8. **"One uniformly random edge per step" uses oriented edges** (`SimpleGraph.Dart`): a uniform
   dart is a uniform edge with a uniform orientation (`avg_edgeRound_edge`,
   `avg_edgeRound_symm`); the orientation is what asymmetric rules (push/pull,
   initiator/responder) need. The roadmap's "random node" variant is not a new type:
   `V × NeighborRound G` read at `(v, r v)` (`avg_vertex_neighborRound`).
9. `NeighborRound G` is empty when `G` has an isolated vertex (then `avg` over it is `0` by
   convention), so the marginal lemmas assume `∀ v, 0 < G.degree v`; the product lemma
   (`avg_neighborRound_prod`) holds unconditionally. Its relation to `RumorPush.Tgt n`
   (complete graph on `Fin n`) is only documented, since `dynamics/` does not import
   `rumor_spread/`.
