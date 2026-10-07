# PROGRESS: CRN-3, semilinear predicates are stably computable (easy direction)

Job: roadmap row CRN-3 (track CRN), easy direction. Sources: Angluin, Aspnes, Diamadi, Fischer,
Peralta, *Computation in networks of passively mobile finite-state sensors*, Distributed Computing
18 (2006) [AADFP06], §3 (model: 3.1 protocols, 3.2 stable computation, 3.3 standard populations,
3.4 symbol-count input and all-agents predicate output conventions) and §4 (Lemma 3 and
Corollary 2: Boolean closure; Lemma 5: threshold and remainder predicates; Theorem 5:
Presburger-definable predicates). Angluin–Aspnes–Eisenstat–Ruppert 2007 [AAER07] for the
combinatorial (reachability) form of stable computation. For the CRN transfer: Chen–Doty–
Soloveichik, *Deterministic function computation with chemical reaction networks*, Natural
Computing 13 (2014) [CDS14], §2.1 (reachability) and §2.2 (chemical reaction deciders), which
cite Angluin–Aspnes–Eisenstat, PODC 2006 [AAE06] for the "every species votes" convention.

## Status

* **Phase 1 (pin statements): done.** Six new files `crn/Crn/Stable*.lean`, imported from
  `Crn.lean`. `lake build Crn` succeeds with only `declaration uses 'sorry'` warnings (13, one per
  pinned theorem). `PINNED.txt` (repo root) lists the 28 pinned declarations (15 definitions,
  13 theorems); each entry checked to occur after its keyword in its file. The 13 theorems are
  appended to `crn/Audit.lean` (they show `sorryAx` until phase 2).
* **Phase 2 (proofs): done.** All 13 pinned theorems are proved; no pinned statement was false.
  `lake build Crn` is warning-free (CRN-3 modules also rebuilt from scratch); no `sorry`, `admit`,
  `axiom`, `native_decide` or `set_option`. `#print axioms` (scratch file under `/tmp`) and
  `python3 ../scripts/check_axioms.py` (26 declarations of `Audit.lean`): only `propext`,
  `Classical.choice`, `Quot.sound`. The pinned text of all 28 declarations (doc comment and text
  up to `:=`, whole block for `structure`/`inductive`) is byte-identical to the phase-1 commit
  `fe1cbf1` (checked mechanically, with a negative control); only imports and `sorry`s changed in
  the pinned files, plus two module-doc paragraphs and the helper lemma `counts_comp` in
  `StableCrn.lean` (it needs the pinned `Counts.map`).

## Pinned (frozen up to `:=`)

`Crn/StableBasic.lean` (namespace `Crn`; reuses CRN-1's `AgentPair`, `counts`)
* `Protocol X Q`: `input : X → Q`, `output : Q → Bool`, `δ : Q × Q → Q × Q` (initiator, responder).
* `Protocol.interact P c e`: encounter `e = (u, v)` (an `AgentPair n`): `u` gets `δ₁(c u, c v)`,
  `v` gets `δ₂(c u, c v)`, others unchanged (two `Function.update`s).
* `Protocol.Step P c c'`: `∃ e : AgentPair n, c' = P.interact c e` (complete interaction graph).
* `Protocol.Reaches P := Relation.ReflTransGen P.Step`.
* `Protocol.OutputStable P b c`: every agent outputs `b` in every configuration reachable from `c`.
* `Protocol.StablyComputes P φ` (`φ : (X → ℕ) → Bool`): for all `n > 0`, all `ι : Fin n → X`,
  every `c` reachable from `P.input ∘ ι` reaches some `d` that is output-stable with output
  `φ (counts ι).1`.
* `StablyComputable φ`: `∃ (Q : Type) (_ : Finite Q) (P : Protocol X Q), P.StablyComputes φ`.
* `Protocol.StablyComputes.unique` (sanity check of the definition): if `P` stably computes `φ`
  and `ψ`, then `φ x = ψ x` for every `x ≠ 0`.

`Crn/StableBoolean.lean`
* `StablyComputable.map₂` (**AADFP06 Lemma 3**): for every `ξ : Bool → Bool → Bool`, `φ`, `ψ`
  stably computable ⇒ `fun x => ξ (φ x) (ψ x)` stably computable.
* `StablyComputable.not`, `.and`, `.or` (Corollary 2): closure under `!`, `&&`, `||`.

`Crn/StableThreshold.lean`
* `threshold a c x = decide (∑ i, a i * (x i : ℤ) < c)` (`a : X → ℤ`, `c : ℤ`), Lemma 5(1)'s form.
* `stablyComputable_threshold` (**Lemma 5(1)**): `StablyComputable (threshold a c)`.
* `stablyComputable_le_sum` (roadmap form): `StablyComputable fun x => decide (c ≤ ∑ aᵢ xᵢ)`.

`Crn/StableRemainder.lean`
* `remainder a c m x = decide (∑ i, a i * (x i : ℤ) ≡ c [ZMOD m])` (`m : ℕ`).
* `stablyComputable_remainder` (**Lemma 5(2)**): `0 < m → StablyComputable (remainder a c m)`.

`Crn/StableSemilinear.lean` (imports `Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic`)
* `IsSemilinearPred` (inductive): `threshold a c`, `remainder a c m` with `0 < m`, closed under
  `!`, `&&`, `||`. Defined as Boolean combinations (per the job); see Deviation 6.
* `IsSemilinearPred.isSemilinearSet`: `IsSemilinearPred φ → IsSemilinearSet {x | φ x = true}`
  (Mathlib's semilinear sets; Presburger-definable by `presburger.definable_iff_isSemilinearSet`).
* `IsSemilinearPred.stablyComputable` (**CRN-3, Theorem 5**): `IsSemilinearPred φ →
  StablyComputable φ`.

`Crn/StableCrn.lean` (reuses CRN-1's `Counts`, `Reaction`, `Network`, `Counts.react`, `consumed`)
* `Counts.map f x`: pushforward of count vectors, `(x.map f) a = ∑_{i, f i = a} x i` (the proof
  obligation is discharged by `Finset.sum_fiberwise`).
* `Network.Step N x y`: `∃ r ∈ N.reactions, (∀ a, r.consumed a ≤ x.1 a) ∧ y = x.react r`.
* `Network.Reaches N := Relation.ReflTransGen N.Step`.
* `Network.OutputStable N O b y`: in every count vector reachable from `y`, every present species
  (`z.1 a ≠ 0`) has `O a = b`.
* `Network.StablyComputes N I O φ` (`I : X ↪ S`, `O : S → Bool`): for all `n > 0`, all
  `x : Counts X n`, every `y` reachable from `x.map I` reaches an output-stable `z` with output
  `φ x.1`.
* `Protocol.exists_network` (**transfer**): if some transition changes the multiset,
  `∃ p q, s(p, q) ≠ s(δ₁(p, q), δ₂(p, q))`, there is `N : Network Q` whose reactions are exactly
  the `r` with `r.reactants ≠ r.products` and `r.reactants = s(p, q)`,
  `r.products = s(δ₁(p, q), δ₂(p, q))` for some `p, q`, and for all `n`, `c : Fin n → Q`, `y`:
  `N.Reaches (counts c) y ↔ ∃ c', P.Reaches c c' ∧ counts c' = y`.
* `StablyComputable.exists_network`: a stably computable `φ` is stably decided by some
  `N : Network S` (`S : Type`, finite, decidable equality) with injective `I` and some `O`.
* `IsSemilinearPred.exists_network` (**CRN-3 for CRNs**): the same for semilinear `φ`.

## Sanity checks done in phase 1

* Lean (`/tmp/crn3check/Check.lean`, outside the repo): `#check` of every statement (no stray
  instance arguments: `threshold`, `remainder`, `IsSemilinearPred` need only `[Fintype X]`;
  constructors refer to `Crn.threshold`/`Crn.remainder`; the `∃ (_ : Fintype S)` binders are used
  as instances); `decide` evaluations: `interact` gives `δ₁` to the initiator and `δ₂` to the
  responder in both orientations, values of `threshold`/`remainder`, and `Counts.map`.
* Python brute force (`/tmp/crn3check/check.py`, exact, multisets of states, which is exact for
  the complete interaction graph): the reachability-form `StablyComputes` decided on the full
  reachable graph.
  - AADFP06's threshold and remainder protocols with the **fixed input map** (Deviation 2):
    40 random instances each (`|aᵢ|, |c| ≤ 3`, `1 ≤ m ≤ 4`, one or two input symbols), every input
    with `n ≤ 5` (resp. `n ≤ 4`): no failure.
  - Negative controls: AADFP06's literal input map `σᵢ ↦ (1, 0, aᵢ)` fails at `n = 1`
    (`a = (1)`, `c = 3`, `x = (1)`) and is correct for `2 ≤ n ≤ 5`; a wrong predicate is rejected.
  - Product construction (Lemma 3) for all 16 Boolean `ξ` on threshold × remainder protocols,
    `n ≤ 3`: no failure.
  - Transfer: 200 random protocols (1–3 states, many trivial transitions), all configurations
    with `n ≤ 4`: CRN-reachable counts (reactions = multiset-changing transitions) equal the
    counts of protocol-reachable configurations.

## Proved

All 13 pinned theorems. New helper files (not pinned; 1638 lines in all 13 `Stable*.lean`):

`Crn/StableInteract.lean` (119 lines; generic, reusable for any protocol)
* `interact_apply`, `interact_fst`, `interact_snd`, `interact_of_ne`, `interact_eq_self`.
* `Reaches.refl/trans/tail`, `Step.reaches`, `reaches_interact`, `Reaches.invariant` (a
  step-closed property holds along paths), `OutputStable.reaches`,
  `outputStable_of_invariant` (a step-closed property under which all agents output `b`).
* `sum_add_pair`: `∑ G' + (G u + G v) = ∑ G + (G' u + G' v)` when only `u ≠ v` change (used for
  value sums, potentials and counts); `add_le_sum_pair`.
* `sum_comp_eq_sum_counts`: `∑_w F(ι w) = ∑_i (counts ι)ᵢ • F i`.

`Crn/StableProduct.lean` (118): `Protocol.prod` (parallel composition), `prod_interact_fst/snd`,
`reaches_fst/snd` (projection), `lift_fst/snd` (lifting a component's path with the same
encounters), `prod_stablyComputes` (**Lemma 3**). `map₂`, `not`, `and`, `or` are one-liners.

`Crn/StableLeader.lean` (398): the generic **leader protocol** (state = leader bit, output bit,
value; leader encounters give `q(u, u')` to the initiator and `r(u, u')` to the responder, both
outputs `t(q)`), shared by threshold and remainder.
* Step analysis: `interact_of_not`, `interact_fst`, `interact_snd`, `step_cases`.
* Invariants: `LeadOut`, `HasLeader`, `AtMostOne`, `NonLeaderVal` with their `_step` and
  `_input` lemmas; `sum_step` (weighted value sums conserved if `F q + F r = F u + F u'`),
  `sum_input`.
* `exists_reaches_atMostOne` (merge leaders, strong induction on their number);
  `pot`, `pot_interact_lt`, `exists_reaches_noImprove` (descent of `∑ μ` over non-leaders).
* `Good t L R` (one leader holding `L`, non-leaders satisfying `R`) with `Good.merge`,
  `Good.step` (closure, given `q(L, y) = q(y, L) = L`, `r(L, y) = r(y, L) = y` for `R y`),
  `Good.out_step`, `Good.out_snd`, `Good.exists_allOut` (broadcast, `Finset` induction) and
  `Good.exists_outputStable`.

`Crn/StableThresholdProtocol.lean` (178): values `{u : ℤ // -s ≤ u ∧ u ≤ s}`,
`s = |c| + 1 + ∑|aᵢ|`, `q` = clamped sum, `r` = rest, `t u = [u < c]`; `classify` (no improving
encounter ⇒ AADFP06's three stable shapes, by `omega`), `merge_zero/top/bot`, and
`stablyComputes` (**Lemma 5(1)**: merge, descent of `∑|u|`, case split on the leader's value).

`Crn/StableRemainderProtocol.lean` (81): values in `ZMod m`, `q = +`, `r = 0`, `t u = [u = c]`;
`stablyComputes` (**Lemma 5(2)**: merge; the leader holds the sum; `ZMod.intCast_eq_intCast_iff`).

`Crn/StableSemilinearSet.lean` (90): `linForm`, `isSemilinearSet_linEq` (Mathlib's
`isSemilinearSet_setOf_eq`), `sum_mul_eq_sub` (positive/negative parts),
`isSemilinearSet_threshold` (one slack variable, `IsSemilinearSet.proj`),
`isSemilinearSet_remainder` (two multipliers of `m`, `linear_combination`). Boolean cases:
`compl` (needs `AddMonoid.FG (X → ℕ)`, inferred), `inter`, `union`.

`Crn/StableTransfer.lean` (162): `count_mk`, `Protocol.reactionOf`; `counts_interact_add`
(`counts' + consumed = counts + produced`), `consumed_le_counts`, `counts_interact` (an encounter
is the reaction of its transition), `counts_interact_of_trivial`, `exists_agentPair` (an
applicable reaction comes from two distinct agents); input tagging `Protocol.untag`,
`Protocol.tagInputs` (states `Fin |X| ⊕ Q`, injective input), `untag_interact`, `reaches_untag`,
`lift_untag`, `tagInputs_stablyComputes`, `tagInputs_nontrivial`.

`Crn/StableCrn.lean`: `counts_comp` (`counts (f ∘ ι) = (counts ι).map f`). Proofs:
`Protocol.exists_network` (reactions = multiset-changing transitions; both directions by
induction on paths with `counts_interact`/`exists_agentPair`); `StablyComputable.exists_network`
(tag the inputs, transfer, read output-stability off the counts: a present species is some
agent's state; an empty input alphabet is handled by a dummy network on `Bool`).

## Remaining

Nothing for CRN-3 (easy direction). Possible extensions (not pinned): the equivalence of the
reachability form with AADFP06's fair executions (via their Lemma 1); the converse inclusion
`IsSemilinearSet → IsSemilinearPred` (Presburger's quantifier elimination, AADFP06 Theorem 4),
which would give "every semilinear predicate is stably computable" for Mathlib's semilinear sets;
the converse of CRN-3 (Angluin–Aspnes–Eisenstat 2006, research-level); README/blueprint, CI
wiring (by hand).

## Errors

None open. Phase 1: a scratch-test typo only. Phase 2 (all fixed): `simp` rewrites
`(a || b) = true` into a disjunction before using such a hypothesis (use `simp only` with
`↓reduceIte`); `set` re-typed a configuration variable (`C✝`) and broke `rw` patterns (replaced
by `obtain ⟨T, hT⟩ : ∃ T, … = T`); `omega` atoms differing by a `let`-bound encounter or a
beta-redex (`set … with`, `dsimp only`); `Good` does not mention `q`, `r`, so they must be passed
explicitly to `Good.exists_outputStable`; inconsistent cast normal forms before
`linear_combination` (`push_cast` first); a sign error in the remainder witnesses (`k⁺`/`k⁻`
swapped); `counts_comp` had to move after the pinned `Counts.map`.

## Deviations from the paper

1. **Stable computation in reachability form**, not with fair executions [AADFP06, §3.2], as
   the job requires (the form of [AAER07] and [CDS14, §2.2]). For finite populations both are
   equivalent (via AADFP06 Lemma 1: the configurations occurring infinitely often in a fair
   execution form a final strongly connected component); this equivalence is not pinned.
2. **Populations of every size `n ≥ 1`** (the job's "nonempty population"). AADFP06 do not state
   a lower bound, but their Lemma 5 protocols start with output bit `0` (`σᵢ ↦ (1, 0, aᵢ)`), which
   is wrong for `n = 1` when the predicate holds (brute-force counterexample above), so the paper
   implicitly assumes `n ≥ 2`. The pinned theorems are existential in the protocol and remain
   true: phase 2 must initialise the output bit to the single-agent value (`[aᵢ < c]`,
   `[aᵢ ≡ c (mod m)]`), which the brute force confirms. `n = 0` is excluded, as usual (no agent,
   no output).
3. **Scope**: predicates only (output alphabet `Bool`, all-agents predicate output convention),
   standard populations (complete interaction graph on `Fin n`), symbol-count input convention.
   Not covered: general interaction graphs, input-output relations and functions, other output
   conventions (AADFP06 Theorem 2), the integer-based input convention (Corollary 3).
4. **Threshold direction**: AADFP06 Lemma 5(1) is `∑ aᵢ xᵢ < c` (pinned as
   `stablyComputable_threshold`, and the atom of `IsSemilinearPred`); the roadmap's
   `∑ aᵢ xᵢ ≥ c` is its negation, pinned separately as `stablyComputable_le_sum`.
5. **Remainder modulus**: `0 < m` instead of AADFP06's `m ≥ 2` (a slight strengthening: `m = 1`
   gives the constant `true`), the natural hypothesis for `Int.ModEq`.
6. **Theorem 5 for an inductive class.** AADFP06 Theorem 5 concerns Presburger-definable
   predicates and its proof reduces them, by Presburger's quantifier elimination (their Theorem
   4, cited without proof), to Boolean combinations of threshold, equality and remainder
   predicates. As the job allows, `IsSemilinearPred` is defined as the Boolean combinations of
   threshold and remainder predicates (equalities are conjunctions of two thresholds, as in the
   paper's proof). The equality of this class with the semilinear / Presburger-definable
   predicates is not proved; added instead: the inclusion `IsSemilinearPred.isSemilinearSet` into
   Mathlib's `IsSemilinearSet` (Mathlib already proves `presburger.definable_iff_isSemilinearSet`,
   Ginsburg–Spanier), which checks that the class is not too large and ties it to Mathlib.
7. **Configurations are agent-level** (`Fin n → Q`, as AADFP06's `C : A → Q` and CRN-1's
   configurations), not multisets; count vectors enter through `counts` in the predicate and in
   the transfer, where `Protocol.exists_network` shows that the induced dynamics on count vectors
   is a CRN's.
8. **Transfer hypothesis.** CRN-1's `Network` is nonempty and has no reaction with
   `reactants = products`, so `Protocol.exists_network` assumes a transition that changes the
   multiset of states (otherwise the counts never change and there is no CRN in CRN-1's sense).
   It is stated for every protocol (stable computation plays no role) and existentially, with
   the reaction set characterised exactly.
9. **CRN-level stable decision (addition).** The job asks only for the reachability transfer; to
   make the roadmap's "hence by count-conserving CRNs" a theorem, `Network.StablyComputes`
   pins [CDS14, §2.2]'s chemical reaction deciders with every species voting (`Υ = Λ`, the
   convention of [AAE06]), no initial context (`σ = 0`, leaderless) and input species given by an
   injective `I : X ↪ S`; the zero input is excluded (`n > 0`: with no molecule the output
   `Φ` is undefined in [CDS14]). Proved via the transfer (plan item 8).
10. **Sanity theorem (addition).** `Protocol.StablyComputes.unique` shows that the definition is
    not vacuous (it determines the predicate on nonzero inputs).
