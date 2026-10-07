# EPI-2 progress: subcritical ⇒ small outbreaks

Source: [BCDPTZ22] Becchetti, Clementi, Denni, Pasquale, Trevisan, Ziccardi, *Percolation and
epidemic processes in one-dimensional small-world networks*, arXiv:2103.16398 (v3 source,
`trunk-full/regular_below.tex` and `OurResults-body.tex`). Theorem 2.3 (bounded-degree graphs,
§2.1) and Theorem E.1 (`thm:reg-infection-stops`, Appendix E "Regular graphs below the
threshold"), with its BFS / deferred-decision proof. The Reed–Frost corollary is the one the paper
mentions but omits after Theorem 2.5 ("we omit here the formal statement"); its shape follows
claim 2 of Theorems 2.4 and 2.5.

## Status

**Phase 1 (pin statements): done.**

**Phase 2 (proofs): done.** All 5 pinned theorems are proved. `lake build Epidemics` is
warning-free; the pinned text up to `:=` is unchanged (checked against the phase-1 commit); no
`sorry`/`admit`/`axiom`/`native_decide`/`set_option`; `#print axioms` of every pinned theorem
gives only `propext`, `Classical.choice`, `Quot.sound` (also `python3 ../scripts/check_axioms.py`,
12 declarations, with the 5 new theorems added to `Audit.lean`). README table and blueprint
section added.

## Pinned (frozen up to `:=`; see `PINNED.txt`)

All in `epidemics/Epidemics/Subcritical.lean`, namespace `Epidemics`. No new definitions: the
statements use EPI-1's `perc`, `coins`, `bernoulli`, `run` (`Epidemics/ReedFrost.lean`),
`Dynamics.Distribution.independent` / `prob`, and Mathlib's `SimpleGraph.degree`,
`ConnectedComponent.supp`, `Set.ncard` (Mathlib's own measure of component size, as in
`oddComponents`).

| Declaration | Content | Source |
| --- | --- | --- |
| `prob_cluster_gt_le_binomial` | degrees ≤ `d` ⇒ `P(|C(s)| > t) ≤ P(≥ t successes in t(d−1)+1 i.i.d. Bernoulli(p))` | proof of Thm E.1 (deferred decisions) |
| `prob_cluster_gt_le` | degrees ≤ `d`, `p(d−1) ≤ 1−ε`, `0<ε<1` ⇒ `P(|C(s)| > t) ≤ exp(ε − ε²t/2)` | Thm E.1, first part |
| `prob_components_small` | same hypotheses ⇒ w.p. `≥ 1 − 1/n` every component of `G_p` has `≤ (10/ε²) log n` vertices | Thm 2.3 = Thm E.1, second part |
| `reedFrost_subcritical` | same, with `R₀ = p(d−1) ≤ 1−ε` ⇒ w.p. `≥ 1 − 1/n` total infected `≤ |I₀|(10/ε²) log n` and no infected node in round `⌊(10/ε²) log n⌋` | omitted corollary after Thm 2.5 (cf. Thms 2.4/2.5 claim 2), via EPI-1 |
| `erdosRenyi_subcritical` | `c ≤ 1−ε` ⇒ w.p. `≥ 1 − 1/n` every component of `G(n, c/n)` (percolation of `⊤`) has `≤ (10/ε²) log n` vertices | Thm 2.3 for `K_n` (roadmap corollary) |

Not pinned (helper, may change): `binomial_tail_le` in `Epidemics/SubcriticalChernoff.lean`, the
local Chernoff bound `P(≥ t successes in t(d−1)+1 trials) ≤ exp(ε − ε²t/2)`.
**Candidate for replacement by FND-3** (weighted Chernoff on `Distribution` products) once it lands.

## Proved

Files (948 lines in total), in import order:

| File | Lines | Content |
| --- | --- | --- |
| `SubcriticalProb.lean` | 160 | finite-probability helpers: `prob_congr`, `prob_mono`, `prob_eq_one`, `prob_eq_zero`, `prob_add_prob_not`, union bound `prob_exists_le_sum`, Markov on an exponential moment `prob_le_expect_exp`, conditioning an independent product on one coordinate `independent_expect_update` (via `Equiv.funSplitAt`) or on the first coordinate of `Fin (m+1)` `independent_expect_fin_succ`, `bernoulli_expect`, `coins_prob_split` |
| `SubcriticalChernoff.lean` | 163 | `binTail` (binomial tail as a product probability) with `binTail_succ_succ`; `one_sub_mul_exp_le` (`(1-ε)e^ε ≤ 1-ε²/2`, from `dynamics`' `exp_le_one_add_add_sq_div`); `expect_exp_card_filter`; **`binomial_tail_le`** |
| `SubcriticalCluster.lean` | 149 | `reachSet H D` and its lemmas (closed sets, adding a neighbour, deleting edges inside `S`), `ncard_supp_eq_card_reachSet`, `dist_lt_ncard_supp`, `card_recovered_le`, `infected_eq_empty_of_ncard_le` |
| `SubcriticalExploration.lean` | 287 | `closeOff`, `frontier` and their lemmas; **`prob_reachSet_le_binTail`** (deferred decisions for every exploration state) and `prob_cluster_gt_le_binTail` |
| `SubcriticalWhp.lean` | 69 | `prob_components_le_of_tail` (union bound over component representatives), `card_mul_exp_le` (the constant `10/ε²`) |
| `Subcritical.lean` | 120 | the 5 pinned theorems, each a short proof from the helpers |

How the crux was proved (differs from the phase-1 plan B, which suggested an explicit
exploration/decision tree): no BFS and no queue. The induction is on a budget `m` over *states*
`(D, X)`: discovered set and examined pairs, with the coins of `X` forced closed (`closeOff`).
Claim: `frontier G D X + (k-1)(d-1) ≤ m ⇒ P(|D| + k ≤ |reach of D|) ≤ binTail m k`. Pick any
frontier edge `{w,x}`, condition on its coin (`coins_prob_split`); closed: `(D, X ∪ {wx})`,
frontier `-1`; open: `(D ∪ {x}, X ∪ {wx})` (the cluster is unchanged, `reachSet_update_true`),
frontier `+ (d-1) - 1`. That is exactly `binTail_succ_succ`. No padding of the coin sequence and
no stochastic-domination coupling are needed, and monotonicity in `m` is built into the budget.

Reusable pieces (candidates for `dynamics/`): everything in `SubcriticalProb.lean` (union bound,
Markov-exponential, the two conditioning lemmas), `binTail` + `binTail_succ_succ`, and the
Chernoff `binomial_tail_le`. **Candidate for replacement by FND-3** (weighted Chernoff on
`Distribution` products): `binomial_tail_le` / `expect_exp_card_filter` /
`prob_le_expect_exp`. They are kept in the `Epidemics` namespace (not `Dynamics.Distribution`) to
avoid name clashes when FND-3 lands.

## Remaining

Nothing for EPI-2. Optional follow-ups: move the `SubcriticalProb.lean` helpers to `dynamics/`;
replace the local Chernoff by FND-3's; human review of the statements (README marks them as not
yet reviewed).

## Errors / open issues

None: no pinned statement turned out false. Numerical sanity checks made before pinning (Python, `/tmp/epi2-check`, not part of the repo):
* the binomial tail `P(Bin(t(d−1)+1, (1−ε)/(d−1)) ≥ t) ≤ exp(ε − ε²t/2)` on a grid of
  `d ≤ 1000`, `ε ∈ [0.001, 0.999]`, `t ≤ 400`; also the degenerate `d ≤ 1`, `m = 1` cases;
* `prob_cluster_gt_le_binomial` by exact enumeration of all coin assignments on 30 small graphs
  (cycle, `K₄`, path, star, single edge, random), for `d ∈ {maxdeg, maxdeg+1, maxdeg+3}`, several
  `p`, all `s`, all `t ≤ n`: holds, with equality in some cases (e.g. star, `t = 1`);
* the union-bound constant `C = 10/ε²` for all `n ≥ 2`.

## Deviations from the paper

1. **Threshold written multiplicatively**: `p * ((d : ℝ) − 1) ≤ 1 − ε` instead of
   `p < (1−ε)/(d−1)` (Thm 2.3) or `p = (1−ε)/(d−1)` (Thm E.1). It covers both (the results are
   monotone in `p`), is equivalent to `p ≤ (1−ε)/(d−1)` for `d ≥ 2`, and avoids Lean's
   `x / 0 = 0` junk value at `d = 1`, where the paper's threshold is `+∞`: for `d = 1` any `p` is
   allowed and the statements stay true (components have at most 2 vertices). For `d = 0` the
   hypothesis is automatic and components are singletons.
2. **`ε < 1` assumed** (as in Thm E.1, `1 > ε > 0`; Thm 2.3 says "ε > 0 arbitrary"). For `ε ≥ 1`
   and `d ≥ 2` the hypothesis forces `p = 0`; an explicit `C/ε² · log n` bound would then be
   false for large `ε` (singletons vs a bound tending to 0), so nothing is lost.
3. **"Maximum degree `d`"** is the upper bound `∀ v, G.degree v ≤ d` (equivalent to
   `G.maxDegree ≤ d`); the paper's proof only uses the upper bound.
4. **Explicit tail constant**: `exp(ε − ε²t/2) = e^ε · exp(−ε²t/2)` for Theorem E.1's
   `exp(−Ω(ε²t))`. The paper's proof claims `exp(−ε²t/3)` "by Chernoff bounds", but the mean of
   its `t(d−1)+1` trials is `(1−ε)t + p`, not `(1−ε)t`: the extra trial at the source (degree `d`,
   not `d − 1`) is what the prefactor `e^ε ≤ e` pays for, and Markov on `exp(ε X)` yields this
   bound directly. Numerically, the paper's `exp(−ε²t/3)` also seems to hold for the binomial tail
   (grid `d < 60`, `t < 80`), but it is not what the standard argument proves, so it is not pinned.
5. **"W.h.p." made explicit**: probability at least `1 − 1/n` with `C_ε = 10/ε²`, for every
   `n = Fintype.card V` (no "n large enough"; for `n ≤ 1` the statement is trivial, and for `n = 0`
   Lean's `1/0 = 0` makes it claim probability 1, which holds since there are no components). The
   paper's union-bound sentence ("probability … at most `1 − 1/n²`") has a typo for `1/n²`.
6. **Deferred-decision step pinned as a probability comparison**: the paper's "we have observed at
   most `t(d−1)+1` Bernoulli random variables with parameter `p` and found that at least `t` of
   them were 1" is stated as `P(|C(s)| > t) ≤ P(≥ t successes among t(d−1)+1 i.i.d. Bernoulli(p))`
   with the product `Distribution.independent` over `Fin (t * (d − 1) + 1)` (ℕ subtraction: one
   trial when `d = 0`, still true). The paper's BFS (with a stray `y` for `x`) is replaced in the
   plan by any one-vertex-at-a-time exploration.
7. **Percolation model**: EPI-1's `coins` put one coin on every element of `Sym2 V` (non-edges and
   the diagonal included); only the coins of edges of `G` matter, so `perc G ω` has the law of
   `G_p`.
8. **Reed–Frost corollary**: the paper omits its formal statement for bounded-degree graphs. We
   take the shape of claim 2 of Theorems 2.4/2.5 ("stops within `O_ε(log n)` steps, `O_ε(|I₀| log n)`
   recovered nodes") with explicit constants, for EPI-1's pathwise process (one coin per edge,
   equivalent in law to Reed–Frost with transmission probability `p`). The reproduction number is
   `R₀ = p(d−1)` (an infected non-source node has at most `d − 1` susceptible neighbours), and
   "`R₀ < 1`" is quantified as `R₀ ≤ 1 − ε` with `0 < ε < 1`, which covers every `R₀ < 1`.
   "Stops within `T` rounds" is `(run G ω I₀ T).infected = ∅`; the total number of infected nodes
   is the final recovered set `(run G ω I₀ (Fintype.card V)).recovered`.
9. **Erdős–Rényi corollary** (from the roadmap row, not in the task's minimum): `G(n, c/n)` is
   `perc ⊤ ω` with `coins (c/n)`; the hypotheses `0 ≤ c/n ≤ 1` are needed to form the coins.
