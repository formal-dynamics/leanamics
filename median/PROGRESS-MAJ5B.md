# MAJ-5B: two-sample voting on expanders with a small imbalance (Theorem 2)

Source: Cooper, Elsässer and Radzik, *The power of two choices in distributed voting*
(ICALP 2014, arXiv:1404.7479). Theorem, lemma, corollary and equation names follow the arXiv
version (Theorem 2 is the theorem labelled `Th1-expanders`, Lemma 2 is `lemMethod2-new`,
Lemma 3 is the expander mixing lemma, Corollary 2 is `lemMethod2-expanders`, Theorem 4 is
`phaseIIandIII-expander`). Part (a) of roadmap MAJ-5 (Theorem 4) is in `Median/Expander*.lean`
and is reused here unchanged: the model (`graphStep`, `graphRun`, `minority`), the spectral
quantity `lambdaG`, the mixing lemma `expander_mixing` and Theorem 4
(`two_choices_expander_explicit`).

## Status

Pinning phase done. The build succeeds with only `declaration uses 'sorry'` warnings.

* Proved: `majority_add_minority`, `minority_add_gainCount`, `mixingProp_of_lambdaG`,
  `growth_small`, `growth_large`, `phaseI_expander` (from `phaseI`), the `*_spec` theorems.
* Remaining (`sorry`): `expected_gain_ge`, `expected_loss_le`, `gain_tail`, `loss_tail`,
  `phaseI_step`, `phaseI`, `two_choices_expander_general_explicit`,
  `two_choices_expander_general`.
* `Audit.lean` has a `#print axioms` line for every pinned theorem (they report `sorryAx`
  until proved).

## Files

* `Median/ExpanderGeneralDefs.lean`: definitions and small lemmas.
* `Median/ExpanderGeneralPhaseI.lean`: Phase I (Lemma 2 and Corollary 2).
* `Median/ExpanderGeneral.lean`: Theorem 2.

All declarations are in the namespace `Median.ExpanderGeneral`.

## Pinned statements in words

Notation: `n = |V|`, `a` the majority opinion, `A = majority a x`, `B = minority a x`,
`ν = imbalance a x = (A − B)/n`, `η = phaseEta α a x = α n / √(A B)`,
`Δ_{BA} = gainCount a x y` (vertices of `B` that hold `a` after the round),
`Δ_{AB} = lossCount a x y` (vertices of `A` that no longer hold `a`).

Definitions (`ExpanderGeneralDefs.lean`):

* `majority`, `imbalance`, `phaseEta`, `gainCount`, `lossCount` as above;
  `majority_add_minority` (`A + B = n`) and `minority_add_gainCount`
  (`B' + Δ_{BA} = B + Δ_{AB}`) are proved.
* `MixingProp G d α c`: the hypothesis (mixing-prop) of Lemma 2: for disjoint `X`, `Y` with
  `|Y| ≥ c n` and `|X| ≥ (2/3) α c^{3/2} n`, `|E(X, Y) − d |X| |Y| / n| ≤ α d √(|X| |Y|)`.
  `mixingProp_of_lambdaG` (proved): `λ_G ≤ α` implies it (Lemma 3).
* `phaseIRounds ν c = ⌈log_{5/4} (1/(2ν))⌉ + ⌈log_{4/3} (1/(4c))⌉`, the length of Phase I.
* `*_spec` (proved by `rfl`): the defining equations of the definitions above and of those of
  part (a) that the statements use (`med3`, `minority`, `edgeCount`, `GraphRound`,
  `graphStep`, `graphRun`, `transitionMatrix`, `walkEigenvalues`, `lambdaG`). They are
  pinned so that the statements keep their meaning: the pinned text of a definition stops
  at `:=` and does not include its body.

Phase I (`ExpanderGeneralPhaseI.lean`). The one-round lemmas assume `d > 0`, `G` `d`-regular,
`0 < c ≤ 1/2`, `0 < α ≤ c √c / 36`, `MixingProp G d α c`, `c n ≤ B` and `B ≤ A`.

* `expected_gain_ge` (proof of Lemma 2, (hjre21)-(be56sw)):
  `𝔼 Δ_{BA} ≥ (A² B / n²)(1 − 2η)`.
* `expected_loss_le` (proof of Lemma 2, (eq-upperOnDAB)): `𝔼 Δ_{AB} ≤ (A B² / n²)(1 + 15η)`.
* `gain_tail` (proof of Lemma 2, (eq-fger)):
  `P(Δ_{BA} ≤ (A² B / n²)(1 − 3η)) ≤ e^{−α² c n / 6}`.
* `loss_tail` (proof of Lemma 2, (eq-fger2)):
  `P(Δ_{AB} ≥ (A B² / n²)(1 + 17η)) ≤ e^{−α² c² n / 2}`.
* `phaseI_step` ((bchwc), (ncnwd-Appx)):
  `P(ν' ≥ ν + ν(1 − ν²)/2 − 12α/√(1 − ν²)) ≥ 1 − e^{−α² c n / 6} − e^{−α² c² n / 2}`.
* `growth_small` (after (ncnwd-Appx)): if `120 α ≤ ν ≤ 1/2` then `ν' ≥ (5/4) ν`
  (deterministic).
* `growth_large` ((ncnwd-Appx334x)): if `1/2 ≤ ν ≤ 1 − 2c` then `1 − ν' ≤ (3/4)(1 − ν)`
  (deterministic).
* `phaseI` (Lemma 2): if `ν₀ ≥ 120 α`, then within `T₁ = phaseIRounds ν₀ c` rounds the
  minority is at most `c n` at some time `t ≤ T₁`, except with probability
  `T₁ (e^{−α² c n / 6} + e^{−α² c² n / 2})`.
* `phaseI_expander` (Corollary 2): `phaseI` with `λ_G ≤ α` in place of `MixingProp`.

Theorem 2 (`ExpanderGeneral.lean`):

* `two_choices_expander_general_explicit`: if `ν₀ > 0` and `4000 λ_G ≤ ν₀`, then for every
  `T₂`, after `T₁ + T₂` rounds (`T₁ = phaseIRounds ν₀ (1/20)`) every vertex holds `a`, except
  with probability at most
  `T₁ (e^{−α² n / 120} + e^{−α² n / 800}) + (24/25)^{T₂} n + (T₁ + T₂) e^{−n / 97000}`,
  with `α = ν₀ / 4000` (the first term is Phase I with `c = 1/20`; the other two are
  Theorem 4 with `ε = 1/4`).
* `two_choices_expander_general`: there are absolute constants `K, C > 0` such that on every
  `d`-regular graph with `d > 0`, if `K λ_G ≤ ν₀`, then after `⌈C log n⌉` rounds every vertex
  holds `a`, except with probability at most `1/n + (2 C log n + C) e^{−ν₀² n / C}`.

## Deviations from the source

1. **Theorem 2 needs a major correction for very small `λ_G`.** The paper claims success with
   high probability ("probability tending to 1 as `n` increases", footnote in Section 2)
   whenever `ν₀ ≥ K λ_G`, for "an `n`-vertex `d`-regular graph" and "an absolute constant `K`
   (independent of `d` and `λ_G`)" (the abstract: "for any regular graph"). Its proof goes
   through Corollary 2, whose success probability is only `1 − e^{−Θ(λ² n)}`: Lemma 2 assumes
   `α² c² n = Ω(n^ε)`, which the proof of Corollary 2 does not check when it takes `α = λ`,
   and Section 7 does not state a probability for Phase I. When `λ_G` is of order `1/√n` or
   smaller this is not `1 − o(1)`, and the printed statement does not hold: on the complete
   graph `λ_G = 1/(n − 1)`, so `A − B = K + 2` (a constant) satisfies `ν₀ ≥ K λ_G`; the first
   round already produces fluctuations of order `√n` in `A − B`, and by the symmetry between
   the two opinions the initial majority then wins with probability tending to `1/2` (with
   `A − B` of order `√n` it still loses with probability bounded away from `0`). Since
   `λ_G² ≥ (n − d)/(d (n − 1))` (the trace of `P²`), this regime only concerns dense graphs
   (`d` of order `n`). The formal theorem applies Phase I with `α = ν₀ / K ≥ λ_G` instead of
   `α = λ_G`, which gives the failure probability `(2 C log n + C) e^{−ν₀² n / C}` (plus
   `1/n`): it tends to `0` once `ν₀² n` is large compared with `log log n` (for example, for
   any fixed `ν₀ > 0`, or whenever `λ_G ≥ n^{−1/2+ε}`, the regime of Lemma 2).
2. **Explicit constants.** `K = 120` in Lemma 2, `K = 4000` and `c = 1/20` in the explicit form
   of Theorem 2. "With high probability" is the explicit failure bound above. The number of
   rounds `phaseIRounds` is the paper's `⌈log_{5/4}(1/(2ν₀))⌉ + ⌈log_{4/3}(1/(4c))⌉`.
3. **Assembly of the phases.** The paper combines Corollary 2 (with `c = 1/10`), Lemma 6 and
   Corollary 5 (Phases II and III, with `λ_G ≤ 1/6`). Here Phases II and III are Theorem 4 as
   formalized in part (a) (`two_choices_expander_explicit`, one supermartingale argument),
   applied with `ε = 1/4`, which needs `λ_G ≤ 7/20` and a minority of at most `n/20`; hence
   Phase I runs down to `c = 1/20`.
4. **Lemma 2 in "hitting" form.** The paper says that the minority "decreases to `c n` within
   `K' (log(1/ν₀) + log(1/c))` steps". `phaseI` states that at some time `t ≤ T₁` the minority
   is at most `c n` (`∃ t ≤ T₁` over prefixes `l.take t` of the rounds). The graph is not
   assumed connected (the paper's Lemma 2 assumes it, but the proof does not use it), and
   the condition `α² c² n = Ω(n^ε)` is replaced by the explicit failure bound.
5. **Concentration with mean bounds.** `gain_tail` and `loss_tail` use Chernoff bounds with a
   lower (respectively upper) bound on the mean (`avg_chernoff_lower`, `avg_chernoff_upper`);
   the paper's lower bound `𝔼 Δ_{AB} ≥ c² n / 4` used for (eq-fger2) is not needed.
6. **Model.** As in part (a): sampling with replacement, no adversary redistributing the
   opinions between rounds, and Boolean opinions with `a` the majority (the hypothesis
   `K λ_G ≤ ν₀` with `λ_G ≥ 0` forces `ν₀ ≥ 0`).
7. **Not formalized.** Theorem 1, Corollary 1 and Theorem 3 (random regular graphs, which need
   the configuration model) and the robustness Corollary 6 (`robustness`).
