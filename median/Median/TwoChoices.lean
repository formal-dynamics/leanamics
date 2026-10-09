import Median.TwoChoicesDefs
import Median.TwoChoicesExpect
import Median.TwoChoicesPlurality
import Median.TwoChoicesLower

/-! # The k-party 2-Choices dynamics

Every node samples two nodes uniformly at random (with replacement) and adopts their colour if
the two samples agree; with two colours this is the median dynamics (`TwoChoices.step_bool`).

* `Median/TwoChoicesDefs.lean`: the model, the bridge to `Median.step` on `Bool`, and the
  domination of a colour by the binary median process.
* `Median/TwoChoicesExpect.lean`: the one-round expectations (Elsässer et al., arXiv v5
  numbering: equation (1), Observation 2.1, the expected gap) and the aggregation of the
  minority colours.
* `Median/TwoChoicesPlurality.lean`: plurality consensus from a gap of order `√(n log n)` in
  `O((n/c₁) log n)` rounds (Elsässer et al., Lemmas 2.2 and 2.3 and Theorem 1.2;
  roadmap MAJ-4).
* `Median/TwoChoicesLower.lean`: the `Ω(n/log n)` lower bound from configurations with colours
  of `O(log n)` nodes (Berenbrink et al., PODC 2017,
  Theorem 5 of arXiv:1702.04921 v1; roadmap MAJ-6 (a)).
-/
