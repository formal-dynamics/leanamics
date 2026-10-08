import Epidemics.Revisited.ProtocolsAux

/-! # The push, pull and push–pull protocols on the complete graph (EPI-8, instances)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), Appendix C of the long version (Theorems 51, 52 and 53).

In one round every node calls a node chosen uniformly at random among all `n` nodes,
independently; following the paper's convention for complete graphs, a node may call itself.
The calls of a round are a uniform function `c : Fin n → Fin n` (`calls n`); the
definitions are in `ProtocolsDefs`.

* **push**: every informed node sends the rumor to the node it calls;
* **pull**: every uninformed node that calls an informed node becomes informed;
* **push–pull**: both, so a node becomes informed if it calls an informed node or is called by
  one.

The per-state quantities of the general theory are computed exactly: with `k = |S|` informed
nodes, an uninformed node becomes informed with probability `1 - (1 - 1/n)^k` (push), `k / n`
(pull) and `1 - (1 - 1/n)^k (1 - k/n)` (push–pull); the three protocols are homogeneous; the
events that two distinct uninformed nodes become informed are nonpositively correlated (and
independent for pull). From these, the conditions of the general upper bounds hold with
explicit constants.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-! ### Exact one-round probabilities -/

/-- Push: an uninformed node is informed with probability `p_k = 1 - (1 - 1/n)^k`. -/
theorem push_informProb {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    (push n).informProb S x = 1 - (1 - 1 / (n : ℝ)) ^ S.card := by
  exact push_informProb_proof hx

/-- Pull: an uninformed node is informed with probability `p_k = k / n`. -/
theorem pull_informProb {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    (pull n).informProb S x = S.card / (n : ℝ) := by
  exact pull_informProb_proof hx

/-- Push–pull: an uninformed node is informed with probability
`p_k = 1 - (1 - 1/n)^k (1 - k/n)`. -/
theorem pushPull_informProb {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    (pushPull n).informProb S x = 1 - (1 - 1 / (n : ℝ)) ^ S.card * (1 - S.card / (n : ℝ)) := by
  exact pushPull_informProb_proof hx

theorem push_homogeneous :
    (push n).Homogeneous (fun k => 1 - (1 - 1 / (n : ℝ)) ^ k) :=
  fun _ _ hx => push_informProb hx

theorem pull_homogeneous :
    (pull n).Homogeneous (fun k => k / (n : ℝ)) :=
  fun _ _ hx => pull_informProb hx

theorem pushPull_homogeneous :
    (pushPull n).Homogeneous (fun k => 1 - (1 - 1 / (n : ℝ)) ^ k * (1 - k / (n : ℝ))) :=
  fun _ _ hx => pushPull_informProb hx

/-- Push: two distinct uninformed nodes are informed nonpositively correlated. -/
theorem push_cov_nonpos {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) : (push n).cov S x y ≤ 0 := by
  exact push_cov_nonpos_proof hx hy hxy

/-- Pull: two distinct uninformed nodes are informed independently. -/
theorem pull_cov_eq_zero {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) : (pull n).cov S x y = 0 := by
  exact pull_cov_eq_zero_proof hx hy hxy

/-- Push–pull: two distinct uninformed nodes are informed nonpositively correlated. -/
theorem pushPull_cov_nonpos {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) : (pushPull n).cov S x y ≤ 0 := by
  exact pushPull_cov_nonpos_proof hx hy hxy

/-! ### The conditions of the general upper bounds, with explicit constants -/

/-- Push satisfies the upper exponential growth conditions in `[1, n/2[` with `γ = 1`,
`a = 1/2`, `b = c = 0`: `p_k ≥ (k/n)(1 - k/(2n))`. -/
theorem push_upperGrowth : (push n).UpperGrowth 1 (1 / 2) 0 0 (1 / 2) := by
  exact push_upperGrowth_proof

/-- Push satisfies the upper exponential shrinking conditions from `n/2` uninformed nodes on,
with `ρ = 1`, `a = 2/e`, `c = 0`: `1 - p_{n-u} = (1 - 1/n)^{n-u} ≤ e^{-1} + (2/e)(u/n)`. -/
theorem push_upperShrinking : (push n).UpperShrinking 1 (2 / Real.exp 1) 0 (1 / 2) := by
  exact push_upperShrinking_proof

/-- Pull satisfies the upper exponential growth conditions in `[1, n/2[` with `γ = 1`,
`a = b = c = 0`: `p_k = k/n`. -/
theorem pull_upperGrowth : (pull n).UpperGrowth 1 0 0 0 (1 / 2) := by
  exact pull_upperGrowth_proof

/-- Pull satisfies the upper double exponential shrinking conditions with `ℓ = 2`, `a = 1`,
`c = 0`, `g = 1/2`, `α = 1/2`: `1 - p_{n-u} = u/n`. -/
theorem pull_upperDoubleShrinking : (pull n).UpperDoubleShrinking 2 1 0 (1 / 2) (1 / 2) := by
  exact pull_upperDoubleShrinking_proof

/-- Pull finishes fast below `√n` uninformed nodes: `1 - p_{n-u} = u/n ≤ n^{-1/2}`. -/
theorem pull_fastFinishing : (pull n).FastFinishing (1 / 2) (1 / 2) := by
  exact pull_fastFinishing_proof

/-- Push–pull satisfies the upper exponential growth conditions in `[1, n/2[` with `γ = 2`,
`a = 3/4`, `b = c = 0`: `p_k ≥ 2(k/n)(1 - 3k/(4n))`. -/
theorem pushPull_upperGrowth : (pushPull n).UpperGrowth 2 (3 / 4) 0 0 (1 / 2) := by
  exact pushPull_upperGrowth_proof

/-- Push–pull satisfies the upper double exponential shrinking conditions with `ℓ = 2`,
`a = 1`, `c = 0`, `g = 1/2`, `α = 1/2`: `1 - p_{n-u} = (u/n)(1 - 1/n)^{n-u} ≤ u/n`. -/
theorem pushPull_upperDoubleShrinking :
    (pushPull n).UpperDoubleShrinking 2 1 0 (1 / 2) (1 / 2) := by
  exact pushPull_upperDoubleShrinking_proof

/-- Push–pull finishes fast below `√n` uninformed nodes: `1 - p_{n-u} ≤ u/n ≤ n^{-1/2}`. -/
theorem pushPull_fastFinishing : (pushPull n).FastFinishing (1 / 2) (1 / 2) := by
  exact pushPull_fastFinishing_proof

end Epidemics.Revisited
