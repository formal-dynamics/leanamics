import RumorSpread.Model
import Dynamics.Uniform
import RumorSpread.PullFoldl

/-!
# PULL and PUSH–PULL rumor spreading on the complete graph

The random phone call model of Karp, Schindelhauer, Shenker and Vöcking [KSSV00, §1.2]: in
every round each node `v` calls a random partner `r v`, and the rumor may travel along the call
in either direction. We reuse the round configurations `Tgt n` of the PUSH development
(`Model.lean`: every node calls a uniformly random *other* node, as in [FG85]), so that the three
protocols are driven by the same random calls:

* PUSH (`step`, in `Model.lean`): an informed caller informs its callee;
* PULL (`pullStep`): an uninformed caller learns the rumor if its callee is informed;
* PUSH–PULL (`pushPullStep`): the rumor is sent in both directions along every call
  [KSSV00, §2].

`pullRun` and `pushPullRun` consume a list of rounds head first (as `run` does), and
`prPullNotAllInformed`, `prPushPullNotAllInformed` are the probabilities that some node is still
uninformed after `T` i.i.d. uniform rounds started from a single informed node, in the same
`expList` form as `prNotAllInformed` for PUSH.

Because the three steps read the same calls, PUSH–PULL dominates PUSH and PULL pathwise
(`run_subset_pushPullRun`, `pullRun_subset_pushPullRun`).

## References

* [KSSV00] R. Karp, C. Schindelhauer, S. Shenker, B. Vöcking, *Randomized rumor spreading*,
  FOCS 2000.
* [FG85] A. M. Frieze, G. R. Grimmett, *The shortest-path problem for graphs with random
  arc-lengths*, Discrete Appl. Math. 10 (1985).
-/

namespace RumorPush

open Finset Dynamics

variable {n : ℕ}

/-- One PULL round [KSSV00, §1.2 and §2]: every node `v` calls `r v`, and an uninformed caller
becomes informed if its callee is informed. -/
def pullStep (I : Finset (Fin n)) (r : Tgt n) : Finset (Fin n) :=
  I ∪ univ.filter fun v => ((r v) : Fin n) ∈ I

/-- The informed set after consuming the list `l` of PULL rounds (head first), starting from
the informed set `I`. -/
def pullRun (I : Finset (Fin n)) (l : List (Tgt n)) : Finset (Fin n) :=
  l.foldl pullStep I

/-- One PUSH–PULL round [KSSV00, §2]: along every call `v → r v` the rumor is transmitted in
both directions, so the new informed set is the union of the PUSH round `step` and the PULL
round `pullStep` driven by the same calls. -/
def pushPullStep (I : Finset (Fin n)) (r : Tgt n) : Finset (Fin n) :=
  step I r ∪ pullStep I r

/-- The informed set after consuming the list `l` of PUSH–PULL rounds (head first), starting
from the informed set `I`. -/
def pushPullRun (I : Finset (Fin n)) (l : List (Tgt n)) : Finset (Fin n) :=
  l.foldl pushPullStep I

/-- Probability that not all nodes are informed after `T` rounds of PULL, starting from the
single informed node `v₀`. -/
noncomputable def prPullNotAllInformed (n : ℕ) (v₀ : Fin n) (T : ℕ) : ℝ :=
  expList (Tgt n) T (fun l => if pullRun {v₀} l = univ then (0 : ℝ) else 1)

/-- Probability that not all nodes are informed after `T` rounds of PUSH–PULL, starting from
the single informed node `v₀`. -/
noncomputable def prPushPullNotAllInformed (n : ℕ) (v₀ : Fin n) (T : ℕ) : ℝ :=
  expList (Tgt n) T (fun l => if pushPullRun {v₀} l = univ then (0 : ℝ) else 1)

/-! ### Basic properties of the steps -/

lemma mem_pullStep {I : Finset (Fin n)} {r : Tgt n} {v : Fin n} :
    v ∈ pullStep I r ↔ v ∈ I ∨ ((r v) : Fin n) ∈ I := by
  simp [pullStep]

lemma mem_pushPullStep {I : Finset (Fin n)} {r : Tgt n} {v : Fin n} :
    v ∈ pushPullStep I r ↔ v ∈ step I r ∨ v ∈ pullStep I r := by
  simp [pushPullStep]

lemma subset_pullStep (I : Finset (Fin n)) (r : Tgt n) : I ⊆ pullStep I r :=
  subset_union_left

lemma step_subset_pushPullStep (I : Finset (Fin n)) (r : Tgt n) :
    step I r ⊆ pushPullStep I r :=
  subset_union_left

lemma pullStep_subset_pushPullStep (I : Finset (Fin n)) (r : Tgt n) :
    pullStep I r ⊆ pushPullStep I r :=
  subset_union_right

lemma subset_pushPullStep (I : Finset (Fin n)) (r : Tgt n) : I ⊆ pushPullStep I r :=
  (subset_step I r).trans (step_subset_pushPullStep I r)

lemma step_mono (r : Tgt n) : Monotone fun I : Finset (Fin n) => step I r :=
  fun _ _ h => union_subset_union h (image_subset_image h)

lemma pullStep_mono (r : Tgt n) : Monotone fun I : Finset (Fin n) => pullStep I r := by
  intro I J h v
  simp only [mem_pullStep]
  exact Or.imp (fun hv => h hv) (fun hv => h hv)

lemma pushPullStep_mono (r : Tgt n) : Monotone fun I : Finset (Fin n) => pushPullStep I r :=
  fun _ _ h => union_subset_union (step_mono r h) (pullStep_mono r h)

/-- The PUSH trajectory `run` is the `List.foldl` of `step`. -/
lemma run_eq_foldl (I : Finset (Fin n)) (l : List (Tgt n)) : run I l = l.foldl step I := by
  induction l generalizing I with
  | nil => rfl
  | cons r l ih => exact ih (step I r)

lemma subset_pullRun (I : Finset (Fin n)) (l : List (Tgt n)) : I ⊆ pullRun I l :=
  subset_foldl subset_pullStep I l

lemma subset_pushPullRun (I : Finset (Fin n)) (l : List (Tgt n)) : I ⊆ pushPullRun I l :=
  subset_foldl subset_pushPullStep I l

/-- **PUSH–PULL dominates PUSH pathwise**: driven by the same calls, PUSH–PULL has informed at
least the nodes informed by PUSH after every prefix of rounds. -/
theorem run_subset_pushPullRun (I : Finset (Fin n)) (l : List (Tgt n)) :
    run I l ⊆ pushPullRun I l := by
  rw [run_eq_foldl]
  exact foldl_subset_foldl step_subset_pushPullStep pushPullStep_mono I l

/-- **PUSH–PULL dominates PULL pathwise**: driven by the same calls, PUSH–PULL has informed at
least the nodes informed by PULL after every prefix of rounds. -/
theorem pullRun_subset_pushPullRun (I : Finset (Fin n)) (l : List (Tgt n)) :
    pullRun I l ⊆ pushPullRun I l :=
  foldl_subset_foldl pullStep_subset_pushPullStep pushPullStep_mono I l

end RumorPush
