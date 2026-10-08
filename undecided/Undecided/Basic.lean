import Dynamics.Rounds
import Dynamics.Absorption
import Mathlib

/-! # The undecided-state dynamics (synchronous, binary, complete graph)

Each of `n` nodes holds opinion `a`, opinion `b`, or is undecided (`u`). In every round each node
samples a node uniformly at random (with replacement, possibly itself): an undecided node adopts
the sampled opinion; a decided node that samples the other opinion becomes undecided; otherwise
nothing changes.

With `a`, `b`, `q` the numbers of `a`-, `b`- and undecided nodes, one round gives, in expectation,
`a (n - b + q) / n` nodes with opinion `a`, `(q² + 2 a b) / n` undecided nodes, and hence a bias
`(a - b)(1 + q / n)`: the undecided nodes amplify the current majority. Every run is eventually
absorbed in one of the three monochromatic configurations.
-/

namespace Undecided
open Finset Dynamics Filter Topology

/-- Opinions: `a`, `b`, or undecided. -/
inductive Op
  | a
  | b
  | u
  deriving DecidableEq, Fintype

/-- New state of a node holding `x` that samples a node holding `y`. -/
def update : Op → Op → Op
  | .u, y => y
  | x, .u => x
  | .a, .a => .a
  | .b, .b => .b
  | .a, .b => .u
  | .b, .a => .u

/-- Configurations of `n` nodes. -/
abbrev Config (n : ℕ) := Fin n → Op

variable {n : ℕ}

/-- One synchronous round: node `v` samples node `r v`. -/
def step (x : Config n) (r : Fin n → Fin n) : Config n := fun v => update (x v) (x (r v))

/-- Number of nodes in state `o`. -/
def count (x : Config n) (o : Op) : ℕ := (univ.filter fun v => x v = o).card

/-- All nodes are in the same state. -/
def Mono (x : Config n) : Prop := ∃ o, ∀ v, x v = o

/-- Indicator of not yet being monochromatic. -/
noncomputable def notMono (x : Config n) : ℝ := by
  classical
  exact if Mono x then 0 else 1

/-- A node holding `s` that samples `t` is `a` exactly when it was `a` and avoided `b`,
or it was undecided and sampled `a`. -/
lemma indicator_becomes_a (s t : Op) :
    (if update s t = .a then (1 : ℝ) else 0) =
      (if s = .a then (1 : ℝ) else 0) * (if t ≠ .b then (1 : ℝ) else 0) +
      (if s = .u then (1 : ℝ) else 0) * (if t = .a then (1 : ℝ) else 0) := by
  cases s <;> cases t <;> simp [update]

/-- A node holding `s` that samples `t` is `b` exactly when it was `b` and avoided `a`,
or it was undecided and sampled `b`. -/
lemma indicator_becomes_b (s t : Op) :
    (if update s t = .b then (1 : ℝ) else 0) =
      (if s = .b then (1 : ℝ) else 0) * (if t ≠ .a then (1 : ℝ) else 0) +
      (if s = .u then (1 : ℝ) else 0) * (if t = .b then (1 : ℝ) else 0) := by
  cases s <;> cases t <;> simp [update]

/-- A node is undecided after the update exactly in the three transitions of the dynamics. -/
lemma indicator_becomes_u (s t : Op) :
    (if update s t = .u then (1 : ℝ) else 0) =
      (if s = .u then (1 : ℝ) else 0) * (if t = .u then (1 : ℝ) else 0) +
      (if s = .a then (1 : ℝ) else 0) * (if t = .b then (1 : ℝ) else 0) +
      (if s = .b then (1 : ℝ) else 0) * (if t = .a then (1 : ℝ) else 0) := by
  cases s <;> cases t <;> simp [update]

lemma update_on_decided {o s : Op} (ho : o = .a ∨ o = .b) :
    update s o = o ∨ update s o = .u := by
  rcases ho with rfl | rfl <;> cases s <;> decide

lemma update_id_decided {o : Op} (ho : o = .a ∨ o = .b) : update o o = o := by
  rcases ho with rfl | rfl <;> rfl

lemma count_eq_sum (x : Config n) (o : Op) :
    (count x o : ℝ) = ∑ v : Fin n, if x v = o then (1 : ℝ) else 0 := by
  unfold count
  rw [card_filter]
  push_cast
  rfl

/-- The numbers of `a`-, `b`- and undecided nodes add up to `n`. -/
lemma count_add (x : Config n) : (count x .a : ℝ) + count x .b + count x .u = n := by
  rw [count_eq_sum, count_eq_sum, count_eq_sum, ← sum_add_distrib, ← sum_add_distrib]
  have h (v : Fin n) : ((if x v = .a then (1 : ℝ) else 0) + (if x v = .b then 1 else 0)
      + (if x v = .u then 1 else 0)) = 1 := by
    cases x v <;> simp
  rw [sum_congr rfl fun v _ => h v]
  simp

lemma indicator_step (x : Config n) (r : Fin n → Fin n) (v : Fin n) (o : Op) :
    (if step x r v = o then (1 : ℝ) else 0) =
      if update (x v) (x (r v)) = o then (1 : ℝ) else 0 := by
  unfold step
  rfl

lemma count_step_eq_sum (x : Config n) (r : Fin n → Fin n) (o : Op) :
    (count (step x r) o : ℝ) =
      ∑ v, if update (x v) (x (r v)) = o then (1 : ℝ) else 0 := by
  rw [count_eq_sum]
  exact sum_congr rfl fun v _ => indicator_step x r v o

lemma avg_indicator_eq (x : Config n) (o : Op) :
    avg (fun v : Fin n => if x v = o then (1 : ℝ) else 0) = (count x o : ℝ) / n := by
  rw [avg_indicator]
  simp [count, Fintype.card_fin]

lemma node_prob_u (x : Config n) (v : Fin n) :
    avg (fun w : Fin n => if update (x v) (x w) = .u then (1 : ℝ) else 0) =
      (if x v = .u then (1 : ℝ) else 0) * ((count x .u : ℝ) / n) +
        (if x v = .a then (1 : ℝ) else 0) * ((count x .b : ℝ) / n) +
        (if x v = .b then (1 : ℝ) else 0) * ((count x .a : ℝ) / n) := by
  simp_rw [indicator_becomes_u]
  rw [avg_add, avg_add, avg_const_mul, avg_const_mul, avg_const_mul]
  rw [avg_indicator_eq, avg_indicator_eq, avg_indicator_eq]

lemma notMono_binary (x : Config n) : notMono x = 0 ∨ notMono x = 1 := by
  unfold notMono
  split <;> simp

lemma notMono_le_one (x : Config n) : notMono x ≤ 1 := by
  unfold notMono
  split <;> norm_num

lemma notMono_of_mono (x : Config n) (h : Mono x) : notMono x = 0 := by
  unfold notMono
  exact if_pos h

lemma notMono_const (o : Op) : notMono (fun _ : Fin n => o) = 0 := by
  unfold notMono
  exact if_pos ⟨o, fun _ => rfl⟩

lemma exists_decided (x : Config n) (hx : ¬ Mono x) : ∃ w, x w = .a ∨ x w = .b := by
  by_contra h
  apply hx
  refine ⟨.u, fun v => ?_⟩
  have hv : x v ≠ .a ∧ x v ≠ .b := by
    refine ⟨?_, ?_⟩
    · intro ha
      exact h ⟨v, Or.inl ha⟩
    · intro hb
      exact h ⟨v, Or.inr hb⟩
  cases hxv : x v with
  | a => exact absurd hxv hv.1
  | b => exact absurd hxv hv.2
  | u => rfl

lemma step_towards (x : Config n) {w : Fin n} (hw : x w = .a ∨ x w = .b) (v : Fin n) :
    step x (fun _ => w) v = x w ∨ step x (fun _ => w) v = .u := by
  simpa [step] using update_on_decided (o := x w) (s := x v) hw

lemma step_towards_at (x : Config n) {w : Fin n} (hw : x w = .a ∨ x w = .b) :
    step x (fun _ => w) w = x w := by
  simpa [step] using update_id_decided (o := x w) hw

lemma step_clear (y : Config n) {w : Fin n} {o : Op} (ho : o = .a ∨ o = .b)
    (hmem : ∀ v, y v = o ∨ y v = .u) (hw : y w = o) :
    step y (fun _ => w) = fun _ => o := by
  funext v
  rw [step, hw]
  rcases hmem v with hv | hv
  · rw [hv, update_id_decided ho]
  · rw [hv]
    rcases ho with rfl | rfl <;> rfl

/-- If every node samples a decided node `w`, two such rounds make the configuration
monochromatic at `x w`. -/
lemma two_const_mono (x : Config n) {w : Fin n} (hw : x w = .a ∨ x w = .b) :
    step (step x (fun _ => w)) (fun _ => w) = fun _ => x w := by
  exact step_clear (step x (fun _ => w)) hw (fun v => step_towards x hw v) (step_towards_at x hw)

/-- On a nonempty finite type, an observable bounded by `1` and strictly below `1`
somewhere has average strictly below `1`. -/
lemma avg_lt_one {α : Type*} [Fintype α] [Nonempty α] {f : α → ℝ}
    (hf : ∀ a, f a ≤ 1) {b : α} (hb : f b < 1) : avg f < 1 := by
  have hsum : ∑ a, f a < ∑ a : α, (1 : ℝ) :=
    sum_lt_sum (fun a _ => hf a) ⟨b, mem_univ b, hb⟩
  have hlt : avg f < avg (fun _ : α => (1 : ℝ)) := by
    unfold avg
    exact div_lt_div_of_pos_right hsum card_cast_pos
  simpa [avg_const] using hlt

variable [NeZero n]

/-- The dynamics as a Markov kernel on configurations (uniform i.i.d. rounds). -/
noncomputable def kernel (n : ℕ) [NeZero n] : Kernel (Config n) := Kernel.ofStep (step (n := n))

lemma avg_indicator_ne (x : Config n) (o : Op) :
    avg (fun v : Fin n => if x v ≠ o then (1 : ℝ) else 0) =
      ((n : ℝ) - count x o) / n := by
  have h (v : Fin n) :
      (if x v ≠ o then (1 : ℝ) else 0) = 1 - (if x v = o then 1 else 0) := by
    by_cases hv : x v = o <;> simp [hv]
  simp_rw [h, avg_sub, avg_const, avg_indicator_eq]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp

lemma node_prob_a (x : Config n) (v : Fin n) :
    avg (fun w : Fin n => if update (x v) (x w) = .a then (1 : ℝ) else 0) =
      (if x v = .a then (1 : ℝ) else 0) * (((n : ℝ) - count x .b) / n) +
        (if x v = .u then (1 : ℝ) else 0) * ((count x .a : ℝ) / n) := by
  simp_rw [indicator_becomes_a]
  rw [avg_add, avg_const_mul, avg_const_mul, avg_indicator_ne, avg_indicator_eq]

lemma node_prob_b (x : Config n) (v : Fin n) :
    avg (fun w : Fin n => if update (x v) (x w) = .b then (1 : ℝ) else 0) =
      (if x v = .b then (1 : ℝ) else 0) * (((n : ℝ) - count x .a) / n) +
        (if x v = .u then (1 : ℝ) else 0) * ((count x .b : ℝ) / n) := by
  simp_rw [indicator_becomes_b]
  rw [avg_add, avg_const_mul, avg_const_mul, avg_indicator_ne, avg_indicator_eq]

/-- Expected number of `a`-nodes after one round. -/
theorem expected_count_a (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .a : ℝ)) =
      count x .a * (n - count x .b + count x .u) / n := by
  simp_rw [count_step_eq_sum]
  rw [avg_sum]
  have hmarg (v : Fin n) :
      avg (fun r : Fin n → Fin n => if update (x v) (x (r v)) = .a then (1 : ℝ) else 0) =
        avg (fun w : Fin n => if update (x v) (x w) = .a then (1 : ℝ) else 0) :=
    avg_eval (γ := Fin n) n v (fun w => if update (x v) (x w) = .a then (1 : ℝ) else 0)
  simp_rw [hmarg, node_prob_a]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul, ← count_eq_sum, ← count_eq_sum]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp

/-- Expected number of `b`-nodes after one round. -/
theorem expected_count_b (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .b : ℝ)) =
      count x .b * (n - count x .a + count x .u) / n := by
  simp_rw [count_step_eq_sum]
  rw [avg_sum]
  have hmarg (v : Fin n) :
      avg (fun r : Fin n → Fin n => if update (x v) (x (r v)) = .b then (1 : ℝ) else 0) =
        avg (fun w : Fin n => if update (x v) (x w) = .b then (1 : ℝ) else 0) :=
    avg_eval (γ := Fin n) n v (fun w => if update (x v) (x w) = .b then (1 : ℝ) else 0)
  simp_rw [hmarg, node_prob_b]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul, ← count_eq_sum, ← count_eq_sum]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp

/-- Expected number of undecided nodes after one round. -/
theorem expected_count_u (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .u : ℝ)) =
      (count x .u ^ 2 + 2 * count x .a * count x .b) / n := by
  simp_rw [count_step_eq_sum]
  rw [avg_sum]
  have hmarg (v : Fin n) :
      avg (fun r : Fin n → Fin n => if update (x v) (x (r v)) = .u then (1 : ℝ) else 0) =
        avg (fun w : Fin n => if update (x v) (x w) = .u then (1 : ℝ) else 0) :=
    avg_eval (γ := Fin n) n v (fun w => if update (x v) (x w) = .u then (1 : ℝ) else 0)
  simp_rw [hmarg, node_prob_u]
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul]
  rw [← count_eq_sum, ← count_eq_sum, ← count_eq_sum]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp
  ring

/-- The bias grows in expectation by the factor `1 + q / n`. -/
theorem expected_bias (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .a : ℝ) - count (step x r) .b) =
      (count x .a - count x .b) * (1 + count x .u / n) := by
  rw [avg_sub, expected_count_a, expected_count_b]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp
  ring

omit [NeZero n] in
/-- Monochromatic configurations are fixed points. -/
theorem step_of_mono (x : Config n) (h : Mono x) (r : Fin n → Fin n) : step x r = x := by
  obtain ⟨o, ho⟩ := h
  funext v
  rw [step, ho v, ho (r v)]
  cases o <;> rfl

/-- Almost-sure absorption: the probability of not being monochromatic after `t` rounds tends
to zero, from every configuration. -/
lemma notMono_step (x : Config n) : (kernel n).apply notMono x ≤ notMono x := by
  rw [kernel, Kernel.apply_ofStep]
  by_cases h : Mono x
  · have hs : ∀ r : Fin n → Fin n, step x r = x := fun r => step_of_mono x h r
    simp only [hs, avg_const]
    exact le_rfl
  · have hx : notMono x = 1 := by
      unfold notMono
      exact if_neg h
    rw [hx]
    calc avg (fun r => notMono (step x r)) ≤ avg (fun _ : Fin n → Fin n => (1 : ℝ)) :=
          avg_le_avg fun r => notMono_le_one _
      _ = 1 := avg_const 1

lemma kernel_iterate_two (f : Config n → ℝ) (x : Config n) :
    (kernel n).iterate 2 f x =
      avg (fun r₁ : Fin n → Fin n => avg (fun r₂ => f (step (step x r₁) r₂))) := by
  rw [kernel, Kernel.iterate_ofStep]
  simp only [expList_succ, expList_zero]
  refine congrArg avg (funext fun r₁ => congrArg avg (funext fun r₂ => ?_))
  dsimp [List.foldl]

lemma access_from_decided (x : Config n) (w : Fin n) (hw : x w = .a ∨ x w = .b) :
    (kernel n).iterate 2 notMono x < 1 := by
  rw [kernel_iterate_two]
  refine avg_lt_one (b := fun _ => w) ?_ ?_
  · intro r₁
    calc avg (fun r₂ => notMono (step (step x r₁) r₂))
        ≤ avg (fun _ : Fin n → Fin n => (1 : ℝ)) := avg_le_avg fun _ => notMono_le_one _
      _ = 1 := avg_const 1
  · refine avg_lt_one (b := fun _ => w) (fun _ => notMono_le_one _) ?_
    rw [two_const_mono x hw, notMono_const]
    exact zero_lt_one

theorem absorbed (x : Config n) :
    Tendsto (fun t => (kernel n).iterate t notMono x) atTop (𝓝 0) := by
  haveI : Nonempty (Config n) := ⟨fun _ => .u⟩
  refine (kernel n).finite_absorption notMono notMono_binary notMono_step ?_ x
  intro y
  by_cases hy : Mono y
  · refine ⟨0, ?_⟩
    simp only [Kernel.iterate_zero, notMono_of_mono y hy]
    exact zero_lt_one
  · obtain ⟨w, hw⟩ := exists_decided y hy
    exact ⟨2, access_from_decided y w hw⟩

end Undecided
