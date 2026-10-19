import Dynamics.DriftHittingDefs
import Dynamics.Lazy
import Dynamics.Stationary

/-!
# Relations between finite chains

The cross-field dictionary of Leanamics (`home_page/_data/dictionary.yml`) says that processes of
different fields are the same Markov chain, or are related by a kind of relation. This file gives
four of these kinds a precise meaning for finite kernels `Kernel α = α → Distribution α`, quoting
the dictionary's description of each kind.

* **Same chain on counts** (`Kernel.Lumps f K L`, kind `same-chain`: "the same transition kernel,
  on configurations or, where stated, on counts"). From every state `x`, one step of `K` observed
  through `f` (for instance the number of individuals of a type) is one step of `L` from `f x`.
  The lumping lifts to the law at every time, `(K^t x).map f = L^t (f x)` (`Lumps.law`, with
  `Kernel.law` the law at time `t`), to expectations, events and path functionals
  (`Lumps.iterate`, `Lumps.event`, `Lumps.trajectory`), so fixation, consensus and hitting
  probabilities of `K` read through `f` are those of `L` (`Lumps.event`, `Lumps.hitProb`).
* **Same jump chain** (`Kernel.jump`, `Kernel.SameJumpChain`, kind `jump-chain`: "the same chain
  once idle steps are removed ...; the processes differ by a random time change, so absorption
  probabilities agree but running times need not"). The jump chain of `K` is its step conditioned
  on moving; a state that `K` never leaves stays absorbing. Kernels whose rows are proportional
  off the diagonal have the same jump chain (`sameJumpChain_of_weight`); a lazy version is an
  example (`lazy_sameJumpChain`). Kernels with the same jump chain have the same harmonic
  functions (`SameJumpChain.apply_eq_self_iff`) and the same absorption probabilities
  (`SameJumpChain.iSup_event_eq`).
* **Duality** (`Kernel.Dual H K L`, kind `duality`: "an exact identity between probabilities of
  one process and of a dual process ..."): `E_x[H(X_t, y)] = E_y[H(x, Y_t)]`, which follows for
  every `t` from the case of one step (`Dual.iterate`).
* **Mean field** (`Kernel.MeanField K φ F`, kind `mean-field`: "the expected one-step change ...
  coincides; the stochastic processes may differ"): the expected one-step map of the observables
  `φ` is the recursion `F`, `E_x[φ(X₁)] = F(φ(x))`. A lumping transfers it (`Lumps.meanField`).

The other kinds of the dictionary (same continuous-time chain, coupling, large-population limit,
same deterministic recursion) are not statements about one step of two finite kernels and are
not defined here.
-/

namespace Dynamics
open Finset Filter Topology

namespace Distribution
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Distributions with the same weights are equal. -/
theorem ext {p q : Distribution α} (h : ∀ a, p.weight a = q.weight a) : p = q := by
  obtain ⟨wp, _, _⟩ := p
  obtain ⟨wq, _, _⟩ := q
  obtain rfl : wp = wq := funext h
  rfl

/-- The weight of a point is the expectation of its indicator. -/
theorem weight_eq_expect_ite [DecidableEq α] (p : Distribution α) (a : α) :
    p.weight a = p.expect fun b => if b = a then 1 else 0 := by
  simp [expect]

/-- Distributions with the same expectations are equal. -/
theorem ext_expect {p q : Distribution α} (h : ∀ f, p.expect f = q.expect f) : p = q := by
  classical
  exact ext fun a => by rw [weight_eq_expect_ite, weight_eq_expect_ite, h]

/-- Transporting along `f` and then along `g` is transporting along `g ∘ f`. -/
theorem map_map (p : Distribution α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map fun a => g (f a) :=
  ext_expect fun h => by simp only [map_expect]

/-- A point mass is transported to a point mass. -/
theorem map_point (a : α) (f : α → β) : (point a).map f = point (f a) :=
  ext_expect fun h => by rw [map_expect, point_expect, point_expect]

/-- Fubini's theorem for two finite distributions. -/
theorem expect_comm (p : Distribution α) (q : Distribution β) (F : α → β → ℝ) :
    p.expect (fun a => q.expect (F a)) = q.expect fun b => p.expect fun a => F a b := by
  simp only [expect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring

end Distribution

namespace Kernel
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ### Laws at finite times -/

/-- Expectations after one step of a distribution: `𝔼_{pK}[g] = 𝔼_p[Kg]`. -/
theorem advance_expect (K : Kernel α) (p : Distribution α) (g : α → ℝ) :
    (K.advance p).expect g = p.expect (K.apply g) := by
  simp only [Distribution.expect, advance, apply, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- The law at time `t` computes the expectations at time `t`: `𝔼_{pKᵗ}[g] = 𝔼_p[Kᵗg]`; from a
point mass, `(K.law (point x) t).expect g = K.iterate t g x`. -/
theorem law_expect (K : Kernel α) (p : Distribution α) (t : ℕ) (g : α → ℝ) :
    (K.law p t).expect g = p.expect (K.iterate t g) := by
  induction t generalizing g with
  | zero => rfl
  | succ t ih =>
    change (K.advance (K.law p t)).expect g = _
    rw [advance_expect, ih, K.iterate_add_time t 1]
    rfl

/-! ### Same chain on counts: lumping -/

/-- **Same chain on counts** (kind `same-chain` of the dictionary: "the same transition kernel,
on configurations or, where stated, on counts"). `K` *lumps* to `L` along `f` when, from every
state `x`, one step of `K` observed through `f` is one step of `L` from `f x`:
`(K x).map f = L (f x)`. Then `f(X_t)` evolves as the chain `L` from `f x`: it has the same law
at every time (`Lumps.law`) and the same path functionals (`Lumps.trajectory`). -/
def Lumps (f : α → β) (K : Kernel α) (L : Kernel β) : Prop :=
  ∀ x, (K x).map f = L (f x)

/-- A lumping in terms of observables: `𝔼_x[g(f(X₁))] = 𝔼_{f x}[g(Y₁)]` for every `g`. -/
theorem lumps_iff_apply {f : α → β} {K : Kernel α} {L : Kernel β} :
    Lumps f K L ↔ ∀ (g : β → ℝ) (x : α), K.apply (fun a => g (f a)) x = L.apply g (f x) := by
  refine ⟨fun h g x => ?_, fun h x => Distribution.ext_expect fun g => ?_⟩
  · rw [apply, apply, ← h x, Distribution.map_expect]
  · rw [Distribution.map_expect]
    exact h g x

namespace Lumps
variable {f : α → β} {K : Kernel α} {L : Kernel β}

/-- One step of a lumping, on observables. -/
theorem apply (h : Lumps f K L) (g : β → ℝ) (x : α) :
    K.apply (fun a => g (f a)) x = L.apply g (f x) :=
  lumps_iff_apply.1 h g x

/-- A lumping lifts to every time, on observables: `𝔼_x[g(f(X_t))] = 𝔼_{f x}[g(Y_t)]`. -/
theorem iterate (h : Lumps f K L) (t : ℕ) (g : β → ℝ) (x : α) :
    K.iterate t (fun a => g (f a)) x = L.iterate t g (f x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [iterate_succ, iterate_succ, ← h.apply]
    exact congrArg (K.apply · x) (funext ih)

/-- A lumping lifts to the law at every time: `(pKᵗ).map f = (p.map f) Lᵗ`; from a point mass,
`(K^t x).map f = L^t (f x)`. -/
theorem law (h : Lumps f K L) (p : Distribution α) (t : ℕ) :
    (K.law p t).map f = L.law (p.map f) t :=
  Distribution.ext_expect fun g => by
    rw [Distribution.map_expect, law_expect, law_expect, Distribution.map_expect]
    exact congrArg p.expect (funext (h.iterate t g))

/-- The probability that `f(X_t)` lies in `s` is the probability that `Y_t` lies in `s`. -/
theorem event (h : Lumps f K L) (s : β → Prop) (t : ℕ) (x : α) :
    K.event (fun a => s (f a)) t x = L.event s t (f x) := by
  classical
  rw [event_eq_iterate, event_eq_iterate]
  exact h.iterate t (fun b => if s b then 1 else 0) x

/-- A lumping lifts to functionals of the whole trajectory up to time `t`. -/
theorem trajectory (h : Lumps f K L) (t : ℕ) (x : α) (F : List β → β → ℝ) :
    K.trajectory t x (fun l c => F (l.map f) (f c)) = L.trajectory t (f x) F := by
  induction t generalizing x F with
  | zero => rfl
  | succ t ih =>
    change (K x).expect (fun b => K.trajectory t b (fun l c => F (f x :: l.map f) (f c))) =
      (L (f x)).expect (fun b => L.trajectory t b (fun l c => F (f x :: l) c))
    rw [← h x, Distribution.map_expect]
    exact congrArg (K x).expect (funext fun b => ih b fun l c => F (f x :: l) c)

/-- Hitting probabilities transfer: `P_x(f(X_s) ∈ B for some s ≤ t) = P_{f x}(Y_s ∈ B for some
s ≤ t)`. -/
theorem hitProb (h : Lumps f K L) (B : β → Prop) (t : ℕ) (x : α) :
    K.hitProb (fun a => B (f a)) t x = L.hitProb B t (f x) := by
  classical
  unfold Kernel.hitProb
  rw [← h.trajectory]
  simp

/-- Lumpings compose. -/
theorem comp {M : Kernel γ} {g : β → γ} (h : Lumps f K L) (h' : Lumps g L M) :
    Lumps (fun a => g (f a)) K M := fun x => by
  rw [← Distribution.map_map, h x, h' (f x)]

end Lumps

/-! ### Same jump chain -/

/-- The weights of the states other than `x` add up to `1 - K(x, x)`. -/
theorem sum_erase_weight (K : Kernel α) (x : α) [DecidableEq α] :
    ∑ y ∈ univ.erase x, (K x).weight y = 1 - (K x).weight x := by
  rw [← (K x).sum_one, ← add_sum_erase univ _ (mem_univ x)]
  ring

/-- A state that `K` never leaves gives no weight to the other states. -/
theorem weight_eq_zero_of_weight_self (K : Kernel α) {x : α} (hx : (K x).weight x = 1) {y : α}
    (hy : y ≠ x) : (K x).weight y = 0 := by
  classical
  have hs := K.sum_erase_weight x
  rw [hx, sub_self] at hs
  exact (sum_eq_zero_iff_of_nonneg fun z _ => (K x).nonneg z).1 hs y (mem_erase.2 ⟨hy, mem_univ y⟩)

/-- A state that `K` never leaves: one step from it is the point mass. -/
theorem eq_point_of_weight_self (K : Kernel α) {x : α} (hx : (K x).weight x = 1) :
    K x = Distribution.point x := by
  classical
  refine Distribution.ext fun y => ?_
  simp only [Distribution.point]
  split_ifs with hy
  · rw [hy, hx]
  · exact K.weight_eq_zero_of_weight_self hx hy

/-- The **jump chain** of `K` (kind `jump-chain` of the dictionary: "the same chain once idle
steps are removed"): from `x`, the step of `K` conditioned on leaving `x`, which gives weight
`K(x, y) / (1 - K(x, x))` to every `y ≠ x`. A state that `K` never leaves (`K(x, x) = 1`) stays
absorbing. -/
noncomputable def jump (K : Kernel α) : Kernel α := fun x => by
  classical
  exact if h : (K x).weight x = 1 then Distribution.point x else
    { weight := fun y => if y = x then 0 else (K x).weight y / (1 - (K x).weight x)
      nonneg := fun y => by
        split
        · exact le_rfl
        · exact div_nonneg ((K x).nonneg y) (sub_nonneg.2 (weight_le_one _ x))
      sum_one := by
        have hd : 1 - (K x).weight x ≠ 0 := sub_ne_zero.2 (Ne.symm h)
        rw [← sum_erase_add univ _ (mem_univ x), if_pos rfl, add_zero,
          sum_congr rfl fun y hy => if_neg (ne_of_mem_erase hy), ← sum_div, K.sum_erase_weight,
          div_self hd] }

/-- Two kernels have the **same jump chain** (kind `jump-chain` of the dictionary). -/
def SameJumpChain (K L : Kernel α) : Prop := K.jump = L.jump

/-- From a state that `K` never leaves, the jump chain stays put. -/
theorem jump_of_weight_self (K : Kernel α) {x : α} (hx : (K x).weight x = 1) :
    K.jump x = Distribution.point x := by
  simp only [jump, dif_pos hx]

/-- From a state that `K` may leave, the jump chain moves. -/
theorem jump_weight_self (K : Kernel α) {x : α} (hx : (K x).weight x ≠ 1) :
    (K.jump x).weight x = 0 := by
  simp [jump, hx]

/-- Off the diagonal, `K(x, y) = (1 - K(x, x)) · J(x, y)` for the jump chain `J` of `K`. -/
theorem weight_eq_mul_jump (K : Kernel α) {x y : α} (hy : y ≠ x) :
    (K x).weight y = (1 - (K x).weight x) * (K.jump x).weight y := by
  by_cases hx : (K x).weight x = 1
  · rw [K.weight_eq_zero_of_weight_self hx hy, hx, sub_self, zero_mul]
  · have hd : 1 - (K x).weight x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
    simp only [jump, dif_neg hx, if_neg hy]
    field_simp

/-- One step of `K` stays put with probability `K(x, x)` and otherwise follows its jump chain:
`Kg(x) = K(x, x) g(x) + (1 - K(x, x)) Jg(x)`. -/
theorem apply_eq_jump (K : Kernel α) (g : α → ℝ) (x : α) :
    K.apply g x = (K x).weight x * g x + (1 - (K x).weight x) * K.jump.apply g x := by
  classical
  by_cases hx : (K x).weight x = 1
  · have h1 : K.apply g x = g x := by
      rw [apply, K.eq_point_of_weight_self hx, Distribution.point_expect]
    have h2 : K.jump.apply g x = g x := by
      rw [apply, K.jump_of_weight_self hx, Distribution.point_expect]
    rw [h1, h2, hx]
    ring
  · simp only [apply, Distribution.expect]
    rw [← add_sum_erase univ _ (mem_univ x), ← add_sum_erase univ _ (mem_univ x),
      K.jump_weight_self hx, zero_mul, zero_add, mul_sum]
    congr 1
    refine sum_congr rfl fun y hy => ?_
    rw [K.weight_eq_mul_jump (ne_of_mem_erase hy)]
    ring

/-- `g` is harmonic at `x` for `K` iff it is harmonic at `x` for the jump chain of `K`. -/
theorem apply_eq_self_iff_jump (K : Kernel α) (g : α → ℝ) (x : α) :
    K.apply g x = g x ↔ K.jump.apply g x = g x := by
  by_cases hx : (K x).weight x = 1
  · rw [apply, apply, K.eq_point_of_weight_self hx, K.jump_of_weight_self hx]
  · have hd : 1 - (K x).weight x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
    rw [K.apply_eq_jump g x]
    constructor
    · intro h
      have h' : (1 - (K x).weight x) * (K.jump.apply g x - g x) = 0 := by linarith
      linarith [(mul_eq_zero.1 h').resolve_left hd]
    · intro h
      rw [h]
      ring

/-- **Criterion for the same jump chain.** If, from every state, the rows of `K` and `L` are
proportional off the diagonal with a positive factor, then `K` and `L` have the same jump
chain. -/
theorem sameJumpChain_of_weight {K L : Kernel α}
    (h : ∀ x, ∃ c, 0 < c ∧ ∀ y, y ≠ x → (K x).weight y = c * (L x).weight y) :
    K.SameJumpChain L := by
  classical
  funext x
  obtain ⟨c, hc, hKL⟩ := h x
  have hsum : 1 - (K x).weight x = c * (1 - (L x).weight x) := by
    rw [← K.sum_erase_weight, ← L.sum_erase_weight, mul_sum]
    exact sum_congr rfl fun y hy => hKL y (ne_of_mem_erase hy)
  by_cases hL : (L x).weight x = 1
  · have hK : (K x).weight x = 1 := by
      rw [hL, sub_self, mul_zero] at hsum
      linarith
    rw [K.jump_of_weight_self hK, L.jump_of_weight_self hL]
  · have hK : (K x).weight x ≠ 1 := by
      intro hK
      rw [hK, sub_self] at hsum
      exact hL (by nlinarith [mul_eq_zero.1 hsum.symm])
    have hdL : 1 - (L x).weight x ≠ 0 := sub_ne_zero.2 (Ne.symm hL)
    refine Distribution.ext fun y => ?_
    simp only [jump, dif_neg hK, dif_neg hL]
    split_ifs with hy
    · rfl
    · rw [hKL y hy, hsum, mul_div_mul_left _ _ hc.ne']

/-- The jump chain of a jump chain is itself. -/
theorem jump_jump (K : Kernel α) : K.jump.jump = K.jump :=
  sameJumpChain_of_weight fun x => by
    by_cases hx : (K x).weight x = 1
    · refine ⟨1, one_pos, fun y hy => ?_⟩
      rw [K.jump_of_weight_self hx, K.weight_eq_zero_of_weight_self hx hy]
      simp [Distribution.point, hy]
    · have hd : 0 < 1 - (K x).weight x :=
        sub_pos.2 (lt_of_le_of_ne (weight_le_one _ x) hx)
      refine ⟨(1 - (K x).weight x)⁻¹, inv_pos.2 hd, fun y hy => ?_⟩
      rw [K.weight_eq_mul_jump hy, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]

/-- A kernel that stays put only at the states it never leaves is its own jump chain. -/
theorem jump_eq_self (K : Kernel α) (h : ∀ x, (K x).weight x = 0 ∨ (K x).weight x = 1) :
    K.jump = K := by
  funext x
  rcases h x with h0 | h1
  · have hx : (K x).weight x ≠ 1 := by rw [h0]; norm_num
    refine Distribution.ext fun y => ?_
    by_cases hy : y = x
    · rw [hy, K.jump_weight_self hx, h0]
    · rw [K.weight_eq_mul_jump hy, h0, sub_zero, one_mul]
  · rw [K.jump_of_weight_self h1, K.eq_point_of_weight_self h1]

/-- A lazy version has the same jump chain: its idle steps are removed. -/
theorem lazy_sameJumpChain [DecidableEq α] (K : Kernel α) : (lazy K).SameJumpChain K :=
  sameJumpChain_of_weight fun x =>
    ⟨1 / 2, by norm_num, fun y hy => by rw [lazy_weight, if_neg (Ne.symm hy)]; ring⟩

namespace SameJumpChain
variable {K L : Kernel α}

theorem symm (h : K.SameJumpChain L) : L.SameJumpChain K := Eq.symm h

/-- Kernels with the same jump chain have the same harmonic functions, state by state. -/
theorem apply_eq_self_iff (h : K.SameJumpChain L) (g : α → ℝ) (x : α) :
    K.apply g x = g x ↔ L.apply g x = g x := by
  rw [K.apply_eq_self_iff_jump, L.apply_eq_self_iff_jump, h]

end SameJumpChain

/-- If `A` is absorbing, the probability of `A` at time `t` increases with `t`. -/
theorem event_monotone_of_absorbing (K : Kernel α) {A : α → Prop}
    (hA : ∀ a, A a → (K a).prob A = 1) (x : α) : Monotone fun t => K.event A t x := by
  classical
  have hstep (a : α) :
      (if A a then (1 : ℝ) else 0) ≤ K.apply (fun b => if A b then 1 else 0) a := by
    by_cases ha : A a
    · rw [if_pos ha, apply, ← Distribution.prob_eq_expect, hA a ha]
    · rw [if_neg ha]
      exact (K a).expect_nonneg fun b => by split <;> norm_num
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [K.event_eq_iterate A, K.iterate_add_time t 1]
  exact K.iterate_mono t hstep x

/-- The absorption probability of an absorbing event is harmonic. -/
theorem apply_iSup_event (K : Kernel α) {A : α → Prop} (hA : ∀ a, A a → (K a).prob A = 1)
    (x : α) : K.apply (fun y => ⨆ t, K.event A t y) x = ⨆ t, K.event A t x := by
  classical
  have hlim (y : α) : Tendsto (fun t => K.event A t y) atTop (𝓝 (⨆ t, K.event A t y)) :=
    tendsto_atTop_ciSup (K.event_monotone_of_absorbing hA y)
      ⟨1, by rintro _ ⟨t, rfl⟩; exact K.event_le_one A t y⟩
  have hsucc : Tendsto (fun t => K.apply (fun y => K.event A t y) x) atTop
      (𝓝 (K.apply (fun y => ⨆ t, K.event A t y) x)) := by
    simp only [apply, Distribution.expect]
    exact tendsto_finsetSum _ fun y _ => (hlim y).const_mul _
  have heq (t : ℕ) : K.apply (fun y => K.event A t y) x = K.event A (t + 1) x := by
    simp only [K.event_eq_iterate A]
    rfl
  simp only [heq] at hsucc
  exact tendsto_nhds_unique hsucc ((tendsto_add_atTop_iff_nat 1).2 (hlim x))

/-- A nonnegative harmonic function that is at least `1` on `A` bounds the probability of `A` at
every time. -/
theorem event_le_of_harmonic (K : Kernel α) {A : α → Prop} {g : α → ℝ} (hg0 : ∀ y, 0 ≤ g y)
    (hgA : ∀ y, A y → 1 ≤ g y) (hg : ∀ y, K.apply g y = g y) (t : ℕ) (x : α) :
    K.event A t x ≤ g x := by
  classical
  induction t generalizing x with
  | zero =>
    rw [K.event_eq_iterate, iterate_zero]
    split_ifs with hx
    · exact hgA x hx
    · exact hg0 x
  | succ t ih =>
    rw [K.event_eq_iterate, iterate_succ, ← hg x]
    exact (K x).expect_mono fun y => by rw [← K.event_eq_iterate]; exact ih y

/-- **Same jump chain, same absorption probabilities.** If `K` and `L` have the same jump chain
and `A` is absorbing for both, then from every state the probability of absorption in `A`, the
supremum of the probabilities of `A` at finite times, is the same for `K` and for `L`. -/
theorem SameJumpChain.iSup_event_eq {K L : Kernel α} (h : K.SameJumpChain L) {A : α → Prop}
    (hK : ∀ a, A a → (K a).prob A = 1) (hL : ∀ a, A a → (L a).prob A = 1) (x : α) :
    ⨆ t, K.event A t x = ⨆ t, L.event A t x := by
  -- each absorption probability is harmonic for both kernels, so it bounds the other one
  have key {K L : Kernel α} (h : K.SameJumpChain L) (hL : ∀ a, A a → (L a).prob A = 1)
      (x : α) : ⨆ t, K.event A t x ≤ ⨆ t, L.event A t x := by
    have hb (y : α) : BddAbove (Set.range fun t => L.event A t y) :=
      ⟨1, by rintro _ ⟨t, rfl⟩; exact L.event_le_one A t y⟩
    refine ciSup_le fun t => K.event_le_of_harmonic (g := fun y => ⨆ t, L.event A t y)
      (fun y => (L.event_nonneg A 0 y).trans (le_ciSup (hb y) 0))
      (fun y hy => ?_) (fun y => (h.apply_eq_self_iff _ y).2 (L.apply_iSup_event hL y)) t x
    classical
    refine le_trans (le_of_eq ?_) (le_ciSup (hb y) 0)
    rw [L.event_eq_iterate, iterate_zero, if_pos hy]
  exact le_antisymm (key h hL x) (key h.symm hK x)

/-! ### Duality -/

/-- Expectations under `L` at time `t` commute with a finite average over a parameter. -/
theorem expect_iterate_comm (L : Kernel β) (p : Distribution γ) (F : γ → β → ℝ) (t : ℕ)
    (y : β) : p.expect (fun c => L.iterate t (F c) y) =
      L.iterate t (fun b => p.expect fun c => F c b) y := by
  induction t generalizing y with
  | zero => rfl
  | succ t ih =>
    simp only [iterate_succ, apply]
    rw [Distribution.expect_comm]
    exact congrArg (L y).expect (funext ih)

/-- **Duality** (kind `duality` of the dictionary: "an exact identity between probabilities of
one process and of a dual process ..."). `K` on `α` and `L` on `β` are dual with respect to
`H : α → β → ℝ` when `𝔼_x[H(X₁, y)] = 𝔼_y[H(x, Y₁)]` for all `x` and `y`; it then holds at every
time (`Dual.iterate`). -/
def Dual (H : α → β → ℝ) (K : Kernel α) (L : Kernel β) : Prop :=
  ∀ x y, K.apply (fun a => H a y) x = L.apply (H x) y

/-- **One-step duality gives duality at every time:** `𝔼_x[H(X_t, y)] = 𝔼_y[H(x, Y_t)]`. -/
theorem Dual.iterate {H : α → β → ℝ} {K : Kernel α} {L : Kernel β} (h : Dual H K L) (t : ℕ)
    (x : α) (y : β) : K.iterate t (fun a => H a y) x = L.iterate t (H x) y := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [iterate_succ, apply, show K.iterate t (fun a => H a y) = fun a => L.iterate t (H a) y
      from funext ih, expect_iterate_comm, L.iterate_add_time t 1]
    exact congrArg (L.iterate t · y) (funext fun b => h x b)

/-- Duality is symmetric. -/
theorem Dual.symm {H : α → β → ℝ} {K : Kernel α} {L : Kernel β} (h : Dual H K L) :
    Dual (fun b a => H a b) L K := fun y x => (h x y).symm

/-! ### Mean field -/

/-- **Mean field** (kind `mean-field` of the dictionary: "the expected one-step change ...
coincides; the stochastic processes may differ"). The observables `φ i` of `K` follow the
recursion `F` in expectation over one step: `𝔼_x[φ(X₁)] = F(φ(x))`. Two chains with the same
observables and map `F` have the same mean-field recursion. -/
def MeanField {ι : Type*} (K : Kernel α) (φ : α → ι → ℝ) (F : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ x i, K.apply (fun a => φ a i) x = F (φ x) i

/-- A lumping transfers a mean-field map to the observables read through the lumping map. -/
theorem Lumps.meanField {ι : Type*} {f : α → β} {K : Kernel α} {L : Kernel β}
    (h : Lumps f K L) {φ : β → ι → ℝ} {F : (ι → ℝ) → ι → ℝ} (hL : L.MeanField φ F) :
    K.MeanField (fun a => φ (f a)) F := fun x i => by
  rw [h.apply (fun b => φ b i) x, hL]

/-- With the identity as mean-field map, every observable keeps its expectation at all times
(it is a martingale). -/
theorem MeanField.iterate_id {ι : Type*} {K : Kernel α} {φ : α → ι → ℝ}
    (h : K.MeanField φ fun u => u) (t : ℕ) (x : α) (i : ι) :
    K.iterate t (fun a => φ a i) x = φ x i :=
  congrFun (K.iterate_invariant (funext fun y => h y i) t) x

end Kernel
end Dynamics
