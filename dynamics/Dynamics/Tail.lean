import Dynamics.Absorption
import Dynamics.Rounds

/-!
# Elementary tail bounds and probability monotonicity

Probability facts that several model packages used to prove locally (see
`dynamics/CONCENTRATION_AUDIT.md`), stated once for the shared finite layer.

* `Distribution.prob_mono`: the probability of an event is monotone in the event.
* `Distribution.expect_lt_one`, `avg_lt_one`: an observable bounded by `1` that is strictly
  below `1` at a point of positive weight has expectation strictly below `1`.
* `avg_markov`: **Markov's inequality** `P(X ≥ c) ≤ 𝔼X / c` for uniform averages, and
  `avg_markov_one`: its form `P(X ≥ 1) ≤ 𝔼X` for a sum of independent nonnegative
  coordinates.
* `Kernel.one_sub_avg_le_prob_ofStep`: one uniformly random round lands in an event with
  probability at least `1 - 𝔼[bad]`, when `bad ≥ 0` charges every miss at least `1`.
* `Kernel.iterate_monotone`: a subharmonic observable (`f ≤ K f`) has nondecreasing
  finite-time expectations, and `Kernel.event_monotone`: the occupation probability of an
  absorbing event is nondecreasing in time.
* `exp_neg_two_log`, `one_le_of_log_pos`: the scalar conversions used to state
  high-probability bounds in regimes `C ≤ log n`.

As everywhere in this library, the source has no paper numbering; each docstring names the
package lemmas that the statement replaces.
-/

namespace Dynamics

open Finset

/-! ### Distributions -/

namespace Distribution
variable {α : Type*} [Fintype α]

/-- **Monotonicity of probability**: a larger event has a larger probability. A set
inclusion `h : A ⊆ B` can be passed directly for the events `(· ∈ A)` and `(· ∈ B)`.
Replaces `Plurality.prob_mono_set` and `Median.prob_mono_set'`. -/
theorem prob_mono (p : Distribution α) {s t : α → Prop} (h : ∀ ⦃a⦄, s a → t a) :
    p.prob s ≤ p.prob t := by
  classical
  unfold prob
  refine p.expect_mono fun a => ?_
  by_cases ha : s a
  · simp [ha, h ha]
  · by_cases hb : t a <;> simp [ha, hb]

/-- An observable bounded by `1` that is strictly below `1` at a point of positive weight has
expectation strictly below `1`. Replaces `Moran.expect_lt_one` and `Voter.expect_lt_one`. -/
theorem expect_lt_one (p : Distribution α) (f : α → ℝ) (hf : ∀ a, f a ≤ 1) (b : α)
    (hb : 0 < p.weight b) (hfb : f b < 1) : p.expect f < 1 := by
  calc p.expect f < p.expect (fun _ => 1) :=
        sum_lt_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a) (p.nonneg a))
          ⟨b, mem_univ b, mul_lt_mul_of_pos_left hfb hb⟩
    _ = 1 := p.expect_const 1

end Distribution

/-! ### Uniform averages: strict bound and Markov's inequality -/

variable {α : Type*} [Fintype α]

/-- The uniform case of `Distribution.expect_lt_one`: on a nonempty type, an observable
bounded by `1` and strictly below `1` somewhere has average strictly below `1`.
Replaces `Undecided.avg_lt_one`. -/
theorem avg_lt_one [Nonempty α] {f : α → ℝ} (hf : ∀ a, f a ≤ 1) {b : α} (hb : f b < 1) :
    avg f < 1 := by
  have hsum : ∑ a, f a < ∑ _a : α, (1 : ℝ) := sum_lt_sum (fun a _ => hf a) ⟨b, mem_univ b, hb⟩
  have hlt : avg f < avg (fun _ : α => (1 : ℝ)) :=
    (div_lt_div_iff_of_pos_right card_cast_pos).mpr hsum
  rwa [avg_const] at hlt

/-- **Markov's inequality** for uniform averages: if `X ≥ 0` and `c > 0`, then
`P(X ≥ c) ≤ 𝔼X / c`. -/
theorem avg_markov {X : α → ℝ} (hX : ∀ a, 0 ≤ X a) {c : ℝ} (hc : 0 < c) :
    avg (fun a => if c ≤ X a then (1 : ℝ) else 0) ≤ avg X / c := by
  have hpt (a : α) : (if c ≤ X a then (1 : ℝ) else 0) ≤ c⁻¹ * X a := by
    split_ifs with h
    · rw [← div_eq_inv_mul, one_le_div hc]
      exact h
    · exact mul_nonneg (inv_nonneg.mpr hc.le) (hX a)
  calc _ ≤ avg (fun a => c⁻¹ * X a) := avg_le_avg hpt
    _ = avg X / c := by rw [avg_const_mul, div_eq_inv_mul]

/-- **Markov's inequality for a sum of independent nonnegative coordinates**:
`P(X ≥ 1) ≤ 𝔼X` for `X = ∑ᵢ Yᵢ(ωᵢ)`, `ω : Fin n → γ` uniform. Replaces
`Plurality.markov_one` (plurality blueprint `lem:tails`) and the Markov steps proved inline
in `Median.falses_tail_markov` and `ThreeMajority.saturation_stage2c`. -/
theorem avg_markov_one {n : ℕ} {γ : Type*} [Fintype γ] (Y : Fin n → γ → ℝ)
    (hY : ∀ i x, 0 ≤ Y i x) :
    avg (fun ω : Fin n → γ => if 1 ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ ∑ i, avg (Y i) := by
  have hpt (ω : Fin n → γ) :
      (if 1 ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0) ≤ ∑ i, Y i (ω i) := by
    split_ifs with h
    · exact h
    · exact sum_nonneg fun i _ => hY i (ω i)
  calc _ ≤ avg (fun ω : Fin n → γ => ∑ i, Y i (ω i)) := avg_le_avg hpt
    _ = ∑ i, avg (fun ω : Fin n → γ => Y i (ω i)) := avg_sum univ _
    _ = ∑ i, avg (Y i) := by
        refine sum_congr rfl fun i _ => ?_
        rcases isEmpty_or_nonempty γ with hγ | hγ
        · have : IsEmpty (Fin n → γ) := ⟨fun ω => hγ.false (ω i)⟩
          simp [avg]
        · exact avg_eval n i (Y i)

/-! ### One random round, and absorbing events -/

namespace Kernel

/-- **One round lands in an event with probability at least `1 - 𝔼[bad]`**, whenever the
nonnegative charge `bad` is at least `1` on every round that misses the event (Markov's
inequality for the complement). Replaces `Median.prob_step_ge` and
`Plurality.le_prob_step`. -/
theorem one_sub_avg_le_prob_ofStep {S R : Type*} [Fintype S] [Fintype R] [Nonempty R]
    (step : S → R → S) (P : S → Prop) (s : S) (bad : R → ℝ) (h0 : ∀ r, 0 ≤ bad r)
    (h1 : ∀ r, ¬ P (step s r) → 1 ≤ bad r) :
    1 - avg bad ≤ (ofStep step s).prob P := by
  classical
  rw [prob_ofStep]
  have e : 1 - avg bad = avg (fun r => 1 - bad r) := by rw [avg_sub, avg_const]
  rw [e]
  refine avg_le_avg fun r => ?_
  by_cases hr : P (step s r)
  · simp only [hr, ↓reduceIte]
    linarith [h0 r]
  · have := h1 r hr
    simp only [hr, ↓reduceIte]
    linarith

/-- An observable with `f ≤ K f` (subharmonic) has nondecreasing finite-time expectations:
the counterpart of `iterate_antitone`. Replaces the inductions in `Moran.fixation_mono`,
`Voter.colorProbability_mono` and `Median.event_absorb_mono`. -/
theorem iterate_monotone (K : Dynamics.Kernel α) (f : α → ℝ)
    (h : ∀ a, f a ≤ K.apply f a) (a : α) : Monotone (fun n => K.iterate n f a) := by
  apply monotone_nat_of_le_succ
  intro n
  have he : K.iterate (n + 1) f = K.iterate n (K.apply f) := by
    rw [K.iterate_add_time]
    rfl
  rw [he]
  exact K.iterate_mono n h a

/-- **The occupation probability of an absorbing event is nondecreasing in time**: if every
state of `P` stays in `P` with probability one, then `n ↦ P(Xₙ ∈ P)` is monotone.
Replaces `Median.event_absorb_mono`. -/
theorem event_monotone (K : Dynamics.Kernel α) {P : α → Prop}
    (habs : ∀ a, P a → (K a).prob P = 1) (a : α) : Monotone (fun n => K.event P n a) := by
  classical
  have hstep (b : α) :
      (if P b then (1 : ℝ) else 0) ≤ K.apply (fun c => if P c then (1 : ℝ) else 0) b := by
    by_cases hb : P b
    · rw [if_pos hb]
      exact (habs b hb).symm.le
    · rw [if_neg hb]
      exact (K b).expect_nonneg fun c => by split <;> norm_num
  exact K.iterate_monotone _ hstep a

end Kernel

/-! ### Scalar facts for high-probability statements -/

/-- `exp (-2 log n) = 1/n²`, the conversion of a tail bound `exp (-c)` with `c ≥ 2 log n`
into a failure probability `1/n²`. Replaces `Plurality.exp_neg_two_log` and
`Median.exp_neg_two_log`. -/
theorem exp_neg_two_log {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(2 * Real.log n)) = 1 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.exp_neg, show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div]

/-- A hypothesis `0 < log n`, as implied by the regimes `C ≤ log n` with `C > 0`, forces
`1 ≤ n`. Replaces `Plurality.one_le_of_log_pos` and `Median.one_le_of_log_pos`. -/
theorem one_le_of_log_pos {n : ℕ} (h : 0 < Real.log n) : 1 ≤ n := by
  rcases n with _ | n
  · simp at h
  · omega

end Dynamics
