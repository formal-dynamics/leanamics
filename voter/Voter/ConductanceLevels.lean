import Voter.Coalescence

/-! # Time spent in a set left with uniform probability (VOT-5)

A generic bound on expected occupation times, used twice in the analysis of the lazy voter of
Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn (ICALP 2016):

* `sum_iterate_le_of_block`: let `f` be the indicator of a set `A` that cannot be re-entered
  (`K f ≤ f`), and `g ≤ f` the indicator of a part `D` of `A`. If from every state of `D` the
  chain has left `A` after `B` steps with probability at least `p`, then the expected time spent
  in `D`, `∑_{t < N} P_x(X_t ∈ D)`, is at most `B / p` (and zero outside `A`). With `D = A` the
  non-consensus states this is "restarting": `𝔼[T] ≤ B / p`.
* the supporting facts on `Kernel.iterate`: it commutes with finite sums
  (`iterate_finset_sum`), constant configurations are absorbing for every observable
  (`transition_iterate_constant`), and disagreement cannot reappear (`transition_disagreement_le`).

`sum_iterate_le_of_block` and `iterate_finset_sum` are candidates for `dynamics/`.
-/

namespace Voter
open Dynamics Finset

section Generic
variable {α : Type*} [Fintype α]

/-- `Kernel.iterate` commutes with finite sums of observables. -/
lemma iterate_finset_sum {ι : Type*} (K : Kernel α) (n : ℕ) (s : Finset ι)
    (F : ι → α → ℝ) :
    K.iterate n (fun y => ∑ i ∈ s, F i y) = fun y => ∑ i ∈ s, K.iterate n (F i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact K.iterate_const n 0
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    rw [K.iterate_add n (F i) (fun y => ∑ j ∈ s, F j y), ih]

/-- `Kernel.apply` commutes with finite sums of observables. -/
lemma apply_finset_sum {ι : Type*} (K : Kernel α) (s : Finset ι) (F : ι → α → ℝ) (x : α) :
    K.apply (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, K.apply (F i) x :=
  congrFun (iterate_finset_sum K 1 s F) x

/-- **Expected time in a part of a set that cannot be re-entered.** Let `f ∈ [0, 1]` with
`K f ≤ f` (e.g. the indicator of a set that the chain never re-enters), and `g ≤ f` a
`{0, 1}`-valued observable. If from every state with `g = 1` the expectation of `f` after `B`
steps is at most `1 - p`, with `p > 0`, then for every horizon `N`,
`∑_{t < N} 𝔼_x[g(X_t)] ≤ (B / p) f x`. -/
theorem sum_iterate_le_of_block (K : Kernel α) (f g : α → ℝ) (B : ℕ) {p : ℝ} (hp : 0 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (hg : ∀ x, g x = 0 ∨ g x = 1)
    (hgf : ∀ x, g x ≤ f x) (hK : ∀ x, K.apply f x ≤ f x)
    (hblock : ∀ x, g x = 1 → K.iterate B f x ≤ 1 - p) (N : ℕ) (x : α) :
    ∑ t ∈ range N, K.iterate t g x ≤ B / p * f x := by
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rcases hg x with h | h <;> simp [h]
  have hg1 : ∀ x, g x ≤ 1 := fun x => by rcases hg x with h | h <;> simp [h]
  have hBp : 0 ≤ (B : ℝ) / p := div_nonneg (Nat.cast_nonneg _) hp.le
  induction N using Nat.strong_induction_on generalizing x with
  | h N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using mul_nonneg hBp (hf0 x)
    -- one step: `S_N x = g x + K S_{N-1} x`
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hstep : ∑ t ∈ range (M + 1), K.iterate t g x =
        g x + K.apply (fun y => ∑ t ∈ range M, K.iterate t g y) x := by
      rw [sum_range_succ', apply_finset_sum, add_comm]
      rfl
    rcases hg x with hx | hx
    · -- `x ∉ D`: one step and the induction hypothesis
      rw [hstep, hx, zero_add]
      calc K.apply (fun y => ∑ t ∈ range M, K.iterate t g y) x
          ≤ K.apply (fun y => B / p * f y) x := (K x).expect_mono fun y => ih M (by omega) y
        _ = B / p * K.apply f x := (K x).expect_mul _ _
        _ ≤ B / p * f x := mul_le_mul_of_nonneg_left (hK x) hBp
    · -- `x ∈ D`: then `f x = 1`
      have hfx : f x = 1 := le_antisymm (hf1 x) (hx ▸ hgf x)
      have hp1 : p ≤ 1 := by
        have := hblock x hx
        linarith [K.iterate_nonneg B hf0 x]
      rw [hfx, mul_one]
      by_cases hMB : M + 1 ≤ B
      · -- short horizon: at most one per step
        calc ∑ t ∈ range (M + 1), K.iterate t g x
            ≤ ∑ t ∈ range (M + 1), (1 : ℝ) := by
              refine sum_le_sum fun t _ => ?_
              simpa [Kernel.iterate_const] using K.iterate_mono t hg1 x
          _ = (M + 1 : ℕ) := by simp
          _ ≤ B := by exact_mod_cast hMB
          _ ≤ B / p := by
              rw [le_div_iff₀ hp]
              nlinarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
      · -- `B` steps, then restart with the induction hypothesis
        obtain ⟨R, hR⟩ : ∃ R, M + 1 = B + R := ⟨M + 1 - B, by omega⟩
        have hRlt : R < M + 1 := by
          rcases Nat.eq_zero_or_pos B with hB0 | hB0
          · exfalso
            have := hblock x hx
            rw [hB0, Kernel.iterate_zero, hfx] at this
            linarith
          · omega
        rw [hR, sum_range_add]
        have hfirst : ∑ t ∈ range B, K.iterate t g x ≤ B := by
          calc ∑ t ∈ range B, K.iterate t g x ≤ ∑ t ∈ range B, (1 : ℝ) :=
                sum_le_sum fun t _ => by simpa [Kernel.iterate_const] using K.iterate_mono t hg1 x
            _ = B := by simp
        have hrest : ∑ t ∈ range R, K.iterate (B + t) g x ≤ B / p * (1 - p) := by
          have hcomm : ∑ t ∈ range R, K.iterate (B + t) g x =
              K.iterate B (fun y => ∑ t ∈ range R, K.iterate t g y) x := by
            rw [iterate_finset_sum]
            exact sum_congr rfl fun t _ => by rw [Kernel.iterate_add_time]
          rw [hcomm]
          calc K.iterate B (fun y => ∑ t ∈ range R, K.iterate t g y) x
              ≤ K.iterate B (fun y => B / p * f y) x :=
                K.iterate_mono B (fun y => ih R hRlt y) x
            _ = B / p * K.iterate B f x := congrFun (K.iterate_mul B _ f) x
            _ ≤ B / p * (1 - p) := mul_le_mul_of_nonneg_left (hblock x hx) hBp
        have hsplit : (B : ℝ) + B / p * (1 - p) = B / p := by
          field_simp
          ring
        linarith

end Generic

/-! ### Constant configurations and disagreement -/

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

/-- A constant configuration is absorbing: every observable keeps its value. -/
lemma transition_iterate_constant (H : Kernel V) (c : C) (f : Config V C → ℝ) (n : ℕ) :
    (transition H).iterate n f (fun _ => c) = f (fun _ => c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Kernel.iterate_succ, transition_constant, ih]

omit [Fintype V] [DecidableEq V] [Fintype C] in
/-- Disagreement is `0` or `1`. -/
lemma disagreement_zero_or_one (s : Config V C) : disagreement s = 0 ∨ disagreement s = 1 := by
  classical
  unfold disagreement
  split <;> simp

/-- Disagreement cannot reappear: `K disagreement ≤ disagreement`. -/
lemma transition_disagreement_le (H : Kernel V) (s : Config V C) :
    (transition H).apply disagreement s ≤ disagreement s := by
  classical
  by_cases hs : ∃ c, s = fun _ => c
  · obtain ⟨c, rfl⟩ := hs
    rw [transition_constant]
  · have h1 : disagreement s = 1 := by
      unfold disagreement
      rw [if_neg hs]
    rw [h1]
    calc (transition H).apply disagreement s ≤ (transition H s).expect (fun _ => 1) :=
          (transition H s).expect_mono fun t => by
            rcases disagreement_zero_or_one t with h | h <;> simp [h]
      _ = 1 := (transition H s).expect_const 1

end Voter
