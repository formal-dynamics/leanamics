import Epidemics.Revisited.ShrinkingAux

/-! # Lower bounds for rumor spreading: generic tools (EPI-8, lower bounds)

Doerr and Kostrygin, *Randomized rumor spreading revisited* (ICALP 2017; long version
arXiv:2303.11150), lower bounds of Theorems 51, 52 and 53. The paper derives them from its
general lower bounds (Theorems 27, 38 and 48), joined through Lemma 20, which needs a major
correction (see `Lemma20`). The lower bounds here follow a direct route instead, made of three
generic tools.

* `reach_le_of_expect_card_le` (first moment): if one round multiplies the expected number of
  informed nodes by at most `μ`, then at least `m` nodes are informed after `t` rounds with
  probability at most `μ^t |S| / m`. This replaces Theorem 27 (lower exponential growth).
* `reach_add_le` (Markov property at a fixed time): the probability of having informed `m`
  nodes after `s + t` rounds is at most the probability of having informed `m'` nodes after `s`
  rounds plus a bound on the probability of informing `m` nodes in `t` rounds from any state
  with fewer than `m'` informed nodes. Splitting at a fixed time, not at the hitting time of
  `m'`, avoids any overshoot estimate such as Lemma 20.
* `envelope_le` (deterministic lower envelope): if in one round an observable `V` falls below
  `f v` (from a state with `V ≥ v`) with probability at most `δ v`, then after `t` rounds it is
  below `f^[t] v` with probability at most `∑_{i < t} δ (f^[i] v)`. This is the round-by-round
  form of the phase arguments of Theorems 38 and 48 (Lemmas 42 and 50). `envelope_seq_le` is
  the same with an explicit target sequence `g i` in place of the iterates `f^[i] v`.

Throughout, `1 - P.notYet m t S` is the probability that at least `m` nodes are informed after
`t` rounds started from `S`, that is, `P[T(|S|, m) ≤ t]`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

/-! ### Complements of iterated observables -/

section Kernel
variable {α : Type*} [Fintype α]

/-- `1 - E[g(X_t)] = E[1 - g(X_t)]`. -/
lemma one_sub_iterate (K : Kernel α) (t : ℕ) (g : α → ℝ) (a : α) :
    1 - K.iterate t g a = K.iterate t (fun b => 1 - g b) a := by
  have h : (fun b => 1 - g b) = fun b => (fun _ => (1 : ℝ)) b + (-1) * g b := by
    funext b
    ring
  rw [h, K.iterate_add, K.iterate_mul, K.iterate_const]
  ring

/-- **Deterministic lower envelope.** Suppose that from every state `a` with `v ≤ V a`, the
observable `V` falls below `f v` in one round with probability at most `δ v ≥ 0`. Then, started
from `a` with `v ≤ V a`, it is below `f^[t] v` after `t` rounds with probability at most
`∑_{i < t} δ (f^[i] v)`. (The round-by-round form of the leapfrog arguments of Lemmas 42 and 50
of the paper.) -/
theorem envelope_le (K : Kernel α) (V : α → ℝ) (f δ : ℝ → ℝ) (hδ : ∀ v, 0 ≤ δ v)
    (h : ∀ a v, v ≤ V a → (K a).prob (fun b => V b < f v) ≤ δ v)
    (t : ℕ) (a : α) (v : ℝ) (hv : v ≤ V a) :
    K.event (fun b => V b < f^[t] v) t a ≤ ∑ i ∈ range t, δ (f^[i] v) := by
  classical
  induction t generalizing a v with
  | zero =>
    rw [Kernel.event_eq_iterate, Kernel.iterate_zero]
    simp [not_lt.mpr hv]
  | succ t ih =>
    have hsum : 0 ≤ ∑ i ∈ range t, δ (f^[i] (f v)) := sum_nonneg fun i _ => hδ _
    have hpt : ∀ b, K.event (fun c => V c < f^[t] (f v)) t b ≤
        (if V b < f v then (1 : ℝ) else 0) + ∑ i ∈ range t, δ (f^[i] (f v)) := by
      intro b
      by_cases hb : V b < f v
      · rw [if_pos hb]
        have := K.event_le_one (fun c => V c < f^[t] (f v)) t b
        linarith only [this, hsum]
      · rw [if_neg hb, zero_add]
        exact ih b (f v) (not_lt.mp hb)
    have hstep : K.event (fun b => V b < f^[t + 1] v) (t + 1) a =
        (K a).expect (fun b => K.event (fun c => V c < f^[t] (f v)) t b) := by
      rw [Function.iterate_succ_apply, Kernel.event_eq_iterate, Kernel.iterate_succ,
        Kernel.apply]
      congr 1
    rw [hstep, sum_range_succ']
    calc (K a).expect (fun b => K.event (fun c => V c < f^[t] (f v)) t b)
        ≤ (K a).expect (fun b => (if V b < f v then (1 : ℝ) else 0) +
            ∑ i ∈ range t, δ (f^[i] (f v))) := (K a).expect_mono hpt
      _ = (K a).prob (fun b => V b < f v) + ∑ i ∈ range t, δ (f^[i] (f v)) := by
        rw [Distribution.expect_add, Distribution.expect_const, Distribution.prob_eq_expect]
      _ ≤ δ v + ∑ i ∈ range t, δ (f^[i] (f v)) := by
        linarith only [h a v hv]
      _ = ∑ i ∈ range t, δ (f^[i + 1] v) + δ (f^[0] v) := by
        simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
        ring

/-- **Lower envelope along a target sequence.** Suppose that, for every `i`, from every state
`a` with `g i ≤ V a` the observable `V` falls below `g (i + 1)` in one round with probability
at most `δ i ≥ 0`. Then, started from `a` with `g 0 ≤ V a`, it is below `g t` after `t` rounds
with probability at most `∑_{i < t} δ i`. (The form of `envelope_le` with explicit targets, as
the phase sequences `u_j` and `ε_j` of Lemmas 40 and 49.) -/
theorem envelope_seq_le (K : Kernel α) (V : α → ℝ) (g δ : ℕ → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (h : ∀ i a, g i ≤ V a → (K a).prob (fun b => V b < g (i + 1)) ≤ δ i)
    (t : ℕ) (a : α) (ha : g 0 ≤ V a) :
    K.event (fun b => V b < g t) t a ≤ ∑ i ∈ range t, δ i := by
  classical
  induction t generalizing g δ a with
  | zero =>
    rw [Kernel.event_eq_iterate, Kernel.iterate_zero]
    simp [not_lt.mpr ha]
  | succ t ih =>
    have ih' := ih (fun i => g (i + 1)) (fun i => δ (i + 1)) (fun i => hδ _)
      (fun i a ha => h (i + 1) a ha)
    have hsum : 0 ≤ ∑ i ∈ range t, δ (i + 1) := sum_nonneg fun i _ => hδ _
    have hpt : ∀ b, K.event (fun c => V c < g (t + 1)) t b ≤
        (if V b < g 1 then (1 : ℝ) else 0) + ∑ i ∈ range t, δ (i + 1) := by
      intro b
      by_cases hb : V b < g 1
      · rw [if_pos hb]
        have := K.event_le_one (fun c => V c < g (t + 1)) t b
        linarith only [this, hsum]
      · rw [if_neg hb, zero_add]
        exact ih' b (not_lt.mp hb)
    have hstep : K.event (fun b => V b < g (t + 1)) (t + 1) a =
        (K a).expect (fun b => K.event (fun c => V c < g (t + 1)) t b) := by
      rw [Kernel.event_eq_iterate, Kernel.iterate_succ, Kernel.apply]
      congr 1
    rw [hstep, sum_range_succ']
    calc (K a).expect (fun b => K.event (fun c => V c < g (t + 1)) t b)
        ≤ (K a).expect (fun b => (if V b < g 1 then (1 : ℝ) else 0) +
            ∑ i ∈ range t, δ (i + 1)) := (K a).expect_mono hpt
      _ = (K a).prob (fun b => V b < g 1) + ∑ i ∈ range t, δ (i + 1) := by
        rw [Distribution.expect_add, Distribution.expect_const, Distribution.prob_eq_expect]
      _ ≤ δ 0 + ∑ i ∈ range t, δ (i + 1) := by
        linarith only [h 0 a ha]
      _ = ∑ i ∈ range t, δ (i + 1) + δ 0 := by ring

end Kernel

/-! ### Reaching `m` informed nodes -/

variable {n : ℕ}

/-- `1 - P[T(|S|, m) > t]` is the expectation after `t` rounds of the indicator of having at
least `m` informed nodes. -/
lemma one_sub_notYet_eq (P : RumorProcess n) (m : ℝ) (t : ℕ) (S : Finset (Fin n)) :
    1 - P.notYet m t S = P.K.iterate t (fun T => 1 - below m T) S := by
  rw [notYet_below, one_sub_iterate]

lemma iterate_card_le (P : RumorProcess n) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ∀ S : Finset (Fin n), (P.K S).expect (fun T => (T.card : ℝ)) ≤ μ * S.card)
    (t : ℕ) (S : Finset (Fin n)) :
    P.K.iterate t (fun T => (T.card : ℝ)) S ≤ μ ^ t * S.card := by
  induction t generalizing S with
  | zero => simp
  | succ t ih =>
    rw [Kernel.iterate_succ, Kernel.apply]
    calc (P.K S).expect (P.K.iterate t (fun T => (T.card : ℝ)))
        ≤ (P.K S).expect (fun T => μ ^ t * (T.card : ℝ)) := (P.K S).expect_mono ih
      _ = μ ^ t * (P.K S).expect (fun T => (T.card : ℝ)) := Distribution.expect_mul _ _ _
      _ ≤ μ ^ t * (μ * S.card) := mul_le_mul_of_nonneg_left (h S) (pow_nonneg hμ t)
      _ = μ ^ (t + 1) * S.card := by ring

/-- **Growth lower bound by the first moment** (replaces Theorem 27 for the instances): if one
round multiplies the expected number of informed nodes by at most `μ`, then at least `m > 0`
nodes are informed after `t` rounds with probability at most `μ^t |S| / m`. -/
theorem reach_le_of_expect_card_le (P : RumorProcess n) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ∀ S : Finset (Fin n), (P.K S).expect (fun T => (T.card : ℝ)) ≤ μ * S.card)
    {m : ℝ} (hm : 0 < m) (t : ℕ) (S : Finset (Fin n)) :
    1 - P.notYet m t S ≤ μ ^ t * S.card / m := by
  have hpt : ∀ T : Finset (Fin n), 1 - below m T ≤ m⁻¹ * (T.card : ℝ) := by
    intro T
    have hT : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    by_cases hlt : (T.card : ℝ) < m
    · simp only [below, if_pos hlt, sub_self]
      exact mul_nonneg (inv_nonneg.mpr hm.le) hT
    · simp only [below, if_neg hlt, sub_zero]
      rw [← div_eq_inv_mul, one_le_div hm]
      exact not_lt.mp hlt
  rw [one_sub_notYet_eq]
  calc P.K.iterate t (fun T => 1 - below m T) S
      ≤ P.K.iterate t (fun T => m⁻¹ * (T.card : ℝ)) S := P.K.iterate_mono t hpt S
    _ = m⁻¹ * P.K.iterate t (fun T => (T.card : ℝ)) S := by rw [P.K.iterate_mul]
    _ ≤ m⁻¹ * (μ ^ t * S.card) :=
      mul_le_mul_of_nonneg_left (iterate_card_le P hμ h t S) (inv_nonneg.mpr hm.le)
    _ = μ ^ t * S.card / m := by ring

/-- If every uninformed node is informed with probability at most `c |S| / n`, the expected
number of informed nodes after one round is at most `(1 + c) |S|`. -/
lemma expect_card_le_of_informProb_le (P : RumorProcess n) (S : Finset (Fin n)) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x ∉ S, P.informProb S x ≤ c * (S.card / (n : ℝ))) :
    (P.K S).expect (fun T => (T.card : ℝ)) ≤ (1 + c) * S.card := by
  rw [expect_card_eq]
  have hsum : ∑ x ∈ (univ : Finset (Fin n)) \ S, P.informProb S x ≤
      ((n : ℝ) - S.card) * (c * (S.card / (n : ℝ))) := by
    have := sum_le_sum (s := (univ : Finset (Fin n)) \ S) fun x hx => h x (mem_sdiff.mp hx).2
    rwa [sum_const, nsmul_eq_mul, card_compl_cast] at this
  have hk : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hkn : (S.card : ℝ) ≤ n := by
    have := card_le_univ S
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hmul : ((n : ℝ) - S.card) * (c * (S.card / (n : ℝ))) ≤ c * S.card := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero, mul_zero, mul_zero]
      exact mul_nonneg hc hk
    · have hfrac : ((n : ℝ) - S.card) / n ≤ 1 := by
        rw [div_le_one hpos]
        linarith
      have hfrac0 : 0 ≤ ((n : ℝ) - S.card) / n := div_nonneg (by linarith) hpos.le
      calc ((n : ℝ) - S.card) * (c * (S.card / (n : ℝ)))
          = c * S.card * (((n : ℝ) - S.card) / n) := by ring
        _ ≤ c * S.card * 1 :=
          mul_le_mul_of_nonneg_left hfrac (mul_nonneg hc hk)
        _ = c * S.card := mul_one _
  linarith only [hsum, hmul]

/-- Bernoulli's inequality in the form used for push: `1 - (1 - 1/n)^k ≤ k / n`. -/
lemma one_sub_one_sub_inv_pow_le (hn : 0 < n) (k : ℕ) :
    1 - (1 - 1 / (n : ℝ)) ^ k ≤ k / (n : ℝ) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : -2 ≤ -(1 / (n : ℝ)) := by
    have : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnr]
      exact_mod_cast hn
    linarith
  have hb := one_add_mul_le_pow h1n k
  rw [← sub_eq_add_neg] at hb
  rw [div_eq_mul_one_div (k : ℝ) (n : ℝ)]
  linarith only [hb]

/-- **Markov property at a fixed time, lower-bound form.** If from every state with fewer than
`m'` informed nodes at least `m` nodes are informed after `t` rounds with probability at most
`B`, then from `S` at least `m` nodes are informed after `s + t` rounds with probability at most
`P[at least m' informed after s rounds] + B`. -/
theorem reach_add_le (P : RumorProcess n) {m m' B : ℝ} (hB : 0 ≤ B) (s t : ℕ)
    (hT : ∀ T : Finset (Fin n), (T.card : ℝ) < m' → 1 - P.notYet m t T ≤ B)
    (S : Finset (Fin n)) :
    1 - P.notYet m (s + t) S ≤ (1 - P.notYet m' s S) + B := by
  have hpt : ∀ T : Finset (Fin n),
      1 - P.K.iterate t (below m) T ≤ (1 - below m' T) + B := by
    intro T
    rw [← notYet_below]
    by_cases h : (T.card : ℝ) < m'
    · have hb : below m' T = 1 := by simp [below, h]
      have := hT T h
      linarith only [this, hb]
    · have hb : below m' T = 0 := by simp [below, h]
      have := notYet_nonneg P m t T
      linarith only [this, hb, hB]
  rw [notYet_below, P.K.iterate_add_time, one_sub_iterate, one_sub_notYet_eq]
  calc P.K.iterate s (fun T => 1 - P.K.iterate t (below m) T) S
      ≤ P.K.iterate s (fun T => (1 - below m' T) + B) S := P.K.iterate_mono s hpt S
    _ = P.K.iterate s (fun T => 1 - below m' T) S + B := by
      rw [P.K.iterate_add, P.K.iterate_const]

end Epidemics.Revisited
