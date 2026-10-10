import Median.ExpanderGeneralPhaseI
import Median.ExpanderGeneralArith

/-! # Two-sample voting on expanders with a small imbalance

Cooper, Elsässer and Radzik, *The power of two choices in distributed voting* (ICALP 2014,
arXiv:1404.7479), Theorem 2: on a `d`-regular `n`-vertex graph, if the initial imbalance is
`ν₀ = (A − B)/n ≥ K λ_G` for an absolute constant `K`, two-sample voting completes in
`O(log n)` rounds and the initial majority wins.

The proof follows the paper's Section 7 ("Putting the phases together"): Phase I
(Corollary 2, `phaseI_expander`) brings the minority down to `n/20`, and Phases II and III,
formalized as Theorem 4 (`two_choices_expander_explicit`, applied with `ε = 1/4`, which needs
`λ_G ≤ 7/20`), take it from `n/20` to `0`.

* `two_choices_expander_general_explicit`: the explicit form, with `K = 4000`, `c = 1/20`,
  `α = ν₀/4000` in Phase I, and `T₂` further rounds.
* `two_choices_expander_general`: the `O(log n)` form, after `⌈C log n⌉` rounds with failure
  probability at most `1/n + (2 C log n + C) e^{−ν₀² n / C}`.

The paper states the failure probability as `o(1)`. Phase I (the paper's Lemma 2 and
Corollary 2) only gives the failure probability `e^{−Θ(α² n)}` per round with `α ≥ λ_G`, so the
bound here is in terms of `ν₀² n` (taking `α = ν₀/K`): it tends to `0` once `ν₀² n` is large
compared with `log log n` (for instance for fixed `ν₀ > 0`), that is, once the initial
difference `|A − B| = ν₀ n` is somewhat larger than `√n`. Without such a condition the
statement of Theorem 2 needs a major correction: on the complete graph `λ_G = 1/(n − 1)`,
and an initial difference `|A − B|` bounded by a constant does not let the majority win with
probability tending to `1`.
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

/-- The probability of the complement of an event: `𝔼[1 − 1_P] = 1 − 𝔼[1_P]`. -/
lemma expList_ite_compl {α : Type*} [Fintype α] [Nonempty α] (T : ℕ) (P : List α → Prop)
    [DecidablePred P] :
    expList α T (fun l => if P l then (0 : ℝ) else 1)
      = 1 - expList α T (fun l => if P l then (1 : ℝ) else 0) := by
  have h := expList_add T (fun l => if P l then (1 : ℝ) else 0)
    (fun l => if P l then (0 : ℝ) else 1)
  have h1 : (fun l => (if P l then (1 : ℝ) else 0) + if P l then (0 : ℝ) else 1)
      = fun _ => (1 : ℝ) := funext fun l => by split_ifs <;> norm_num
  rw [h1, expList_const] at h
  linarith

section Compose

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Composition of the phases** (the strong Markov property at the first time `t` with
`B ≤ c n`): if `c ≤ ε/5` and `λ_G ≤ 3/5 − ε`, then after `k + T₂` rounds consensus on `a` fails
with probability at most `P(B > c n for all t ≤ k) + (24/25)^{T₂} n + (k + T₂) e^{−ε n / 24250}`,
since Theorem 4 (`two_choices_expander_explicit`) applies from time `t`. -/
theorem not_consensus_le {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c ε : ℝ}
    (hε : 0 < ε) (hlam : lambdaG G d ≤ 3 / 5 - ε) (hc : c ≤ ε / 5) (a : Bool) (T₂ k : ℕ)
    (y : V → Bool) :
    expList (GraphRound G) (k + T₂) (fun l => if graphRun G y l = fun _ => a then (0 : ℝ) else 1)
      ≤ expList (GraphRound G) k (fun l => if ∃ t ≤ k,
            (minority a (graphRun G y (l.take t)) : ℝ) ≤ c * Fintype.card V then (0 : ℝ) else 1)
        + (24 / 25 : ℝ) ^ T₂ * Fintype.card V
        + ((k : ℝ) + T₂) * exp (-(ε * Fintype.card V / 24250)) := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  -- from a configuration with `B ≤ c n`, Theorem 4
  have hhit : ∀ (k : ℕ) (y : V → Bool), (minority a y : ℝ) ≤ c * Fintype.card V →
      expList (GraphRound G) (k + T₂)
          (fun l => if graphRun G y l = fun _ => a then (0 : ℝ) else 1)
        ≤ (24 / 25 : ℝ) ^ T₂ * Fintype.card V
          + ((k : ℝ) + T₂) * exp (-(ε * Fintype.card V / 24250)) := by
    intro k y hy
    have h4 := two_choices_expander_explicit G hd hreg hε hlam a y
      (hy.trans (mul_le_mul_of_nonneg_right hc hn0)) (k + T₂)
    rw [expList_ite_compl]
    have hB : (minority a y : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ _
    have hp : (24 / 25 : ℝ) ^ (k + T₂) ≤ (24 / 25) ^ T₂ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have : (24 / 25 : ℝ) ^ (k + T₂) * minority a y ≤ (24 / 25) ^ T₂ * Fintype.card V :=
      mul_le_mul hp hB (Nat.cast_nonneg _) (by positivity)
    push_cast at h4
    linarith
  induction k generalizing y with
  | zero =>
    by_cases hy : (minority a y : ℝ) ≤ c * Fintype.card V
    · refine (hhit 0 y hy).trans ?_
      rw [add_assoc]
      exact le_add_of_nonneg_left (expList_nonneg fun l => by split_ifs <;> norm_num)
    · simp only [expList_zero]
      rw [if_neg (by rintro ⟨t, -, ht⟩; exact hy (by simpa [graphRun] using ht))]
      have h1 := (expList_le_expList (α := GraphRound G) (T := 0 + T₂)
        (F := fun l => if graphRun G y l = fun _ => a then (0 : ℝ) else 1)
        (fun l => show _ ≤ (1 : ℝ) by split_ifs <;> norm_num)).trans_eq (expList_const _ 1)
      have : 0 ≤ ((0 : ℕ) + (T₂ : ℝ)) * exp (-(ε * Fintype.card V / 24250)) := by positivity
      have : 0 ≤ (24 / 25 : ℝ) ^ T₂ * Fintype.card V := by positivity
      linarith
  | succ k ih =>
    by_cases hy : (minority a y : ℝ) ≤ c * Fintype.card V
    · refine (hhit (k + 1) y hy).trans ?_
      rw [add_assoc]
      exact le_add_of_nonneg_left (expList_nonneg fun l => by split_ifs <;> norm_num)
    · -- not hit at time `0`: shift the time by one round
      rw [show k + 1 + T₂ = k + T₂ + 1 by omega, expList_succ, expList_succ k]
      have hstep : ∀ r : GraphRound G,
          expList (GraphRound G) (k + T₂)
              (fun l => if graphRun G y (r :: l) = fun _ => a then (0 : ℝ) else 1)
            ≤ expList (GraphRound G) k (fun l => if ∃ t ≤ k + 1,
                (minority a (graphRun G y ((r :: l).take t)) : ℝ) ≤ c * Fintype.card V
                then (0 : ℝ) else 1)
              + ((24 / 25 : ℝ) ^ T₂ * Fintype.card V
                + ((k : ℝ) + T₂) * exp (-(ε * Fintype.card V / 24250))) := by
        intro r
        have e : (fun l => if ∃ t ≤ k + 1,
              (minority a (graphRun G y ((r :: l).take t)) : ℝ) ≤ c * Fintype.card V
              then (0 : ℝ) else 1)
            = fun l => if ∃ t ≤ k, (minority a (graphRun G (graphStep G y r) (l.take t)) : ℝ)
              ≤ c * Fintype.card V then (0 : ℝ) else 1 := by
          funext l
          refine if_congr ⟨?_, fun ⟨s, hs, h⟩ => ⟨s + 1, by omega, h⟩⟩ rfl rfl
          rintro ⟨t, ht, h⟩
          cases t with
          | zero => exact absurd h hy
          | succ s => exact ⟨s, by omega, h⟩
        rw [e, ← add_assoc]
        exact ih (graphStep G y r)
      refine (avg_le_avg hstep).trans ?_
      rw [avg_add, avg_const]
      have : 0 ≤ exp (-(ε * Fintype.card V / 24250)) := (exp_pos _).le
      push_cast
      linarith

end Compose

/-- **Theorem 2, explicit form**: on a `d`-regular `n`-vertex graph with
`ν₀ = imbalance a x > 0` and `4000 λ_G ≤ ν₀`, after `T₁ + T₂` rounds, where
`T₁ = phaseIRounds ν₀ (1/20)`, every vertex holds `a`, except with probability at most
`T₁ (e^{−α² n / 120} + e^{−α² n / 800}) + (24/25)^{T₂} n + (T₁ + T₂) e^{−n / 97000}` with
`α = ν₀ / 4000`. -/
theorem two_choices_expander_general_explicit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d)
    (hreg : G.IsRegularOfDegree d) (a : Bool) (x : V → Bool) (hν0 : 0 < imbalance a x)
    (hlam : 4000 * lambdaG G d ≤ imbalance a x) (T₂ : ℕ) :
    1 - ((phaseIRounds (imbalance a x) (1 / 20) : ℝ)
            * (exp (-((imbalance a x / 4000) ^ 2 * (1 / 20) * Fintype.card V / 6))
              + exp (-((imbalance a x / 4000) ^ 2 * (1 / 20) ^ 2 * Fintype.card V / 2)))
          + (24 / 25 : ℝ) ^ T₂ * Fintype.card V
          + ((phaseIRounds (imbalance a x) (1 / 20) : ℝ) + T₂)
            * exp (-((Fintype.card V : ℝ) / 97000)))
      ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) (1 / 20) + T₂)
          (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  have hν1 : imbalance a x ≤ 1 := by
    have hsum : (majority a x : ℝ) + minority a x = Fintype.card V := by
      exact_mod_cast majority_add_minority a x
    have hB : (0 : ℝ) ≤ minority a x := Nat.cast_nonneg _
    unfold imbalance
    rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with hn | hn
    · rw [← hn, div_zero]
      norm_num
    · rw [div_le_iff₀ hn]
      linarith
  have hsq : (2 / 9 : ℝ) ≤ √(1 / 20) := by
    rw [show (2 / 9 : ℝ) = √((2 / 9) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- Phase I (Corollary 2), then Phases II and III (Theorem 4 with `ε = 1/4`)
  have h1 := phaseI_expander G hd hreg (c := 1 / 20) (α := imbalance a x / 4000) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) a x (by linarith)
  have h2 := not_consensus_le G hd hreg (c := 1 / 20) (ε := 1 / 4) (by norm_num) (by linarith)
    (by norm_num) a T₂ (phaseIRounds (imbalance a x) (1 / 20)) x
  rw [expList_ite_compl, expList_ite_compl] at h2
  have he : (1 / 4 : ℝ) * Fintype.card V / 24250 = Fintype.card V / 97000 := by ring
  rw [he] at h2
  linarith

/-- **Theorem 2** (`O(log n)` form): there are absolute constants `K` and `C` such that on every
`d`-regular `n`-vertex graph, if the initial imbalance in favour of `a` is
`ν₀ = (A − B)/n ≥ K λ_G`, then after `⌈C log n⌉` rounds every vertex holds `a`, except with
probability at most `1/n + (2 C log n + C) e^{−ν₀² n / C}`. -/
theorem two_choices_expander_general : ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ},
      0 < d → G.IsRegularOfDegree d → ∀ (a : Bool) (x : V → Bool),
        K * lambdaG G d ≤ imbalance a x →
        1 - (1 / (Fintype.card V : ℝ) + (2 * C * log (Fintype.card V) + C)
              * exp (-(imbalance a x ^ 2 * Fintype.card V / C)))
          ≤ expList (GraphRound G) ⌈C * log (Fintype.card V)⌉₊
              (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  refine ⟨4000, 2 * 10 ^ 10, by norm_num, by norm_num, ?_⟩
  intro V _ _ G _ d hd hreg a x hlam
  exact general_of_explicit G hd hreg a x hlam fun h T₂ =>
    two_choices_expander_general_explicit G hd hreg a x h hlam T₂

end Median.ExpanderGeneral
