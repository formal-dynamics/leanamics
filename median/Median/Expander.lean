import Median.ExpanderStep
import Median.ExpanderDrift

/-! # Two-sample voting on expanders

Cooper, Elsässer and Radzik, *The power of two choices in distributed voting* (ICALP 2014,
arXiv:1404.7479), Theorem 4: on a `d`-regular `n`-vertex graph with `λ_G = 3/5 − ε`, a minority
of size at most `(ε/5) n` disappears within `O(log n)` rounds with high probability, and the
initial majority wins.

* `expander_mixing`: the expander mixing lemma (the paper's Lemma 3),
  `|E(S, T) − d |S| |T| / n| ≤ λ_G d √(|S| |T|)`.
* `expected_minority_step`: the expectation bound in the proof of the paper's Lemma 5, with
  `α = 3/10`: under the sparsity hypothesis below, `𝔼|B'| ≤ (1 − (1 − 2α)(1 − 3α)) |B| =
  (24/25) |B|`.
* `phaseII_step`: the paper's Lemma 5 with `α = 3/10` (so `γ = 1/50`): if every superset `S` of
  the minority `B` with `|S| ≤ (1 + 1/α) |B|` spans at most `α d |S|` edges, one round reduces
  `|B|` by the factor `1 − γ` except with probability `e^{−|B|/4850}`.
* `two_choices_expander_explicit`: Theorem 4 with an explicit failure probability after `T`
  rounds, `(24/25)^T |B| + T e^{−ε n / 24250}`.
* `two_choices_expander`: Theorem 4 in `O(log n)` form, after `⌈C log n⌉` rounds with failure
  probability `1/n + (C log n + 1) e^{−ε n / C}`, which tends to `0`
  (`two_choices_failure_tendsto`) for fixed `ε > 0`.

The paper proves Theorem 4 through its Lemma 6 and Corollary 4 (Phase II, from `(ε/5) n` down
to a slowly growing `ω`) and its Lemma 9 and Corollary 5 (Phase III, from `ω` to `0`). Here the
two phases are replaced by one supermartingale argument (`expList_le_of_contract`): while
`|B| ≤ (ε/5) n`, every set of at most `ε n` vertices is sparse by the mixing lemma
(`sparse_of_lambdaG`), so the expected minority contracts by `24/25` in every round, and one
round leaves the region `|B| ≤ (ε/5) n` with probability at most `e^{−ε n / 24250}`.
-/

namespace Median
open Finset Dynamics Real Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Expander mixing lemma** (the paper's Lemma 3): on a `d`-regular `n`-vertex graph, for all
vertex sets `S` and `T`, `|E(S, T) − d |S| |T| / n| ≤ λ_G d √(|S| |T|)`. -/
theorem expander_mixing {d : ℕ} (hreg : G.IsRegularOfDegree d) (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V|
      ≤ lambdaG G d * d * √((S.card : ℝ) * T.card) :=
  expander_mixing_aux G hreg S T

/-- On a `d`-regular graph with `λ_G ≤ 3/5 − ε`, every set of at most `ε n` vertices spans at
most `(3/10) d |S|` edges: `E(S, S) ≤ |S|² d / n + λ_G d |S| ≤ (ε + 3/5 − ε) d |S|`. -/
theorem sparse_of_lambdaG {d : ℕ} (hreg : G.IsRegularOfDegree d) {ε : ℝ}
    (hlam : lambdaG G d ≤ 3 / 5 - ε) (S : Finset V)
    (hS : (S.card : ℝ) ≤ ε * Fintype.card V) :
    (edgeCount G S S : ℝ) ≤ 3 / 5 * d * S.card := by
  have h := expander_mixing G hreg S S
  rw [Real.sqrt_mul_self (Nat.cast_nonneg _)] at h
  have h1 := (abs_le.mp h).2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have h2 : (d : ℝ) * S.card * S.card / Fintype.card V ≤ ε * d * S.card := by
    rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with hn | hn
    · rw [← hn, div_zero]
      have : (S.card : ℝ) ≤ 0 := by
        have := Finset.card_le_univ S
        have : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast this
        linarith
      have : (S.card : ℝ) = 0 := le_antisymm this hs0
      rw [this]
      simp
    · rw [div_le_iff₀ hn]
      have := mul_le_mul_of_nonneg_left hS (mul_nonneg hd0 hs0)
      linarith
  have h3 : lambdaG G d * d * S.card ≤ (3 / 5 - ε) * d * S.card :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlam hd0) hs0
  linarith

/-- **The expected minority contracts** (the bound `𝔼Δ ≥ (1 − 2α)(1 − 3α) B` in the proof of the
paper's Lemma 5, with `α = 3/10`): if every superset `S ⊇ B` of the minority `B` with
`|S| ≤ (1 + 1/α) |B|` spans at most `α d |S|` edges, then after one round
`𝔼|B'| ≤ (1 − (1 − 2α)(1 − 3α)) |B| = (24/25) |B|`. -/
theorem expected_minority_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool)
    (hsparse : ∀ S : Finset V, univ.filter (fun v => x v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ (1 + 1 / (3 / 10)) * minority a x →
        (edgeCount G S S : ℝ) ≤ 2 * (3 / 10 * d * S.card)) :
    avg (fun r : GraphRound G => (minority a (graphStep G x r) : ℝ))
      ≤ (1 - (1 - 2 * (3 / 10)) * (1 - 3 * (3 / 10))) * minority a x := by
  have h := avg_minority_step_le hd hreg a x fun S hBS hS => by
    have := hsparse S hBS (by norm_num at hS ⊢; linarith)
    linarith
  norm_num at h ⊢
  linarith

/-- **One round shrinks a sparse minority** (the paper's Lemma 5 with `α = 3/10`,
`γ = (1 − 2α)(1 − 3α)/2 = 1/50`): if every superset `S ⊇ B` of the minority `B` with
`|S| ≤ (1 + 1/α) |B|` spans at most `α d |S|` edges (`E(S, S) ≤ 2 α d |S|`), then one round
reduces the minority to at most `(1 − γ) |B|`, with probability at least `1 − e^{−|B|/4850}`. -/
theorem phaseII_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool)
    (hsparse : ∀ S : Finset V, univ.filter (fun v => x v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ (1 + 1 / (3 / 10)) * minority a x →
        (edgeCount G S S : ℝ) ≤ 2 * (3 / 10 * d * S.card)) :
    1 - exp (-((minority a x : ℝ) / 4850))
      ≤ avg (fun r : GraphRound G =>
          if (minority a (graphStep G x r) : ℝ) ≤ (1 - 1 / 50) * minority a x then (1 : ℝ)
          else 0) := by
  have hsp : ∀ S : Finset V, univ.filter (fun v => x v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ 13 / 3 * minority a x → (edgeCount G S S : ℝ) ≤ 3 / 5 * d * S.card :=
    fun S hBS hS => by
      have := hsparse S hBS (by norm_num at hS ⊢; linarith)
      linarith
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  have htail := tail_minority_step hd hreg a x hsp (m := minority a x) le_rfl
  have hpt (r : GraphRound G) :
      1 - (if 49 / 50 * (minority a x : ℝ) ≤ minority a (graphStep G x r) then (1 : ℝ) else 0)
        ≤ if (minority a (graphStep G x r) : ℝ) ≤ (1 - 1 / 50) * minority a x then (1 : ℝ)
          else 0 := by
    split_ifs with h1 h2 h2 <;> norm_num at *
    linarith
  calc 1 - exp (-((minority a x : ℝ) / 4850))
      ≤ 1 - avg (fun r : GraphRound G =>
          if 49 / 50 * (minority a x : ℝ) ≤ minority a (graphStep G x r) then (1 : ℝ)
          else 0) := by linarith
    _ = avg (fun r : GraphRound G => 1 - (if 49 / 50 * (minority a x : ℝ)
          ≤ minority a (graphStep G x r) then (1 : ℝ) else 0)) := by
        rw [avg_sub, avg_const]
    _ ≤ _ := avg_le_avg hpt

/-- **Theorem 4, explicit form**: on a `d`-regular `n`-vertex graph with `λ_G ≤ 3/5 − ε`, if the
minority (the vertices whose opinion differs from `a`) has size at most `(ε/5) n`, then after `T`
rounds every vertex holds `a`, except with probability at most
`(24/25)^T |B| + T e^{−ε n / 24250}`. -/
theorem two_choices_expander_explicit {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d)
    {ε : ℝ} (hε : 0 < ε) (hlam : lambdaG G d ≤ 3 / 5 - ε) (a : Bool) (x : V → Bool)
    (hx : (minority a x : ℝ) ≤ ε / 5 * Fintype.card V) (T : ℕ) :
    1 - ((24 / 25 : ℝ) ^ T * minority a x + T * exp (-(ε * Fintype.card V / 24250)))
      ≤ expList (GraphRound G) T
          (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  have : Nonempty (GraphRound G) := inferInstance
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set m : ℝ := ε / 5 * n with hm
  have hm0 : 0 ≤ m := by positivity
  let Good : (V → Bool) → Prop := fun y => (minority a y : ℝ) ≤ m
  -- inside the region every relevant set is sparse
  have hsp : ∀ y : V → Bool, Good y → ∀ S : Finset V, univ.filter (fun v => y v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ 13 / 3 * minority a y → (edgeCount G S S : ℝ) ≤ 3 / 5 * d * S.card := by
    intro y hy S _ hS
    refine sparse_of_lambdaG G hreg hlam S ?_
    have : (13 / 3 : ℝ) * minority a y ≤ 13 / 3 * m := by
      have : (minority a y : ℝ) ≤ m := hy
      linarith
    have : 13 / 3 * m ≤ ε * n := by rw [hm]; nlinarith
    linarith
  let f : (V → Bool) → ℝ := fun y => if y = fun _ => a then 0 else 1
  have hf1 : ∀ y, f y ≤ 1 := fun y => by simp only [f]; split_ifs <;> norm_num
  have hfΦ : ∀ y, Good y → f y ≤ (minority a y : ℝ) := fun y _ => by
    simp only [f]
    split_ifs with h
    · exact Nat.cast_nonneg _
    · have : ∃ v, y v ≠ a := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      obtain ⟨v, hv⟩ := this
      have : 1 ≤ minority a y :=
        Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
      exact_mod_cast this
  have hdrift : ∀ y, Good y →
      avg (fun r => (minority a (graphStep G y r) : ℝ)) ≤ 24 / 25 * minority a y :=
    fun y hy => avg_minority_step_le hd hreg a y (hsp y hy)
  have hexit : ∀ y, Good y →
      avg (fun r => if Good (graphStep G y r) then (0 : ℝ) else 1)
        ≤ exp (-(ε * n / 24250)) := by
    intro y hy
    have htail := tail_minority_step hd hreg a y (hsp y hy) (m := m) hy
    have he : -(m / 4850) = -(ε * n / 24250) := by rw [hm]; ring
    rw [he] at htail
    refine le_trans (avg_le_avg fun r => ?_) htail
    simp only [Good]
    split_ifs with h1 h2 h2 <;> norm_num
    push Not at h1
    exact h2 (by linarith)
  have key := expList_le_of_contract (graphStep G) (fun y => (minority a y : ℝ)) f Good
    (ρ := 24 / 25) (q := exp (-(ε * n / 24250))) (by norm_num) (exp_pos _).le hf1
    (fun y => Nat.cast_nonneg _) hfΦ hdrift hexit T x hx
  have hsum : expList (GraphRound G) T
        (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0)
      + expList (GraphRound G) T (fun l => f (l.foldl (graphStep G) x)) = 1 := by
    rw [← expList_add]
    calc expList (GraphRound G) T (fun l => (if graphRun G x l = fun _ => a then (1 : ℝ) else 0)
          + f (l.foldl (graphStep G) x))
        = expList (GraphRound G) T (fun _ => (1 : ℝ)) := by
          congr 1
          funext l
          simp only [f, graphRun]
          split_ifs <;> norm_num
      _ = 1 := expList_const T 1
  linarith

/-- **Theorem 4** (`O(log n)` form): there is an absolute constant `C` such that on every
`d`-regular `n`-vertex graph with `λ_G ≤ 3/5 − ε`, a minority of size at most `(ε/5) n`
disappears and the majority opinion `a` wins within `⌈C log n⌉` rounds, except with probability
at most `1/n + (C log n + 1) e^{−ε n / C}` (which tends to `0`, `two_choices_failure_tendsto`).
The proof gives `C = 25000`. -/
theorem two_choices_expander : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ},
      0 < d → G.IsRegularOfDegree d → ∀ {ε : ℝ}, 0 < ε → lambdaG G d ≤ 3 / 5 - ε →
      ∀ (a : Bool) (x : V → Bool), (minority a x : ℝ) ≤ ε / 5 * Fintype.card V →
        1 - (1 / (Fintype.card V : ℝ)
              + (C * log (Fintype.card V) + 1) * exp (-(ε * Fintype.card V / C)))
          ≤ expList (GraphRound G) ⌈C * log (Fintype.card V)⌉₊
              (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  sorry

/-- The failure probability of `two_choices_expander` is `o(1)`: for fixed `C > 0` and `ε > 0`,
`1/n + (C log n + 1) e^{−ε n / C} → 0`. -/
theorem two_choices_failure_tendsto {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) + (C * log n + 1) * exp (-(ε * n / C))) atTop (𝓝 0) := by
  sorry

end Median
