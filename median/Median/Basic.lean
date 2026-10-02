import Median.Defs

/-! # The median dynamics: structure

The median commutes with monotone maps, so thresholding the median process at any value `θ`
gives exactly the binary median process (2-Choices) driven by the same samples: the multi-valued
dynamics is a family of coupled binary ones. Values stay within the current range, and with two
values one round maps the fraction `p` of `true`s to `3p² − 2p³` in expectation. Every run reaches
consensus almost surely.
-/

namespace Median
open Finset Dynamics Filter Topology

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-! ### Auxiliary lemmas

Helpers for the proofs below: an indicator for Booleans, commutation of monotone maps with
`min`/`max`, membership of the median, the Boolean median as a majority polynomial, a sum
formula for `ones`, and averaging lemmas. -/

/-- Indicator of a `true` Boolean. -/
private def ind (b : Bool) : ℝ := if b = true then 1 else 0

/-- A monotone map between linear orders commutes with `min`. -/
private lemma monotone_min {β : Type*} [LinearOrder β] {f : α → β} (hf : Monotone f) (a b : α) :
    f (min a b) = min (f a) (f b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (hf h)]
  · have hb : b ≤ a := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right hb, min_eq_right (hf hb)]

/-- A monotone map between linear orders commutes with `max`. -/
private lemma monotone_max {β : Type*} [LinearOrder β] {f : α → β} (hf : Monotone f) (a b : α) :
    f (max a b) = max (f a) (f b) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (hf h)]
  · have hb : b ≤ a := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left hb, max_eq_left (hf hb)]

/-- The median of three elements is one of them. -/
private lemma med3_mem (a b c : α) : med3 a b c = a ∨ med3 a b c = b ∨ med3 a b c = c := by
  simp only [med3]
  rcases min_choice (max a b) c with h3 | h3
  · rw [h3]
    rcases min_choice a b with h2 | h2
    · rw [h2, max_eq_right (le_max_left a b)]
      rcases max_choice a b with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · rw [h2, max_eq_right (le_max_right a b)]
      rcases max_choice a b with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
  · rw [h3]
    rcases min_choice a b with h2 | h2
    · rw [h2]
      rcases max_choice a c with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)
    · rw [h2]
      rcases max_choice b c with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)

/-- If the last two of the three values coincide, the median is that value. -/
private lemma med3_right (a c : α) : med3 a c c = c := by
  simp only [med3, min_eq_right (le_max_right a c), max_eq_right (min_le_right a c)]

/-- The median of three Booleans is the majority, as an indicator polynomial. -/
private lemma med3_ind (a b c : Bool) :
    ind (med3 a b c) = ind a * ind b + ind a * ind c + ind b * ind c
      - 2 * (ind a * (ind b * ind c)) := by
  cases a <;> cases b <;> cases c <;> norm_num [ind, med3]

/-- `ones` as a real sum of indicators. -/
private lemma ones_eq_sum (y : Config n Bool) :
    (ones y : ℝ) = ∑ v : Fin n, ind (y v) := by
  have h : ∑ v : Fin n, ind (y v) = ((univ.filter fun v => y v = true).card : ℝ) := by
    simp only [ind]
    rw [Finset.sum_boole]
  rw [h]
  rfl

omit [LinearOrder α] in
/-- Consensus configurations are mapped to zero by `notConsensus`. -/
private lemma notConsensus_eq {y : Config n α} (h : Consensus y) : notConsensus y = 0 := by
  unfold notConsensus
  rw [if_pos h]

omit [LinearOrder α] in
/-- Non-consensus configurations are mapped to one by `notConsensus`. -/
private lemma notConsensus_eq' {y : Config n α} (h : ¬ Consensus y) : notConsensus y = 1 := by
  unfold notConsensus
  rw [if_neg h]

omit [LinearOrder α] in
private lemma notConsensus_cases (y : Config n α) : notConsensus y = 0 ∨ notConsensus y = 1 := by
  by_cases h : Consensus y
  · exact Or.inl (notConsensus_eq h)
  · exact Or.inr (notConsensus_eq' h)

/-- A `{0, 1}`-valued average that vanishes somewhere is below one. -/
private lemma avg_lt_one {γ : Type*} [Fintype γ] [Nonempty γ] (g : γ → ℝ)
    (hg : ∀ a, g a = 0 ∨ g a = 1) (a₀ : γ) (ha₀ : g a₀ = 0) : avg g < 1 := by
  classical
  have hpt : ∀ a : γ, g a ≤ (if a = a₀ then (0:ℝ) else 1) := by
    intro a
    by_cases h : a = a₀
    · rw [h, if_pos rfl, ha₀]
    · rw [if_neg h]
      rcases hg a with h' | h' <;> simp [h']
  have hind : avg (fun a : γ => (if a = a₀ then (1:ℝ) else 0)) = 1 / (Fintype.card γ : ℝ) := by
    unfold avg
    rw [Finset.sum_ite_eq' Finset.univ a₀ (fun _ => (1:ℝ))]
    simp
  have havg : avg (fun a : γ => (if a = a₀ then (0:ℝ) else 1))
      = 1 - 1 / (Fintype.card γ : ℝ) := by
    have hbody : (fun a : γ => (if a = a₀ then (0:ℝ) else 1))
        = fun a : γ => (1:ℝ) - (if a = a₀ then (1:ℝ) else 0) := by
      funext a
      by_cases h : a = a₀ <;> simp [h]
    rw [hbody, avg_sub, avg_const, hind]
  have hcard : (0:ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  calc avg g ≤ avg (fun a : γ => (if a = a₀ then (0:ℝ) else 1)) := avg_le_avg hpt
    _ = 1 - 1 / (Fintype.card γ : ℝ) := havg
    _ < 1 := by
        have hpos : (0:ℝ) < 1 / (Fintype.card γ : ℝ) := one_div_pos.mpr hcard
        linarith

/-- Averaging the majority polynomial of two independent uniform samples: with `P` the average
of `u` and `A` a constant, the average of `A u₁ + A u₂ + u₁u₂ − 2 A u₁u₂` over pairs is
`A (2P − 2P²) + P²`. -/
private lemma avg_prod_poly {m : ℕ} [NeZero m] (u : Fin m → ℝ) (P A : ℝ) (h : avg u = P) :
    avg (fun p : Fin m × Fin m =>
        A * u p.1 + A * u p.2 + u p.1 * u p.2 - 2 * (A * (u p.1 * u p.2)))
      = A * (2 * P - 2 * P * P) + P * P := by
  have e1 : avg (fun p : Fin m × Fin m => A * u p.1) = A * P := by
    rw [avg_const_mul, avg_fst_mul u, h]
  have e2 : avg (fun p : Fin m × Fin m => A * u p.2) = A * P := by
    rw [avg_const_mul, avg_snd_mul u, h]
  have e3 : avg (fun p : Fin m × Fin m => u p.1 * u p.2) = P * P := by
    rw [avg_mul_prod u u, h]
  have e4 : avg (fun p : Fin m × Fin m => 2 * (A * (u p.1 * u p.2))) = 2 * (A * (P * P)) := by
    rw [avg_const_mul, avg_const_mul, avg_mul_prod u u, h]
  have hsplit : avg (fun p : Fin m × Fin m =>
      A * u p.1 + A * u p.2 + u p.1 * u p.2 - 2 * (A * (u p.1 * u p.2)))
      = (avg (fun p : Fin m × Fin m => A * u p.1)
        + avg (fun p : Fin m × Fin m => A * u p.2)
        + avg (fun p : Fin m × Fin m => u p.1 * u p.2))
      - avg (fun p : Fin m × Fin m => 2 * (A * (u p.1 * u p.2))) := by
    rw [avg_sub, avg_add, avg_add]
  rw [hsplit, e1, e2, e3, e4]
  ring

/-- The median commutes with monotone maps. -/
theorem med3_monotone {β : Type*} [LinearOrder β] {f : α → β} (hf : Monotone f) (a b c : α) :
    f (med3 a b c) = med3 (f a) (f b) (f c) := by
  simp only [med3, monotone_min hf, monotone_max hf]

/-- Threshold reduction, one round: thresholding commutes with the median rule. -/
theorem threshold_step (θ : α) (x : Config n α) (r : Round n) :
    (fun v => decide (θ ≤ step x r v)) = step (fun v => decide (θ ≤ x v)) r := by
  have hmono : Monotone fun a : α => decide (θ ≤ a) := by
    intro a b hab
    by_cases h : θ ≤ a
    · have hb : θ ≤ b := h.trans hab
      simp [h, hb]
    · simp [h]
  funext v
  exact med3_monotone hmono (x v) (x (r v).1) (x (r v).2)

/-- Threshold reduction, any number of rounds (same samples). -/
theorem threshold_run (θ : α) (x : Config n α) (l : List (Round n)) :
    (fun v => decide (θ ≤ run x l v)) = run (fun v => decide (θ ≤ x v)) l := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih =>
    show (fun v => decide (θ ≤ run (step x r) l v))
      = run (step (fun v => decide (θ ≤ x v)) r) l
    rw [ih (step x r), threshold_step]

/-- Validity: every new value is a current value. -/
theorem step_mem (x : Config n α) (r : Round n) (v : Fin n) : ∃ u, step x r v = x u := by
  rcases med3_mem (x v) (x (r v).1) (x (r v).2) with h | h | h
  · exact ⟨v, h⟩
  · exact ⟨(r v).1, h⟩
  · exact ⟨(r v).2, h⟩

/-- The values stay within any interval containing all current values. -/
theorem step_mem_Icc {m M : α} (x : Config n α) (hx : ∀ v, x v ∈ Set.Icc m M) (r : Round n)
    (v : Fin n) : step x r v ∈ Set.Icc m M := by
  have hstep : step x r v = med3 (x v) (x (r v).1) (x (r v).2) := rfl
  rcases med3_mem (x v) (x (r v).1) (x (r v).2) with h | h | h
  · rw [hstep, h]; exact hx v
  · rw [hstep, h]; exact hx _
  · rw [hstep, h]; exact hx _

/-- Consensus configurations are fixed points. -/
theorem step_of_consensus (x : Config n α) (h : Consensus x) (r : Round n) : step x r = x := by
  obtain ⟨c, hc⟩ := h
  funext v
  show med3 (x v) (x (r v).1) (x (r v).2) = x v
  rw [hc v, hc (r v).1, hc (r v).2]
  simp [med3]

/-- Binary case: one round maps the fraction `p` of `true`s to `3p² − 2p³` in expectation. -/
theorem expected_ones [NeZero n] (x : Config n Bool) :
    avg (fun r : Round n => (ones (step x r) : ℝ)) =
      n * (3 * ((ones x : ℝ) / n) ^ 2 - 2 * ((ones x : ℝ) / n) ^ 3) := by
  have hn : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hS : (ones x : ℝ) = ∑ v : Fin n, ind (x v) := ones_eq_sum x
  have hP : avg (fun w : Fin n => ind (x w)) = (ones x : ℝ) / n := by
    rw [ones_eq_sum]
    unfold avg
    rw [Fintype.card_fin]
  have hD : ∀ v : Fin n,
      avg (fun r : Round n => ind (step x r v))
        = ind (x v) * (2 * ((ones x : ℝ) / n) - 2 * ((ones x : ℝ) / n) * ((ones x : ℝ) / n))
          + ((ones x : ℝ) / n) * ((ones x : ℝ) / n) := by
    intro v
    calc avg (fun r : Round n => ind (step x r v))
        = avg (fun p : Fin n × Fin n => ind (med3 (x v) (x p.1) (x p.2))) :=
          Dynamics.avg_eval n v (fun p : Fin n × Fin n => ind (med3 (x v) (x p.1) (x p.2)))
      _ = avg (fun p : Fin n × Fin n =>
          ind (x v) * ind (x p.1) + ind (x v) * ind (x p.2)
          + ind (x p.1) * ind (x p.2)
          - 2 * (ind (x v) * (ind (x p.1) * ind (x p.2)))) := by
          simp only [med3_ind]
      _ = ind (x v) * (2 * ((ones x : ℝ) / n) - 2 * ((ones x : ℝ) / n) * ((ones x : ℝ) / n))
          + ((ones x : ℝ) / n) * ((ones x : ℝ) / n) :=
          avg_prod_poly (fun w => ind (x w)) ((ones x : ℝ) / n) (ind (x v)) hP
  have hA : (fun r : Round n => (ones (step x r) : ℝ))
      = fun r : Round n => ∑ v : Fin n, ind (step x r v) :=
    funext fun r => ones_eq_sum (step x r)
  have havg : avg (fun r : Round n => ∑ v : Fin n, ind (step x r v))
      = ∑ v : Fin n, avg (fun r : Round n => ind (step x r v)) := by
    have h := Dynamics.avg_sum (α := Round n) (s := Finset.univ)
      (f := fun (v : Fin n) (r : Round n) => ind (step x r v))
    simpa only [] using h
  have hSum : ∑ v : Fin n, avg (fun r : Round n => ind (step x r v))
      = ∑ v : Fin n, (ind (x v) * (2 * ((ones x : ℝ) / n)
          - 2 * ((ones x : ℝ) / n) * ((ones x : ℝ) / n))
          + ((ones x : ℝ) / n) * ((ones x : ℝ) / n)) :=
    Finset.sum_congr rfl fun v _ => hD v
  have h2 : ∑ v : Fin n, (ind (x v) * (2 * ((ones x : ℝ) / n)
          - 2 * ((ones x : ℝ) / n) * ((ones x : ℝ) / n))
          + ((ones x : ℝ) / n) * ((ones x : ℝ) / n))
      = ((∑ v : Fin n, ind (x v)) * (2 * ((ones x : ℝ) / n)
          - 2 * ((ones x : ℝ) / n) * ((ones x : ℝ) / n))
          + ((n : ℕ) : ℝ) * (((ones x : ℝ) / n) * ((ones x : ℝ) / n))) := by
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkey : ∑ v : Fin n, ind (x v) = ((n : ℕ) : ℝ) * ((ones x : ℝ) / n) := by
    rw [← hS]
    field_simp
  rw [hA, havg, hSum, h2, hkey]
  ring

/-- Almost-sure consensus: the probability of not being in consensus after `t` rounds tends to
zero, from every configuration. -/
theorem absorbed [NeZero n] [Fintype α] [Nonempty α] (x : Config n α) :
    Tendsto (fun t => (kernel n α).iterate t notConsensus x) atTop (𝓝 0) := by
  have hstep : ∀ y : Config n α, (kernel n α).apply notConsensus y ≤ notConsensus y := by
    intro y
    unfold kernel
    rw [Dynamics.Kernel.apply_ofStep]
    by_cases h : Consensus y
    · have hfun : (fun r : Round n => notConsensus (step y r))
          = fun _ : Round n => notConsensus y := by
        funext r
        rw [step_of_consensus y h r]
      rw [hfun, avg_const]
    · rw [notConsensus_eq' h]
      have hle : avg (fun r : Round n => notConsensus (step y r))
          ≤ avg (fun _ : Round n => (1 : ℝ)) :=
        avg_le_avg fun r => by
          rcases notConsensus_cases (step y r) with h' | h' <;> simp [h']
      rw [avg_const] at hle
      exact hle
  have hacc : ∀ y : Config n α, ∃ t, (kernel n α).iterate t notConsensus y < 1 := by
    intro y
    refine ⟨1, ?_⟩
    show (kernel n α).apply notConsensus y < 1
    unfold kernel
    rw [Dynamics.Kernel.apply_ofStep]
    have hzero : notConsensus (step y (fun v : Fin n => ((0 : Fin n), (0 : Fin n)))) = 0 := by
      have hfix : step y (fun v : Fin n => ((0 : Fin n), (0 : Fin n))) = fun v => y 0 := by
        funext v
        show med3 (y v) (y 0) (y 0) = y 0
        exact med3_right _ _
      rw [hfix]
      exact notConsensus_eq ⟨y 0, fun v => rfl⟩
    exact avg_lt_one (fun r : Round n => notConsensus (step y r))
      (fun r => notConsensus_cases (step y r))
      (fun v : Fin n => ((0 : Fin n), (0 : Fin n))) hzero
  exact Dynamics.Kernel.finite_absorption (kernel n α) notConsensus
    (fun y => notConsensus_cases y) hstep hacc x

end Median
