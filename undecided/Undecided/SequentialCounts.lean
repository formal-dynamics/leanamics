import Undecided.Sequential

/-! # Counting for the sequential undecided-state dynamics

One interaction changes the counts `(x, y, b) = (count .a, count .b, count .u)` according to the
states of its initiator and responder only, so the expectation of any function of the next
configuration that only depends on those two states is an explicit average over the
`n (n - 1)` ordered pairs (`avg_transition`): pairs `(i, r)` of distinct states occur
`count i * count r` times. Specialized to weighted functions of the counts (`avg_step_counts`),
this is the one-step computation behind every potential of [AAE08, §4].

Also: consensus configurations are fixed by every interaction, the blank count moves by
`I_xy - I_vb` (`count_step_u`), and a non-blank configuration stays non-blank.
-/

namespace Undecided.Sequential
open Finset Dynamics

variable {n : ℕ}

/-! ### Sums over opinions and agents -/

lemma sum_op (f : Op → ℝ) : ∑ o, f o = f .a + f .b + f .u := by
  rw [show (univ : Finset Op) = {.a, .b, .u} by decide]
  simp [add_assoc]

lemma sum_comp_eq (s : Config n) (f : Op → ℝ) :
    ∑ j, f (s j) = ∑ o, (count s o : ℝ) * f o := by
  rw [← Finset.sum_fiberwise univ s (fun j => f (s j))]
  refine sum_congr rfl fun o _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f o) (fun j hj => by rw [(mem_filter.mp hj).2]),
    sum_const, nsmul_eq_mul]
  rfl

/-- The counts add up to the population size. -/
lemma count_add (s : Config n) :
    (count s .a : ℝ) + count s .b + count s .u = n := by
  have h := sum_comp_eq s (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [sum_op] at h
  linarith

lemma count_add_nat (s : Config n) : count s .a + count s .b + count s .u = n := by
  have h := count_add s
  exact_mod_cast h

lemma count_le (s : Config n) (o : Op) : count s o ≤ n := by
  have h := count_add_nat s
  cases o <;> omega

lemma one_le_count {s : Config n} {o : Op} {j : Fin n} (h : s j = o) : 1 ≤ count s o :=
  Finset.card_pos.mpr ⟨j, mem_filter.mpr ⟨mem_univ j, h⟩⟩

lemma count_eq_n {s : Config n} {o : Op} (h : count s o = n) (j : Fin n) : s j = o := by
  have hc : (univ.filter fun v => s v = o) = univ :=
    Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; exact h)
  have hj : j ∈ univ.filter fun v => s v = o := by rw [hc]; exact mem_univ j
  exact (mem_filter.mp hj).2

/-! ### Averages over interactions -/

lemma sum_offDiag (f : Fin n × Fin n → ℝ) :
    ∑ p : Interaction n, f p.1 = ∑ p, f p - ∑ j, f (j, j) := by
  rw [← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2) (by simp) f]
  rw [eq_sub_iff_add_eq,
    ← Finset.sum_filter_add_sum_filter_not univ (fun p : Fin n × Fin n => p.1 ≠ p.2) f]
  congr 1
  simp only [not_not, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp

/-- Number of interactions with initiator in state `i` and responder in state `r`. -/
noncomputable def pairCount (s : Config n) (i r : Op) : ℝ :=
  (count s i : ℝ) * count s r - if i = r then (count s i : ℝ) else 0

lemma sum_interaction (s : Config n) (G : Op → Op → ℝ) :
    ∑ p : Interaction n, G (s p.1.1) (s p.1.2) = ∑ i, ∑ r, pairCount s i r * G i r := by
  rw [sum_offDiag (fun q => G (s q.1) (s q.2)), Fintype.sum_prod_type]
  simp only
  have h1 : ∑ j, ∑ k, G (s j) (s k) = ∑ i, ∑ r, (count s i : ℝ) * count s r * G i r := by
    rw [sum_comp_eq s (fun i => ∑ k, G i (s k))]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comp_eq s (G i), mul_sum]
    exact sum_congr rfl fun r _ => by ring
  have h2 : ∑ j, G (s j) (s j) = ∑ i, (count s i : ℝ) * G i i := sum_comp_eq s (fun i => G i i)
  rw [h1, h2, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [pairCount, sub_mul, sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    mem_univ, if_true]

lemma card_interaction : (Fintype.card (Interaction n) : ℝ) = n * (n - 1) := by
  let s : Config n := fun _ => .u
  have hs := sum_interaction s (fun _ _ => (1 : ℝ))
  simp only [mul_one, sum_const, card_univ, nsmul_eq_mul] at hs
  rw [hs]
  simp only [pairCount, sum_op, if_true, reduceCtorEq, if_false]
  rw [← count_add s]
  ring

/-- An interaction is *idle* when its responder cannot change: equal states or a blank
initiator. -/
def Idle (i r : Op) : Prop := i = r ∨ i = .u

/-- **One-step transition formula.** For `G` constant (`G₀`) on idle pairs, the average over a
uniformly random interaction is `G₀` plus the four state-changing transitions `xb`, `yb`, `xy`,
`yx`, weighted by their numbers of pairs. -/
theorem avg_transition (hn : 2 ≤ n) (s : Config n) (G : Op → Op → ℝ) (G₀ : ℝ)
    (hidle : ∀ i r, Idle i r → G i r = G₀) :
    avg (fun p : Interaction n => G (s p.1.1) (s p.1.2)) =
      G₀ + ((count s .a : ℝ) * count s .u * (G .a .u - G₀) +
        (count s .b : ℝ) * count s .u * (G .b .u - G₀) +
        (count s .a : ℝ) * count s .b * (G .a .b - G₀) +
        (count s .a : ℝ) * count s .b * (G .b .a - G₀)) / (n * (n - 1)) := by
  have hn1 : (0 : ℝ) < n * (n - 1) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  unfold avg
  rw [sum_interaction, card_interaction]
  simp only [sum_op]
  rw [hidle .a .a (Or.inl rfl), hidle .b .b (Or.inl rfl), hidle .u .u (Or.inl rfl),
    hidle .u .a (Or.inr rfl), hidle .u .b (Or.inr rfl)]
  simp only [pairCount, if_true, reduceCtorEq, if_false, sub_zero]
  rw [← count_add s] at hn1 ⊢
  rw [div_eq_iff hn1.ne', add_mul, div_mul_cancel₀ _ hn1.ne']
  ring

/-! ### Counts after one interaction -/

/-- Change of the number of agents in state `o` when an initiator in state `i` meets a responder
in state `r`. -/
def delta (o i r : Op) : ℝ := (if update r i = o then 1 else 0) - (if r = o then 1 else 0)

lemma count_update (s : Config n) (j : Fin n) (o' o : Op) :
    (count (Function.update s j o') o : ℝ) =
      count s o - (if s j = o then 1 else 0) + (if o' = o then 1 else 0) := by
  rw [count_eq_sum, count_eq_sum]
  rw [← Finset.add_sum_erase _ _ (mem_univ j), ← Finset.add_sum_erase _ _ (mem_univ j)]
  have : ∑ x ∈ univ.erase j, (if Function.update s j o' x = o then (1 : ℝ) else 0) =
      ∑ x ∈ univ.erase j, (if s x = o then (1 : ℝ) else 0) := by
    refine sum_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [this, Function.update_self]
  ring

lemma count_step (s : Config n) (p : Interaction n) (o : Op) :
    (count (step s p) o : ℝ) = count s o + delta o (s p.1.1) (s p.1.2) := by
  rw [step, count_update, delta]
  ring

lemma delta_idle {i r : Op} (h : Idle i r) (o : Op) : delta o i r = 0 := by
  unfold Idle at h
  cases i <;> cases r <;> cases o <;> simp_all [delta, update]

/-- **One-step formula for weighted functions of the counts.** -/
theorem avg_step_counts (hn : 2 ≤ n) (s : Config n) (Ψ : Op → Op → ℝ) (ψ₀ : ℝ)
    (hΨ : ∀ i r, Idle i r → Ψ i r = ψ₀) (Φ : ℝ → ℝ → ℝ → ℝ) :
    avg (fun p : Interaction n => Real.exp (Ψ (s p.1.1) (s p.1.2)) *
        Φ (count (step s p) .a) (count (step s p) .b) (count (step s p) .u)) =
      Real.exp ψ₀ * Φ (count s .a) (count s .b) (count s .u) +
      ((count s .a : ℝ) * count s .u * (Real.exp (Ψ .a .u) *
          Φ (count s .a + 1) (count s .b) (count s .u - 1) -
          Real.exp ψ₀ * Φ (count s .a) (count s .b) (count s .u)) +
        (count s .b : ℝ) * count s .u * (Real.exp (Ψ .b .u) *
          Φ (count s .a) (count s .b + 1) (count s .u - 1) -
          Real.exp ψ₀ * Φ (count s .a) (count s .b) (count s .u)) +
        (count s .a : ℝ) * count s .b * (Real.exp (Ψ .a .b) *
          Φ (count s .a) (count s .b - 1) (count s .u + 1) -
          Real.exp ψ₀ * Φ (count s .a) (count s .b) (count s .u)) +
        (count s .a : ℝ) * count s .b * (Real.exp (Ψ .b .a) *
          Φ (count s .a - 1) (count s .b) (count s .u + 1) -
          Real.exp ψ₀ * Φ (count s .a) (count s .b) (count s .u))) / (n * (n - 1)) := by
  simp_rw [count_step]
  rw [avg_transition hn s (fun i r => Real.exp (Ψ i r) * Φ (count s .a + delta .a i r)
      (count s .b + delta .b i r) (count s .u + delta .u i r))
      (Real.exp ψ₀ * Φ (count s .a) (count s .b) (count s .u))]
  · simp [delta, update, sub_eq_add_neg]
  · intro i r h
    simp only [delta_idle h, add_zero, hΨ i r h]

/-! ### Interaction types -/

/-- Indicator of an `xb` or `yb` interaction: a decided initiator meets a blank responder. -/
def vbI (i r : Op) : ℝ := if r = .u ∧ i ≠ .u then 1 else 0

/-- Indicator of an `xy` or `yx` interaction: decided initiator and responder that disagree. -/
def xyI (i r : Op) : ℝ := if i ≠ .u ∧ r ≠ .u ∧ i ≠ r then 1 else 0

lemma vbI_idle {i r : Op} (h : Idle i r) : vbI i r = 0 := by
  unfold Idle at h
  cases i <;> cases r <;> simp_all [vbI]

lemma xyI_idle {i r : Op} (h : Idle i r) : xyI i r = 0 := by
  unfold Idle at h
  cases i <;> cases r <;> simp_all [xyI]

lemma vbI_nonneg (i r : Op) : 0 ≤ vbI i r := by unfold vbI; split <;> norm_num
lemma xyI_nonneg (i r : Op) : 0 ≤ xyI i r := by unfold xyI; split <;> norm_num
lemma vbI_le_one (i r : Op) : vbI i r ≤ 1 := by unfold vbI; split <;> norm_num
lemma xyI_le_one (i r : Op) : xyI i r ≤ 1 := by unfold xyI; split <;> norm_num

/-- The blank count moves by `I_xy - I_vb`. -/
lemma count_step_u (s : Config n) (p : Interaction n) :
    (count (step s p) .u : ℝ) =
      count s .u + xyI (s p.1.1) (s p.1.2) - vbI (s p.1.1) (s p.1.2) := by
  rw [count_step]
  cases s p.1.1 <;> cases s p.1.2 <;> simp [delta, update, xyI, vbI, sub_eq_add_neg]

/-! ### Consensus and non-blank configurations -/

lemma step_of_count_eq {s : Config n} {o : Op} (ho : o = .a ∨ o = .b) (h : count s o = n)
    (p : Interaction n) : step s p = s := by
  unfold step
  rw [count_eq_n h p.1.1, count_eq_n h p.1.2, update_id_decided ho, ← count_eq_n h p.1.2,
    Function.update_eq_self]

lemma run_of_count_eq {s : Config n} {o : Op} (ho : o = .a ∨ o = .b) (h : count s o = n)
    (l : List (Interaction n)) : run s l = s := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change List.foldl step (step s p) l = s
    rw [step_of_count_eq ho h p]
    exact ih

/-- Consensus in the sense of [AAE08, §4.1]: `x = n` or `y = n`. -/
def Cons (s : Config n) : Prop := count s .a = n ∨ count s .b = n

instance (s : Config n) : Decidable (Cons s) := by unfold Cons; infer_instance

lemma step_of_cons {s : Config n} (h : Cons s) (p : Interaction n) : step s p = s := by
  rcases h with h | h
  · exact step_of_count_eq (Or.inl rfl) h p
  · exact step_of_count_eq (Or.inr rfl) h p

lemma cons_of_step_cons {s : Config n} {p : Interaction n} (h : Cons s) : Cons (step s p) := by
  rw [step_of_cons h p]; exact h

lemma run_cons (s : Config n) (p : Interaction n) (l : List (Interaction n)) :
    run s (p :: l) = run (step s p) l := rfl

lemma cons_run {s : Config n} (h : Cons s) (l : List (Interaction n)) : Cons (run s l) := by
  induction l generalizing s with
  | nil => exact h
  | cons p l ih => rw [run_cons]; exact ih (cons_of_step_cons h)

/-- A step that creates a blank (`I_xy = 1`) needs an `x`-agent and a `y`-agent. -/
lemma counts_of_xyI {s : Config n} {p : Interaction n} (h : xyI (s p.1.1) (s p.1.2) ≠ 0) :
    1 ≤ count s .a ∧ 1 ≤ count s .b := by
  have hi := one_le_count (s := s) (j := p.1.1) rfl
  have hr := one_le_count (s := s) (j := p.1.2) rfl
  revert hi hr h
  cases s p.1.1 <;> cases s p.1.2 <;> simp [xyI] <;> omega

/-- Non-blank configurations stay non-blank. -/
lemma nonblank_step {s : Config n} (h : 1 ≤ count s .a + count s .b) (p : Interaction n) :
    1 ≤ count (step s p) .a + count (step s p) .b := by
  have hu := count_step_u s p
  have hs := count_add s
  have hs' := count_add (step s p)
  have h' : (1 : ℝ) ≤ count s .a + count s .b := by exact_mod_cast h
  have hv : (1 : ℝ) ≤ count (step s p) .a + count (step s p) .b := by
    by_cases hx : xyI (s p.1.1) (s p.1.2) = 0
    · have := vbI_nonneg (s p.1.1) (s p.1.2)
      linarith
    · obtain ⟨ha, hb⟩ := counts_of_xyI hx
      have ha' : (1 : ℝ) ≤ count s .a := by exact_mod_cast ha
      have hb' : (1 : ℝ) ≤ count s .b := by exact_mod_cast hb
      have := xyI_le_one (s p.1.1) (s p.1.2)
      have := vbI_nonneg (s p.1.1) (s p.1.2)
      linarith
  exact_mod_cast hv

lemma nonblank_run {s : Config n} (h : 1 ≤ count s .a + count s .b) (l : List (Interaction n)) :
    1 ≤ count (run s l) .a + count (run s l) .b := by
  induction l generalizing s with
  | nil => exact h
  | cons p l ih => rw [run_cons]; exact ih (nonblank_step h p)

end Undecided.Sequential
