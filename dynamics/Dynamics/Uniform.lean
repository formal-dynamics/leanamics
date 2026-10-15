import Mathlib

/-!
# Finite uniform expectations

Shared finite averages, trajectory expectations, independence (over any finite dependent
product, `avg_pi_prod`, `avg_pi_eval`, and of disjoint blocks of coordinates, `avg_pi_split`),
and reindexing.
The average on an empty type is zero.
-/

namespace Dynamics

open Finset

variable {α : Type*} [Fintype α]

/-- Expectation under the uniform distribution on a fintype. -/
noncomputable def avg (f : α → ℝ) : ℝ := (∑ a, f a) / (Fintype.card α : ℝ)

lemma avg_nonneg {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ avg f :=
  div_nonneg (sum_nonneg fun a _ => hf a) (by positivity)

lemma avg_le_avg {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (by positivity)

lemma avg_add (f g : α → ℝ) : avg (fun a => f a + g a) = avg f + avg g := by
  unfold avg
  rw [sum_add_distrib, add_div]

lemma avg_sub (f g : α → ℝ) : avg (fun a => f a - g a) = avg f - avg g := by
  unfold avg
  rw [sum_sub_distrib, sub_div]

lemma avg_const_mul (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  unfold avg
  rw [← mul_sum, mul_div_assoc]

lemma avg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) := by
  unfold avg
  rw [sum_comm, sum_div]

/-- The expectation of an indicator is a counting ratio. -/
lemma avg_indicator (P : α → Prop) [DecidablePred P] :
    avg (fun a => if P a then (1 : ℝ) else 0)
      = ((univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := by
  unfold avg
  congr 1
  rw [sum_boole]

lemma card_cast_pos [Nonempty α] : (0 : ℝ) < (Fintype.card α : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma avg_const [Nonempty α] (c : ℝ) : avg (fun _ : α => c) = c := by
  unfold avg
  rw [sum_const, card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc,
    div_self (ne_of_gt (card_cast_pos (α := α))), mul_one]

/-- A uniform average of values at most one is at most one (also on an empty type). -/
lemma avg_le_one {f : α → ℝ} (h : ∀ a, f a ≤ 1) : avg f ≤ 1 := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [avg]
  · simpa [avg_const] using avg_le_avg h

/-- Expectation of a functional of `T` i.i.d. uniform draws from `α`,
in transition-operator form: the head draw is averaged out first. -/
noncomputable def expList (α : Type*) [Fintype α] : ℕ → (List α → ℝ) → ℝ
  | 0, F => F []
  | T + 1, F => avg fun a : α => expList α T fun l => F (a :: l)

@[simp] lemma expList_zero (F : List α → ℝ) : expList α 0 F = F [] := rfl

lemma expList_succ (T : ℕ) (F : List α → ℝ) :
    expList α (T + 1) F = avg fun a : α => expList α T fun l => F (a :: l) :=
  rfl

lemma expList_nonneg {T : ℕ} {F : List α → ℝ} (h : ∀ l, 0 ≤ F l) :
    0 ≤ expList α T F := by
  induction T generalizing F with
  | zero => exact h []
  | succ T ih => exact avg_nonneg fun a => ih fun l => h (a :: l)

/-- `expList α T` only evaluates its argument on lists of length `T`, so a comparison on those
lists is enough. -/
lemma expList_le_of_length {T : ℕ} {F G : List α → ℝ}
    (h : ∀ l : List α, l.length = T → F l ≤ G l) : expList α T F ≤ expList α T G := by
  induction T generalizing F G with
  | zero => exact h [] rfl
  | succ T ih => exact avg_le_avg fun a => ih fun l hl => h (a :: l) (by simp [hl])

lemma expList_le_expList {T : ℕ} {F G : List α → ℝ} (h : ∀ l, F l ≤ G l) :
    expList α T F ≤ expList α T G :=
  expList_le_of_length fun l _ => h l

/-- An `expList` average of values at most one is at most one (also on an empty type). -/
lemma expList_le_one {T : ℕ} {F : List α → ℝ} (h : ∀ l, F l ≤ 1) : expList α T F ≤ 1 := by
  induction T generalizing F with
  | zero => exact h []
  | succ T ih => exact avg_le_one fun a => ih fun l => h (a :: l)

lemma expList_add (T : ℕ) (F G : List α → ℝ) :
    expList α T (fun l => F l + G l) = expList α T F + expList α T G := by
  induction T generalizing F G with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ, expList_succ (F := F), expList_succ (F := G), ← avg_add]
    exact congrArg avg (funext fun a => ih _ _)

lemma expList_const_mul (T : ℕ) (c : ℝ) (F : List α → ℝ) :
    expList α T (fun l => c * F l) = c * expList α T F := by
  induction T generalizing F with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ, expList_succ (F := F), ← avg_const_mul]
    exact congrArg avg (funext fun a => ih _)

lemma expList_const [Nonempty α] (T : ℕ) (c : ℝ) :
    expList α T (fun _ => c) = c := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ]
    simpa [ih] using avg_const (α := α) c

/-- Expectation of a complement: `𝔼[1 - F] = 1 - 𝔼[F]` (the `expList` form of
`Kernel.iterateSeq_one_sub`). -/
lemma expList_one_sub [Nonempty α] (T : ℕ) (F : List α → ℝ) :
    expList α T (fun l => 1 - F l) = 1 - expList α T F := by
  have h := expList_add T (fun l => 1 - F l) F
  simp only [sub_add_cancel, expList_const] at h
  linarith

lemma expList_sum {ι : Type*} (s : Finset ι) (T : ℕ) (F : ι → List α → ℝ) :
    expList α T (fun l => ∑ i ∈ s, F i l) = ∑ i ∈ s, expList α T (F i) := by
  induction T generalizing F with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ]
    simp_rw [ih, expList_succ]
    exact avg_sum s _

lemma expList_append (T₁ T₂ : ℕ) (F : List α → ℝ) :
    expList α (T₁ + T₂) F
      = expList α T₁ fun l₁ => expList α T₂ fun l₂ => F (l₁ ++ l₂) := by
  induction T₁ generalizing F with
  | zero => simp
  | succ T₁ ih =>
    rw [Nat.succ_add, expList_succ, expList_succ
      (F := fun l₁ => expList α T₂ fun l₂ => F (l₁ ++ l₂))]
    exact congrArg avg (funext fun a => by rw [ih]; simp)

/-! ### Lengths and prefixes: `expList α T` only evaluates lists of length `T`

The comparison form `expList_le_of_length` is stated above, with the monotonicity lemmas. -/

/-- `expList α T` only evaluates its argument on lists of length `T`. -/
lemma expList_congr_length {T : ℕ} {F G : List α → ℝ}
    (h : ∀ l : List α, l.length = T → F l = G l) : expList α T F = expList α T G :=
  le_antisymm (expList_le_of_length fun l hl => (h l hl).le)
    (expList_le_of_length fun l hl => (h l hl).ge)

/-- **Two phases.** If, after any first phase `l₁` of `T₁` rounds, the expectation of `Φ` over
the second phase is at most `a + Ψ l₁`, then over both phases it is at most `a + 𝔼 Ψ`. -/
lemma expList_le_of_split [Nonempty α] {T₁ T₂ : ℕ} {Φ Ψ : List α → ℝ} {a : ℝ}
    (h : ∀ l₁ : List α, l₁.length = T₁ → expList α T₂ (fun l₂ => Φ (l₁ ++ l₂)) ≤ a + Ψ l₁) :
    expList α (T₁ + T₂) Φ ≤ a + expList α T₁ Ψ := by
  rw [expList_append]
  calc expList α T₁ (fun l₁ => expList α T₂ fun l₂ => Φ (l₁ ++ l₂))
      ≤ expList α T₁ (fun l₁ => a + Ψ l₁) := expList_le_of_length h
    _ = a + expList α T₁ Ψ := by rw [expList_add, expList_const]

/-- A function of the first `k` of `T ≥ k` draws only sees `k` draws. -/
lemma expList_take [Nonempty α] {k T : ℕ} (hk : k ≤ T) (F : List α → ℝ) :
    expList α T (fun l => F (l.take k)) = expList α k F := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [expList_append]
  refine expList_congr_length fun l hl => ?_
  simp_rw [List.take_left' hl]
  exact expList_const (α := α) m _

/-- A function of the first `k` of `T > k` draws and of the next one: the next draw is a fresh
uniform sample. -/
lemma expList_take_getElem? [Nonempty α] {k T : ℕ} (hk : k < T) (F : List α → Option α → ℝ) :
    expList α T (fun l => F (l.take k) l[k]?) = expList α k fun p => avg fun a => F p (some a) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show k + m + 1 = k + (m + 1) by ring, expList_append]
  refine expList_congr_length fun p hp => ?_
  have h1 : ∀ l : List α, (p ++ l).take k = p := fun l => List.take_left' hp
  have h2 : ∀ l : List α, (p ++ l)[k]? = l.head? := fun l => by
    rw [List.getElem?_append_right (by omega), hp, Nat.sub_self, List.head?_eq_getElem?]
  simp_rw [h1, h2, expList_succ, List.head?_cons]
  congr 1
  funext a
  exact expList_const (α := α) m _

/-! ### Independence: average of a product over a product space -/

/-- **Independence for a pair of coordinates**: the average of a product
`g p.1 * h p.2` over a product Fintype `β × δ` (uniform measure) equals the
product of the individual averages. No `Nonempty` hypothesis is needed:
if either factor is empty, both sides are `0` by the `0/0 = 0` convention. -/
lemma avg_mul_prod {β δ : Type*} [Fintype β] [Fintype δ] (g : β → ℝ) (h : δ → ℝ) :
    avg (fun p : β × δ => g p.1 * h p.2) = avg g * avg h := by
  unfold avg
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  rw [show (∑ i : β, ∑ j : δ, g i * h j) = (∑ b, g b) * ∑ d, h d from by
    rw [Finset.sum_mul_sum univ univ g h]]
  push_cast
  ring

/-- **Marginal**: the average of a function of the first coordinate only,
over a product space, equals its average over the first factor alone. -/
lemma avg_fst_mul {β δ : Type*} [Fintype β] [Fintype δ] [Nonempty δ] (g : β → ℝ) :
    avg (fun p : β × δ => g p.1) = avg g := by
  rw [show (fun p : β × δ => g p.1) = fun p : β × δ => g p.1 * (fun _ : δ => (1 : ℝ)) p.2
      from funext fun p => (mul_one _).symm,
    avg_mul_prod g (fun _ : δ => (1 : ℝ)), avg_const, mul_one]

/-- **Marginal**: the average of a function of the second coordinate only,
over a product space, equals its average over the second factor alone. -/
lemma avg_snd_mul {β δ : Type*} [Fintype β] [Nonempty β] [Fintype δ] (h : δ → ℝ) :
    avg (fun p : β × δ => h p.2) = avg h := by
  rw [show (fun p : β × δ => h p.2) = fun p : β × δ => (fun _ : β => (1 : ℝ)) p.1 * h p.2
      from funext fun p => (one_mul _).symm,
    avg_mul_prod (fun _ : β => (1 : ℝ)) h, avg_const, one_mul]

/-- Reindexing `avg` along an `Equiv` between the underlying Fintypes. -/
lemma avg_equiv {β : Type*} [Fintype β] (e : α ≃ β) (F : β → ℝ) :
    avg (fun a => F (e a)) = avg F := by
  unfold avg
  rw [Equiv.sum_comp e F, Fintype.card_congr e]

/-- **Independence over a dependent product**: under the uniform distribution on a finite
product `∀ i, β i`, the coordinates are independent, so the average of a product
`∏ i, g i (x i)` is the product of the averages `avg (g i)`. -/
lemma avg_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (g : ∀ i, β i → ℝ) :
    avg (fun x : (∀ i, β i) => ∏ i, g i (x i)) = ∏ i, avg (g i) := by
  unfold avg
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, ← prod_div_distrib]

/-- **Marginal over a dependent product**: the average of a function of one coordinate, over
the whole product space, is its average over that coordinate alone. -/
lemma avg_pi_eval {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] (i : ι) (g : β i → ℝ) :
    avg (fun x : (∀ j, β j) => g (x i)) = avg g := by
  rw [← avg_fst_mul (δ := (j : {j // j ≠ i}) → β j) g]
  exact avg_equiv (Equiv.piSplitAt i β) (fun p => g p.1)

/-- **Independence over a `Fin n`-indexed product**: the average of a product
`∏ i, f i (x i)` over the product Fintype `Fin n → γ` (uniform measure)
equals the product of the individual averages `avg (f i)`. This is the
discrete, measure-theory-free form of "coordinate projections on a product
space are independent", the non-dependent case of `avg_pi_prod`. -/
lemma avg_prod_pi {γ : Type*} [Fintype γ] :
    ∀ (n : ℕ) (f : Fin n → γ → ℝ),
      avg (fun x : Fin n → γ => ∏ i, f i (x i)) = ∏ i, avg (f i) :=
  fun _ f => avg_pi_prod f

/-- **Marginal for `Fin n`-indexed Pi types**: the average of a function of
a single fixed coordinate, over the whole product space, equals its average
over that one factor alone (the non-dependent case of `avg_pi_eval`). -/
lemma avg_eval {γ : Type*} [Fintype γ] [Nonempty γ] (n : ℕ) (v : Fin n) (G : γ → ℝ) :
    avg (fun x : Fin n → γ => G (x v)) = avg G :=
  avg_pi_eval (β := fun _ : Fin n => γ) v G

/-- Finite uniform averages over a product of index sets commute. -/
lemma avg_avg_swap {β : Type*} [Fintype β] (F : α → β → ℝ) :
    avg (fun a => avg (fun b => F a b)) = avg (fun b => avg (fun a => F a b)) := by
  unfold avg
  dsimp only
  rw [← Finset.sum_div, div_div, sum_comm, mul_comm, ← div_div, Finset.sum_div]

/-- The average over a product type is the iterated average. -/
lemma avg_prod_eq_avg_avg {β δ : Type*} [Fintype β] [Fintype δ] (G : β × δ → ℝ) :
    avg G = avg (fun b => avg (fun d => G (b, d))) := by
  unfold avg
  dsimp only
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, sum_div, sum_div]
  exact sum_congr rfl fun b _ => by rw [div_div, mul_comm]

/-- **Independence of disjoint blocks of coordinates**: under the uniform distribution on
`I → γ`, the coordinates in `{i // p i}` and those in its complement are independent, so the
average of a function of the two restrictions is the iterated average. -/
lemma avg_pi_split {I γ : Type*} [Fintype I] [DecidableEq I] [Fintype γ] (p : I → Prop)
    [DecidablePred p] (F : ({i // p i} → γ) → ({i // ¬ p i} → γ) → ℝ) :
    avg (fun τ : I → γ => F (fun i => τ i) (fun i => τ i)) =
      avg (fun τ₁ : {i // p i} → γ => avg (fun τ₂ : {i // ¬ p i} → γ => F τ₁ τ₂)) := by
  rw [← avg_prod_eq_avg_avg fun q => F q.1 q.2]
  exact avg_equiv (Equiv.piEquivPiSubtypeProd p fun _ : I => γ) fun q => F q.1 q.2

/-- `expList` is an iterated average, so it commutes with an outer uniform average. -/
lemma expList_avg_comm {β : Type*} [Fintype β] (T : ℕ) (G : α → List β → ℝ) :
    avg (fun a => expList β T (G a)) = expList β T (fun l => avg (fun a => G a l)) := by
  induction T generalizing G with
  | zero => simp [expList_zero]
  | succ T ih =>
    simp_rw [expList_succ]
    rw [avg_avg_swap]
    refine congrArg avg (funext fun b => ?_)
    exact ih (fun a l => G a (b :: l))

/-- The expectation of the zero functional vanishes (no nonemptiness needed). -/
lemma expList_zero_fun (T : ℕ) : expList α T (fun _ => (0 : ℝ)) = 0 := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ, ih]
    simp [avg]

/-- `expList` commutes with finite sums. -/
lemma expList_finset_sum {ι : Type*} (T : ℕ) (s : Finset ι) (F : ι → List α → ℝ) :
    expList α T (fun l => ∑ i ∈ s, F i l) = ∑ i ∈ s, expList α T (F i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact expList_zero_fun T
  | @insert i s hi ih =>
    have hfun :
        (fun l => ∑ j ∈ insert i s, F j l) = fun l => F i l + ∑ j ∈ s, F j l := by
      funext l
      rw [Finset.sum_insert hi]
    rw [hfun, expList_add, ih, Finset.sum_insert hi]

end Dynamics
