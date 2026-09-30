import ThreeMajority.Model
import Dynamics.Rounds

/-!
# The 3-majority dynamics with `k` colors (Section 2)

`n` anonymous nodes each support one of `k` colors; a coloring is a map
`Config n k := Fin n → Fin k`. At every round each node picks three nodes
uniformly at random (including itself, with repetitions) and recolors itself
according to the majority of the three colors it sees; if it sees three
different colors it takes the first one.

The randomness of a round is exactly that of the binary development:
`ThreeMajority.Tgt3 n = Fin n → Fin n × Fin n × Fin n`, one ordered triple of
samples per node, drawn uniformly. Multi-round expectations are
`Dynamics.expList (Tgt3 n) T`, and `kernel f` is the same process as a
finite Markov kernel (`Dynamics.Kernel.ofStep`), which is how the phase
lemma `Dynamics.Kernel.nested_phases` (the paper's Lemma A.4) applies.

Section 4.2 of the paper compares 3-majority with an arbitrary deterministic
3-input rule `f : Fin k → Fin k → Fin k → Fin k`, so the round is defined for
any such rule (`stepWith f`) and 3-majority is the instance `f = maj3`.
-/

namespace Plurality

open Finset
open ThreeMajority (Tgt3 tgt3_nonempty)

/-- A coloring of `n` nodes with `k` colors. -/
abbrev Config (n k : ℕ) := Fin n → Fin k

variable {n k : ℕ}

/-- The **3-majority rule**: the majority color among `a, b, c`, and the
first one, `a`, if all three differ. -/
def maj3 (a b c : Fin k) : Fin k := if b = c then b else a

lemma maj3_of_eq_left {a b c : Fin k} (h : a = b) : maj3 a b c = a := by
  unfold maj3; split_ifs with h' <;> simp_all

lemma maj3_of_eq_right {a b c : Fin k} (h : b = c) : maj3 a b c = b := by
  simp [maj3, h]

lemma maj3_of_eq_outer {a b c : Fin k} (h : a = c) : maj3 a b c = a := by
  unfold maj3; split_ifs with h' <;> simp_all

lemma maj3_mem (a b c : Fin k) : maj3 a b c = a ∨ maj3 a b c = b ∨ maj3 a b c = c := by
  unfold maj3; split_ifs <;> simp

/-- One synchronous round of the 3-input dynamics with rule `f`: node `v`
sees the colors of its three samples `r v` and adopts `f` of them. -/
def stepWith (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k) (r : Tgt3 n) :
    Config n k :=
  fun v => f (x (r v).1) (x (r v).2.1) (x (r v).2.2)

/-- One round of the 3-majority dynamics. -/
def step (x : Config n k) (r : Tgt3 n) : Config n k := stepWith maj3 x r

/-- The coloring after consuming a list of rounds with rule `f`. -/
def runWith (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k) (l : List (Tgt3 n)) :
    Config n k :=
  l.foldl (stepWith f) x

/-- The coloring after consuming a list of rounds of 3-majority. -/
def run (x : Config n k) (l : List (Tgt3 n)) : Config n k := runWith maj3 x l

@[simp] lemma runWith_nil (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k) :
    runWith f x [] = x := rfl

@[simp] lemma runWith_cons (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k) (r : Tgt3 n)
    (l : List (Tgt3 n)) : runWith f x (r :: l) = runWith f (stepWith f x r) l := rfl

lemma runWith_append (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k)
    (l₁ l₂ : List (Tgt3 n)) : runWith f x (l₁ ++ l₂) = runWith f (runWith f x l₁) l₂ := by
  simp [runWith, List.foldl_append]

@[simp] lemma run_nil (x : Config n k) : run x [] = x := rfl

@[simp] lemma run_cons (x : Config n k) (r : Tgt3 n) (l : List (Tgt3 n)) :
    run x (r :: l) = run (step x r) l := rfl

lemma run_append (x : Config n k) (l₁ l₂ : List (Tgt3 n)) :
    run x (l₁ ++ l₂) = run (run x l₁) l₂ :=
  runWith_append maj3 x l₁ l₂

/-! ### Color counts -/

/-- The number `c_j` of nodes supporting color `j`. The map `count x` is the
paper's `k`-color distribution (`k`-cd) of `x`. -/
def count (x : Config n k) (j : Fin k) : ℕ := (univ.filter fun v => x v = j).card

lemma count_le (x : Config n k) (j : Fin k) : count x j ≤ n := by
  unfold count
  simpa using card_le_card (filter_subset (fun v => x v = j) univ)

/-- The color counts sum to `n`. -/
lemma sum_count (x : Config n k) : ∑ j, count x j = n := by
  unfold count
  rw [← card_eq_sum_card_fiberwise (f := x) (fun v _ => mem_univ (x v))]
  simp

lemma sum_count_real (x : Config n k) : ∑ j, (count x j : ℝ) = n := by
  exact_mod_cast sum_count x

/-- Summing a function of the colors over all nodes groups the nodes by color. -/
lemma sum_comp_eq_sum_count {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (x : Config n k) (F : Fin k → M) :
    ∑ v, F (x v) = ∑ j, (count x j : ℝ) • F j := by
  rw [← sum_fiberwise univ x (fun v => F (x v))]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_congr rfl (g := fun _ => F j) (by intro v hv; rw [(mem_filter.mp hv).2]), sum_const]
  simp [count, Nat.cast_smul_eq_nsmul]

/-- `x` is monochromatic of color `j`: every node supports `j`. -/
def Mono (x : Config n k) (j : Fin k) : Prop := ∀ v, x v = j

instance (x : Config n k) (j : Fin k) : Decidable (Mono x j) :=
  inferInstanceAs (Decidable (∀ v, x v = j))

/-- `x` is monochromatic (in some color). -/
def Monochromatic (x : Config n k) : Prop := ∃ j, Mono x j

instance (x : Config n k) : Decidable (Monochromatic x) :=
  inferInstanceAs (Decidable (∃ j, ∀ v, x v = j))

lemma mono_iff_count (x : Config n k) (j : Fin k) : Mono x j ↔ count x j = n := by
  unfold Mono count
  constructor
  · intro h
    simp [h]
  · intro h v
    have : univ.filter (fun v => x v = j) = univ := by
      apply eq_univ_of_card
      simpa using h
    have hv := mem_univ v
    rw [← this] at hv
    exact (mem_filter.mp hv).2

/-- A 3-input rule that always returns one of its inputs keeps a
monochromatic coloring monochromatic: consensus is absorbing. -/
lemma stepWith_mono {f : Fin k → Fin k → Fin k → Fin k}
    (hf : ∀ a b c, f a b c = a ∨ f a b c = b ∨ f a b c = c)
    {x : Config n k} {j : Fin k} (hx : Mono x j) (r : Tgt3 n) : Mono (stepWith f x r) j := by
  intro v
  simp only [stepWith, hx _]
  rcases hf j j j with h | h | h <;> exact h

lemma runWith_mono {f : Fin k → Fin k → Fin k → Fin k}
    (hf : ∀ a b c, f a b c = a ∨ f a b c = b ∨ f a b c = c)
    {x : Config n k} {j : Fin k} (hx : Mono x j) (l : List (Tgt3 n)) :
    Mono (runWith f x l) j := by
  induction l generalizing x with
  | nil => exact hx
  | cons r l ih => exact ih (stepWith_mono hf hx r)

lemma run_mono {x : Config n k} {j : Fin k} (hx : Mono x j) (l : List (Tgt3 n)) :
    Mono (run x l) j :=
  runWith_mono maj3_mem hx l

/-! ### The Markov kernel -/

instance [NeZero n] : Nonempty (Tgt3 n) := tgt3_nonempty (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

/-- The dynamics with rule `f` as a finite Markov kernel on colorings. -/
noncomputable def kernel [NeZero n] (f : Fin k → Fin k → Fin k → Fin k) :
    Dynamics.Kernel (Config n k) :=
  Dynamics.Kernel.ofStep (stepWith f)

/-- Probabilities at time `T` for the kernel are expectations over `T`
independent rounds. -/
lemma kernel_event [NeZero n] (f : Fin k → Fin k → Fin k → Fin k) (P : Config n k → Prop)
    [DecidablePred P] (T : ℕ) (x : Config n k) :
    (kernel f).event P T x
      = Dynamics.expList (Tgt3 n) T (fun l => if P (runWith f x l) then 1 else 0) := by
  rw [kernel, Dynamics.Kernel.event_ofStep]
  congr 1
  funext l
  by_cases h : P (runWith f x l)
  · have h' : P (List.foldl (stepWith f) x l) := h
    rw [if_pos h, if_pos h']
  · have h' : ¬ P (List.foldl (stepWith f) x l) := h
    rw [if_neg h, if_neg h']

end Plurality
