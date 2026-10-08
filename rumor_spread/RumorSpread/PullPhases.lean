import RumorSpread.Main
import RumorSpread.PullFoldl

/-!
# The two-phase argument for an arbitrary inflationary spreading step

The PUSH proof (`Growth.lean`, `Saturation.lean`, `Main.lean`) only uses two one-round facts about
`step`: a round is *good* (grows the informed set by `9/8`, or starts above `n/2`) with
probability `≥ 1/8`, and above `n/2` the expected number of uninformed nodes contracts by `2/3`.
This file runs the same argument for any step `f : Finset (Fin n) → α → Finset (Fin n)` that is
inflationary (`I ⊆ f I a`), driven by i.i.d. uniform rounds `a : α`, with trajectories
`l.foldl f I`:

* `pow_goodCountOf_mul_card_le` — deterministic growth along good rounds;
* `expList_half_pow_goodCountOf` — `𝔼[(1/2)^(good rounds)] ≤ (15/16)^T`;
* `phase1Of`, `saturationOf` — the two phases;
* `notAllOf_le` — gluing, as `prNotAllInformed_le`;
* `notAllOf_antitone` — more rounds never hurt;
* `notAllOf_le_two_div` — with the constants of `Main.lean`, all nodes are informed after
  `⌈160 log n⌉` rounds with probability `≥ 1 - 2/n`.

It is instantiated for PULL in `PullMain.lean`.
-/

namespace RumorPush

open Finset Dynamics

variable {n : ℕ} {α : Type*}

/-- A round `a` is good for the step `f` if it multiplies the informed set by at least `9/8`,
or if more than half of the nodes are already informed (`goodRound` for a general step). -/
def goodRoundOf (f : Finset (Fin n) → α → Finset (Fin n)) (I : Finset (Fin n)) (a : α) :
    Prop :=
  9 * I.card ≤ 8 * (f I a).card ∨ n < 2 * I.card

instance (f : Finset (Fin n) → α → Finset (Fin n)) (I : Finset (Fin n)) (a : α) :
    Decidable (goodRoundOf f I a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The number of good rounds along a trajectory of the step `f`. -/
def goodCountOf (f : Finset (Fin n) → α → Finset (Fin n)) (I : Finset (Fin n)) : List α → ℕ
  | [] => 0
  | a :: l => (if goodRoundOf f I a then 1 else 0) + goodCountOf f (f I a) l

@[simp] lemma goodCountOf_nil (f : Finset (Fin n) → α → Finset (Fin n)) (I : Finset (Fin n)) :
    goodCountOf f I [] = 0 := rfl

lemma goodCountOf_cons (f : Finset (Fin n) → α → Finset (Fin n)) (I : Finset (Fin n)) (a : α)
    (l : List α) :
    goodCountOf f I (a :: l) = (if goodRoundOf f I a then 1 else 0) + goodCountOf f (f I a) l :=
  rfl

variable {f : Finset (Fin n) → α → Finset (Fin n)}

/-- Deterministic growth: if the final informed set is at most `n/2`, each good round
multiplied the informed set by `9/8` (as `pow_goodCount_mul_card_le_card_run`). -/
lemma pow_goodCountOf_mul_card_le (hf : ∀ I a, I ⊆ f I a) (I : Finset (Fin n)) (l : List α)
    (h : 2 * (l.foldl f I).card ≤ n) :
    ((9 : ℝ) / 8) ^ goodCountOf f I l * I.card ≤ ((l.foldl f I).card : ℝ) := by
  induction l generalizing I with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons] at h ⊢
    have hrun : (f I a).card ≤ (l.foldl f (f I a)).card := card_le_card (subset_foldl hf _ l)
    have hstep : I.card ≤ (f I a).card := card_le_card (hf I a)
    have hnotbig : ¬ n < 2 * I.card := by omega
    have IH := ih (f I a) h
    have hpow : (0 : ℝ) ≤ ((9 : ℝ) / 8) ^ goodCountOf f (f I a) l := by positivity
    rw [goodCountOf_cons]
    by_cases hg : goodRoundOf f I a
    · have h98 : 9 * I.card ≤ 8 * (f I a).card := hg.resolve_right hnotbig
      have hcast : (9 : ℝ) / 8 * I.card ≤ ((f I a).card : ℝ) := by
        have : (9 : ℝ) * I.card ≤ 8 * (f I a).card := by exact_mod_cast h98
        linarith
      rw [if_pos hg]
      calc ((9 : ℝ) / 8) ^ (1 + goodCountOf f (f I a) l) * I.card
          = ((9 : ℝ) / 8) ^ goodCountOf f (f I a) l * ((9 / 8) * I.card) := by
            rw [pow_add, pow_one]; ring
        _ ≤ ((9 : ℝ) / 8) ^ goodCountOf f (f I a) l * (f I a).card :=
            mul_le_mul_of_nonneg_left hcast hpow
        _ ≤ _ := IH
    · have hcast : (I.card : ℝ) ≤ ((f I a).card : ℝ) := by exact_mod_cast hstep
      rw [if_neg hg, zero_add]
      calc ((9 : ℝ) / 8) ^ goodCountOf f (f I a) l * I.card
          ≤ ((9 : ℝ) / 8) ^ goodCountOf f (f I a) l * (f I a).card :=
            mul_le_mul_of_nonneg_left hcast hpow
        _ ≤ _ := IH

variable [Fintype α] [Nonempty α]

/-- Per-round exponential moment of the good-round indicator. -/
lemma avg_half_pow_goodOf {I : Finset (Fin n)}
    (hgood : (1 : ℝ) / 8 ≤ avg (fun a : α => if goodRoundOf f I a then (1 : ℝ) else 0)) :
    avg (fun a : α => ((1 : ℝ) / 2) ^ (if goodRoundOf f I a then 1 else 0)) ≤ 15 / 16 := by
  have hpt : (fun a : α => ((1 : ℝ) / 2) ^ (if goodRoundOf f I a then 1 else 0))
      = fun a : α => (fun _ : α => (1 : ℝ)) a
          - (fun a : α => (1 : ℝ) / 2 * (if goodRoundOf f I a then (1 : ℝ) else 0)) a := by
    funext a
    by_cases hg : goodRoundOf f I a
    · simp only [hg, if_true, pow_one, mul_one]
      norm_num
    · simp [hg]
  rw [hpt, avg_sub, avg_const, avg_const_mul]
  linarith

/-- **Exponential-moment bound for adaptive trials** (as `expList_half_pow_goodCount`):
`𝔼[(1/2) ^ (number of good rounds in T rounds)] ≤ (15/16) ^ T`. -/
lemma expList_half_pow_goodCountOf (hf : ∀ I a, I ⊆ f I a)
    (hgood : ∀ I : Finset (Fin n), I.Nonempty →
      (1 : ℝ) / 8 ≤ avg (fun a : α => if goodRoundOf f I a then (1 : ℝ) else 0))
    (T : ℕ) : ∀ I : Finset (Fin n), I.Nonempty →
      expList α T (fun l => ((1 : ℝ) / 2) ^ goodCountOf f I l) ≤ ((15 : ℝ) / 16) ^ T := by
  induction T with
  | zero =>
    intro I _
    simp
  | succ T ih =>
    intro I hI
    rw [expList_succ]
    have key : ∀ a : α,
        (expList α T fun l => ((1 : ℝ) / 2) ^ goodCountOf f I (a :: l))
          = ((1 : ℝ) / 2) ^ (if goodRoundOf f I a then 1 else 0)
              * expList α T fun l => ((1 : ℝ) / 2) ^ goodCountOf f (f I a) l := by
      intro a
      rw [← expList_const_mul]
      congr 1
      funext l
      rw [goodCountOf_cons, pow_add]
    calc avg (fun a : α =>
            expList α T fun l => ((1 : ℝ) / 2) ^ goodCountOf f I (a :: l))
        = avg (fun a : α =>
            ((1 : ℝ) / 2) ^ (if goodRoundOf f I a then 1 else 0)
              * expList α T fun l => ((1 : ℝ) / 2) ^ goodCountOf f (f I a) l) :=
          congrArg avg (funext key)
      _ ≤ avg (fun a : α =>
            ((1 : ℝ) / 2) ^ (if goodRoundOf f I a then 1 else 0) * ((15 : ℝ) / 16) ^ T) := by
          apply avg_le_avg
          intro a
          exact mul_le_mul_of_nonneg_left (ih (f I a) (hI.mono (hf I a))) (by positivity)
      _ = ((15 : ℝ) / 16) ^ T
            * avg (fun a : α => ((1 : ℝ) / 2) ^ (if goodRoundOf f I a then 1 else 0)) := by
          rw [← avg_const_mul]
          exact congrArg avg (funext fun a => mul_comm _ _)
      _ ≤ ((15 : ℝ) / 16) ^ T * ((15 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_left (avg_half_pow_goodOf (hgood I hI)) (by positivity)
      _ = ((15 : ℝ) / 16) ^ (T + 1) := (pow_succ _ _).symm

/-- **Phase 1** (as `phase1`): if `(9/8)^L ≥ n`, then after `T₁` rounds the informed set is
still `≤ n/2` with probability at most `2^L · (15/16)^T₁`. -/
lemma phase1Of (hf : ∀ I a, I ⊆ f I a)
    (hgood : ∀ I : Finset (Fin n), I.Nonempty →
      (1 : ℝ) / 8 ≤ avg (fun a : α => if goodRoundOf f I a then (1 : ℝ) else 0))
    (v₀ : Fin n) (L T₁ : ℕ) (hL : (n : ℝ) ≤ ((9 : ℝ) / 8) ^ L) :
    expList α T₁ (fun l => if 2 * (l.foldl f {v₀}).card ≤ n then (1 : ℝ) else 0)
      ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ := by
  have hpt : ∀ l : List α, (if 2 * (l.foldl f {v₀}).card ≤ n then (1 : ℝ) else 0)
      ≤ 2 ^ L * ((1 : ℝ) / 2) ^ goodCountOf f {v₀} l := by
    intro l
    by_cases h : 2 * (l.foldl f {v₀}).card ≤ n
    · rw [if_pos h]
      have hgrow := pow_goodCountOf_mul_card_le hf {v₀} l h
      rw [card_singleton] at hgrow
      have h1 : 1 ≤ (l.foldl f {v₀}).card :=
        card_pos.2 ((singleton_nonempty v₀).mono (subset_foldl hf _ l))
      have hltn : (l.foldl f {v₀}).card < n := by omega
      have hgL : ((9 : ℝ) / 8) ^ goodCountOf f {v₀} l < ((9 : ℝ) / 8) ^ L := by
        calc ((9 : ℝ) / 8) ^ goodCountOf f {v₀} l
            ≤ ((l.foldl f {v₀}).card : ℝ) := by simpa using hgrow
          _ < (n : ℝ) := by exact_mod_cast hltn
          _ ≤ ((9 : ℝ) / 8) ^ L := hL
      have hglt : goodCountOf f {v₀} l < L := by
        by_contra hge
        push Not at hge
        exact absurd (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 9 / 8) hge) (not_le.2 hgL)
      have h2g : (2 : ℝ) ^ goodCountOf f {v₀} l ≤ 2 ^ L :=
        pow_le_pow_right₀ (by norm_num) hglt.le
      have hpos : (0 : ℝ) < 2 ^ goodCountOf f {v₀} l := by positivity
      rw [div_pow, one_pow, mul_one_div, le_div_iff₀ hpos, one_mul]
      exact h2g
    · rw [if_neg h]
      positivity
  calc expList α T₁ (fun l => if 2 * (l.foldl f {v₀}).card ≤ n then (1 : ℝ) else 0)
      ≤ expList α T₁ (fun l => 2 ^ L * ((1 : ℝ) / 2) ^ goodCountOf f {v₀} l) :=
        expList_le_expList hpt
    _ = 2 ^ L * expList α T₁ (fun l => ((1 : ℝ) / 2) ^ goodCountOf f {v₀} l) :=
        expList_const_mul _ _ _
    _ ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ :=
        mul_le_mul_of_nonneg_left
          (expList_half_pow_goodCountOf hf hgood T₁ {v₀} (singleton_nonempty v₀))
          (by positivity)

omit [Nonempty α] in
/-- **Phase 2** (as `saturation`): starting above half, the expected number of uninformed
nodes after `T` further rounds is at most `(2/3)^T · (n - |I|)`. -/
lemma saturationOf (hf : ∀ I a, I ⊆ f I a)
    (hsat : ∀ I : Finset (Fin n), n ≤ 2 * I.card →
      avg (fun a : α => (n : ℝ) - (f I a).card) ≤ 2 / 3 * ((n : ℝ) - I.card))
    (T : ℕ) : ∀ I : Finset (Fin n), n ≤ 2 * I.card →
      expList α T (fun l => (n : ℝ) - (l.foldl f I).card)
        ≤ ((2 : ℝ) / 3) ^ T * ((n : ℝ) - I.card) := by
  induction T with
  | zero =>
    intro I _
    simp
  | succ T ih =>
    intro I hI
    rw [expList_succ]
    calc avg (fun a : α => expList α T fun l => (n : ℝ) - ((a :: l).foldl f I).card)
        ≤ avg (fun a : α => ((2 : ℝ) / 3) ^ T * ((n : ℝ) - (f I a).card)) := by
          apply avg_le_avg
          intro a
          exact ih (f I a) (le_trans hI (by have := card_le_card (hf I a); omega))
      _ = ((2 : ℝ) / 3) ^ T * avg (fun a : α => (n : ℝ) - (f I a).card) :=
          avg_const_mul _ _
      _ ≤ ((2 : ℝ) / 3) ^ T * (2 / 3 * ((n : ℝ) - I.card)) :=
          mul_le_mul_of_nonneg_left (hsat I hI) (by positivity)
      _ = ((2 : ℝ) / 3) ^ (T + 1) * ((n : ℝ) - I.card) := by
          rw [pow_succ]
          ring

/-- Gluing the two phases (as `prNotAllInformed_le`). -/
lemma notAllOf_le (hf : ∀ I a, I ⊆ f I a)
    (hgood : ∀ I : Finset (Fin n), I.Nonempty →
      (1 : ℝ) / 8 ≤ avg (fun a : α => if goodRoundOf f I a then (1 : ℝ) else 0))
    (hsat : ∀ I : Finset (Fin n), n ≤ 2 * I.card →
      avg (fun a : α => (n : ℝ) - (f I a).card) ≤ 2 / 3 * ((n : ℝ) - I.card))
    (v₀ : Fin n) (L T₁ T₂ : ℕ) (hL : (n : ℝ) ≤ ((9 : ℝ) / 8) ^ L) :
    expList α (T₁ + T₂) (fun l => if l.foldl f {v₀} = univ then (0 : ℝ) else 1)
      ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ + ((2 : ℝ) / 3) ^ T₂ * n := by
  rw [expList_append]
  have hinner : ∀ l₁ : List α,
      expList α T₂ (fun l₂ => if (l₁ ++ l₂).foldl f {v₀} = univ then (0 : ℝ) else 1)
        ≤ (if 2 * (l₁.foldl f {v₀}).card ≤ n then (1 : ℝ) else 0)
            + ((2 : ℝ) / 3) ^ T₂ * n := by
    intro l₁
    by_cases hA : 2 * (l₁.foldl f {v₀}).card ≤ n
    · rw [if_pos hA]
      have h1 : expList α T₂
          (fun l₂ => if (l₁ ++ l₂).foldl f {v₀} = univ then (0 : ℝ) else 1) ≤ 1 := by
        calc expList α T₂
              (fun l₂ => if (l₁ ++ l₂).foldl f {v₀} = univ then (0 : ℝ) else 1)
            ≤ expList α T₂ (fun _ => (1 : ℝ)) :=
              expList_le_expList fun l₂ => by split <;> norm_num
          _ = 1 := expList_const _ _
      have h2 : (0 : ℝ) ≤ ((2 : ℝ) / 3) ^ T₂ * n := by positivity
      linarith
    · rw [if_neg hA]
      push Not at hA
      have hpt : ∀ l₂ : List α,
          (if (l₁ ++ l₂).foldl f {v₀} = univ then (0 : ℝ) else 1)
            ≤ (n : ℝ) - (l₂.foldl f (l₁.foldl f {v₀})).card := by
        intro l₂
        rw [List.foldl_append]
        by_cases h : l₂.foldl f (l₁.foldl f {v₀}) = univ
        · rw [if_pos h, h, card_univ, Fintype.card_fin, sub_self]
        · rw [if_neg h]
          have hlt : (l₂.foldl f (l₁.foldl f {v₀})).card < n := by
            have hss : l₂.foldl f (l₁.foldl f {v₀}) ⊂ univ := ssubset_univ_iff.2 h
            simpa using card_lt_card hss
          have hc : ((l₂.foldl f (l₁.foldl f {v₀})).card : ℝ) + 1 ≤ n := by
            exact_mod_cast hlt
          linarith
      calc expList α T₂
            (fun l₂ => if (l₁ ++ l₂).foldl f {v₀} = univ then (0 : ℝ) else 1)
          ≤ expList α T₂ (fun l₂ => (n : ℝ) - (l₂.foldl f (l₁.foldl f {v₀})).card) :=
            expList_le_expList hpt
        _ ≤ ((2 : ℝ) / 3) ^ T₂ * ((n : ℝ) - (l₁.foldl f {v₀}).card) :=
            saturationOf hf hsat T₂ _ (le_of_lt hA)
        _ ≤ ((2 : ℝ) / 3) ^ T₂ * n := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have h0 : (0 : ℝ) ≤ ((l₁.foldl f {v₀}).card : ℝ) := by positivity
            linarith
        _ = 0 + ((2 : ℝ) / 3) ^ T₂ * n := (zero_add _).symm
  calc expList α T₁ (fun l₁ => expList α T₂
          fun l₂ => if (l₁ ++ l₂).foldl f {v₀} = univ then (0 : ℝ) else 1)
      ≤ expList α T₁ (fun l₁ =>
          (if 2 * (l₁.foldl f {v₀}).card ≤ n then (1 : ℝ) else 0)
            + ((2 : ℝ) / 3) ^ T₂ * n) :=
        expList_le_expList hinner
    _ = expList α T₁ (fun l₁ => if 2 * (l₁.foldl f {v₀}).card ≤ n then (1 : ℝ) else 0)
          + expList α T₁ (fun _ => ((2 : ℝ) / 3) ^ T₂ * n) :=
        expList_add _ _ _
    _ = expList α T₁ (fun l₁ => if 2 * (l₁.foldl f {v₀}).card ≤ n then (1 : ℝ) else 0)
          + ((2 : ℝ) / 3) ^ T₂ * n := by
        rw [expList_const]
    _ ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ + ((2 : ℝ) / 3) ^ T₂ * n := by
        have h := phase1Of hf hgood v₀ L T₁ hL
        linarith

/-- **More rounds never hurt**: for an inflationary step, the probability that not all nodes
are informed is antitone in the number of rounds. -/
lemma notAllOf_antitone (hf : ∀ I a, I ⊆ f I a) (I : Finset (Fin n)) {T T' : ℕ}
    (h : T ≤ T') :
    expList α T' (fun l => if l.foldl f I = univ then (0 : ℝ) else 1)
      ≤ expList α T (fun l => if l.foldl f I = univ then (0 : ℝ) else 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [expList_append]
  apply expList_le_expList
  intro l₁
  by_cases h₁ : l₁.foldl f I = univ
  · rw [if_pos h₁]
    calc expList α k (fun l₂ => if (l₁ ++ l₂).foldl f I = univ then (0 : ℝ) else 1)
        = expList α k (fun _ => (0 : ℝ)) := by
          congr 1
          funext l₂
          rw [if_pos (foldl_append_eq_univ hf h₁ l₂)]
      _ = 0 := expList_const _ _
      _ ≤ 0 := le_rfl
  · rw [if_neg h₁]
    calc expList α k (fun l₂ => if (l₁ ++ l₂).foldl f I = univ then (0 : ℝ) else 1)
        ≤ expList α k (fun _ => (1 : ℝ)) :=
          expList_le_expList fun l₂ => by split <;> norm_num
      _ = 1 := expList_const _ _

omit [Fintype α] [Nonempty α] in
/-- The round count of `push_informs_all_whp` is at most `⌈160 log n⌉`. -/
lemma rounds_le_ceil_160 (hn : 2 ≤ n) :
    (⌈(117 : ℝ) * Real.log n⌉₊ + 23) + ⌈(6 : ℝ) * Real.log n⌉₊ ≤ ⌈(160 : ℝ) * Real.log n⌉₊ := by
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h2 := Real.log_two_gt_d9
  have hg0 : 0 ≤ Real.log n := by linarith
  have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 117 * Real.log n)
  have h3 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 6 * Real.log n)
  have h4 := Nat.le_ceil ((160 : ℝ) * Real.log n)
  have hlt : (((⌈(117 : ℝ) * Real.log n⌉₊ + 23) + ⌈(6 : ℝ) * Real.log n⌉₊ : ℕ) : ℝ)
      < ⌈(160 : ℝ) * Real.log n⌉₊ := by
    push_cast
    linarith
  exact le_of_lt (by exact_mod_cast hlt)

/-- **The two-phase theorem for a general step**: if good rounds have probability `≥ 1/8` and
the expected uninformed count contracts by `2/3` above half, then after `⌈160 log n⌉` rounds
started from one informed node, not all nodes are informed with probability at most `2/n`. -/
theorem notAllOf_le_two_div (hn : 2 ≤ n) (hf : ∀ I a, I ⊆ f I a)
    (hgood : ∀ I : Finset (Fin n), I.Nonempty →
      (1 : ℝ) / 8 ≤ avg (fun a : α => if goodRoundOf f I a then (1 : ℝ) else 0))
    (hsat : ∀ I : Finset (Fin n), n ≤ 2 * I.card →
      avg (fun a : α => (n : ℝ) - (f I a).card) ≤ 2 / 3 * ((n : ℝ) - I.card))
    (v₀ : Fin n) :
    expList α ⌈(160 : ℝ) * Real.log n⌉₊ (fun l => if l.foldl f {v₀} = univ then (0 : ℝ) else 1)
      ≤ 2 / n := by
  have hA := numeric_A hn
  have hB := numeric_B hn
  have hC := numeric_C hn
  have h := notAllOf_le hf hgood hsat v₀ (⌈(9 : ℝ) * Real.log n⌉₊ + 1)
    (⌈(117 : ℝ) * Real.log n⌉₊ + 23) (⌈(6 : ℝ) * Real.log n⌉₊) hA
  have hmono := notAllOf_antitone (α := α) hf {v₀} (rounds_le_ceil_160 hn)
  have htwo : 1 / (n : ℝ) + 1 / n = 2 / n := by ring
  linarith

end RumorPush
