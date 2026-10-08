import Undecided.PluralityProgress

/-! # The stages of the `k`-colour dynamics (UND-3)

With `p = (k + 4) e^{-ℓ}` the probability of a bad round (`bad_le`):

* **Main stage** (`main_stage`): from a configuration `x₀` without undecided nodes in which
  every other colour has at most `θ c_m` nodes, after `T + 1` rounds the configuration lies in
  `Gset ... T = (Inv ∩ {Φ ≥ φ λ^T}) ∪ Fpsi` except with probability `(T + 1) p`, where
  `λ = 1 + κ/(8000B)` (`first_step`, then `inv_step`, `phi_step`, `fpsi_step`, through
  `Dynamics.expList_escape` with moving targets). Since `Φ ≤ n`, `Gset ... T ⊆ Fpsi` as soon
  as `φ λ^T > n`.
* **Final stage** (`fin_stage`): from `Fpsi`, the probability of not being monochromatic in `m`
  after `T` rounds is at most `(3/4)^T (4S + q) + T p` (`4S + q` contracts in expectation and
  `Fpsi` persists except with probability `p` per round; UND-1's `fin_stage` pattern).

The stages are composed by `miss_comp` (Markov property), where `miss D T x` is the
probability of missing `D` after `T` rounds from `x`.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

/-- Probability of missing `D` after `T` rounds started from `x`. -/
noncomputable def miss (D : Set (Config n k)) (T : ℕ) (x : Config n k) : ℝ := by
  classical
  exact expList (Fin n → Fin n) T (fun l => if l.foldl step x ∈ D then 0 else 1)

/-- All nodes hold colour `m`. -/
def allM (m : Fin k) : Set (Config n k) := {x | x = fun _ => some m}

/-! ### Missing probabilities -/

lemma miss_succ (D : Set (Config n k)) (T : ℕ) (x : Config n k) :
    miss D (T + 1) x = avg (fun r : Fin n → Fin n => miss D T (step x r)) := rfl

lemma miss_nonneg (D : Set (Config n k)) (T : ℕ) (x : Config n k) : 0 ≤ miss D T x := by
  classical
  unfold miss
  exact expList_nonneg fun l => by split <;> norm_num

lemma miss_le_one [NeZero n] (D : Set (Config n k)) (T : ℕ) (x : Config n k) :
    miss D T x ≤ 1 := by
  classical
  unfold miss
  calc _ ≤ expList (Fin n → Fin n) T (fun _ => (1 : ℝ)) :=
        expList_le_expList fun l => by split <;> norm_num
    _ = 1 := expList_const T 1

/-- Missing a smaller set is more likely. -/
lemma miss_mono {D D' : Set (Config n k)} (h : D ⊆ D') (T : ℕ) (x : Config n k) :
    miss D' T x ≤ miss D T x := by
  classical
  unfold miss
  refine expList_le_expList fun l => ?_
  by_cases hD : l.foldl step x ∈ D
  · simp [hD, h hD]
  · rw [if_neg hD]
    split <;> norm_num

/-- **Composition of stages** (Markov property). -/
lemma miss_comp [NeZero n] {D E : Set (Config n k)} {T₁ T₂ : ℕ} {e : ℝ} (he : 0 ≤ e)
    (hE : ∀ y ∈ D, miss E T₂ y ≤ e) (x : Config n k) :
    miss E (T₁ + T₂) x ≤ miss D T₁ x + e := by
  classical
  have key (l₁ : List (Fin n → Fin n)) :
      expList (Fin n → Fin n) T₂ (fun l₂ => if (l₁ ++ l₂).foldl step x ∈ E then (0 : ℝ) else 1)
        = miss E T₂ (l₁.foldl step x) := by
    simp only [miss, List.foldl_append]
  have hpt (l₁ : List (Fin n → Fin n)) : miss E T₂ (l₁.foldl step x)
      ≤ (if l₁.foldl step x ∈ D then (0 : ℝ) else 1) + e := by
    by_cases hD : l₁.foldl step x ∈ D
    · rw [if_pos hD, zero_add]
      exact hE _ hD
    · rw [if_neg hD]
      linarith [miss_le_one E T₂ (l₁.foldl step x)]
  calc miss E (T₁ + T₂) x
      = expList (Fin n → Fin n) T₁ (fun l₁ => miss E T₂ (l₁.foldl step x)) := by
        rw [← funext key]
        exact expList_append T₁ T₂ _
    _ ≤ expList (Fin n → Fin n) T₁
          (fun l₁ => (if l₁.foldl step x ∈ D then (0 : ℝ) else 1) + e) :=
        expList_le_expList hpt
    _ = miss D T₁ x + e := by
        rw [expList_add, expList_const]
        rfl

lemma foldl_const (o : Option (Fin k)) (l : List (Fin n → Fin n)) :
    l.foldl step (fun _ : Fin n => o) = fun _ => o := by
  induction l with
  | nil => rfl
  | cons r l ih => simp only [List.foldl_cons, step_const, ih]

/-- Once all nodes hold `m`, they keep it. -/
lemma miss_allM_of_mem {y : Config n k} {m : Fin k} (hy : y ∈ allM m) (T : ℕ) :
    miss (allM m) T y = 0 := by
  classical
  have hy' : y = fun _ => some m := hy
  unfold miss
  simp_rw [hy', foldl_const]
  simp only [allM, Set.mem_setOf_eq, if_true]
  exact expList_zero_fun T

/-- The probability of not being monochromatic in `m` does not increase with time. -/
lemma miss_allM_antitone [NeZero n] (x : Config n k) (m : Fin k) {T T' : ℕ} (h : T ≤ T') :
    miss (allM m) T' x ≤ miss (allM m) T x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have := miss_comp (D := allM m) (E := allM m) (T₁ := T) (T₂ := j) le_rfl
    (fun y hy => (miss_allM_of_mem hy j).le) x
  linarith

/-! ### One round -/

variable [NeZero n]

/-- If every good round from `x` lands in `D`, a round from `x` misses `D` with probability at
most `(k + 4) e^{-ℓ}`. -/
lemma round_le {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin k) (x : Config n k) (D : Set (Config n k))
    (hD : ∀ y, Good ℓ m x y → y ∈ D) :
    avg (fun r : Fin n → Fin n => by classical exact if step x r ∈ D then (0 : ℝ) else 1)
      ≤ (k + 4) * exp (-ℓ) := by
  classical
  refine le_trans (avg_le_avg fun r => ?_) (bad_le x m hℓ)
  by_cases h : step x r ∈ D
  · simp only [h, if_true]
    split <;> norm_num
  · have hG : ¬ Good ℓ m x (step x r) := fun hG => h (hD _ hG)
    simp [h, hG]

/-! ### The main stage -/

/-- The targets of the main stage: `(Inv ∩ {Φ ≥ φ λ^t}) ∪ Fpsi`. -/
def Gset (ℓ θ B φ lam : ℝ) (m : Fin k) (t : ℕ) : Set (Config n k) :=
  {y | y ∈ Inv ℓ θ B m ∧ φ * lam ^ t ≤ mu y m} ∪ Fpsi m

/-- The targets of the main stage, starting from `x₀` at time `0`. -/
def Hset (x₀ : Config n k) (ℓ θ B φ lam : ℝ) (m : Fin k) : ℕ → Set (Config n k)
  | 0 => {x₀}
  | t + 1 => Gset ℓ θ B φ lam m t

/-- **Main stage.** -/
theorem main_stage {ℓ θ B φ : ℝ} (H : Hyp n ℓ θ B φ) {m : Fin k} {x₀ : Config n k}
    (hq : und x₀ = 0) (hθx : ∀ i, i ≠ m → cnt x₀ i ≤ θ * cnt x₀ m) (hmd : B = 2 * md x₀)
    (hφ : 2 * φ ≤ mu x₀ m) (T : ℕ) :
    miss (Gset ℓ θ B φ (1 + (1 - θ) / (4000 * B) / 2) m T) (T + 1) x₀
      ≤ ((T + 1 : ℕ) : ℝ) * ((k + 4) * exp (-ℓ)) := by
  set lam := 1 + (1 - θ) / (4000 * B) / 2 with hlam
  have hp : 0 ≤ (k + 4 : ℝ) * exp (-ℓ) := by positivity
  have hlam1 : 1 ≤ lam := by
    have : 0 ≤ (1 - θ) / (4000 * B) / 2 := by
      have := H.kappa_pos
      have := H.hB
      positivity
    linarith
  have hφ0 : 0 ≤ φ := by
    by_contra h
    have : θ ^ 2 * (1 - θ) ^ 2 * φ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_le.mp h).le
    linarith [H.h1, H.hℓ]
  refine expList_escape step hp (T + 1) (Hset x₀ ℓ θ B φ lam m) x₀ rfl ?_
  intro t _ y hy
  cases t with
  | zero =>
    have hy' : y = x₀ := hy
    subst hy'
    refine round_le H.hℓ m y _ fun z hz => ?_
    obtain ⟨h1, h2⟩ := first_step H hq hθx hmd hφ hz
    left
    exact ⟨h1, by simpa using h2⟩
  | succ s =>
    refine round_le H.hℓ m y _ fun z hz => ?_
    rcases hy with ⟨hinv, hΦ⟩ | hF
    · by_cases hF : y ∈ Fpsi m
      · exact Or.inr (fpsi_step H.hn H.hℓ.le H.h5 hF hz)
      · have hφy : φ ≤ mu y m := by
          have : φ ≤ φ * lam ^ s := le_mul_of_one_le_right hφ0 (one_le_pow₀ hlam1)
          linarith
        left
        refine ⟨inv_step H hinv hφy hz, ?_⟩
        have := phi_step H hinv hφy hF hz
        rw [pow_succ]
        have : φ * lam ^ s * lam ≤ mu y m * lam :=
          mul_le_mul_of_nonneg_right hΦ (by linarith)
        rw [← hlam] at *
        nlinarith
    · exact Or.inr (fpsi_step H.hn H.hℓ.le H.h5 hF hz)

/-- Once `φ λ^T > n`, the targets of the main stage lie in `Fpsi`. -/
lemma Gset_sub {ℓ θ B φ lam : ℝ} {m : Fin k} {T : ℕ} (hT : (n : ℝ) < φ * lam ^ T) :
    Gset ℓ θ B φ lam m T ⊆ (Fpsi m : Set (Config n k)) := by
  rintro y (⟨-, hy⟩ | hy)
  · exfalso
    have := mu_le_n y m (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
    linarith
  · exact hy

/-! ### The final stage -/

lemma avg_oth_step (x : Config n k) (m : Fin k) :
    avg (fun r : Fin n → Fin n => oth (step x r) m) = muS x m := by
  simp_rw [oth_step_ind]
  rw [avg_sum, ← sum_avg_indS]
  exact sum_congr rfl fun v _ => avg_eval n v (indS x m v)

lemma avg_und_step (x : Config n k) :
    avg (fun r : Fin n → Fin n => und (step x r)) = muU x := by
  unfold und
  rw [expected_count_none]
  rfl

/-- The potential `Ψ = 4S + q` of the final stage. -/
noncomputable def psi (x : Config n k) (m : Fin k) : ℝ := 4 * oth x m + und x

omit [NeZero n] in
lemma psi_nonneg (x : Config n k) (m : Fin k) : 0 ≤ psi x m := by
  unfold psi
  have := oth_nonneg x m
  have := und_nonneg x
  linarith

omit [NeZero n] in
/-- A configuration that is not monochromatic in `m` has `Ψ ≥ 1`. -/
lemma one_le_psi {x : Config n k} {m : Fin k} (hx : x ∉ allM m) : 1 ≤ psi x m := by
  have hv : ∃ v, x v ≠ some m := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨v, hv⟩ := hv
  have hS := oth_nonneg x m
  have hq := und_nonneg x
  unfold psi
  cases h : x v with
  | none =>
    have : (1 : ℝ) ≤ und x := by
      have : 0 < count x none := Finset.card_pos.mpr ⟨v, by simp [h]⟩
      unfold und
      exact_mod_cast this
    linarith
  | some j =>
    have hj : j ≠ m := fun e => hv (by rw [h, e])
    have : (1 : ℝ) ≤ cnt x j := by
      have : 0 < count x (some j) := Finset.card_pos.mpr ⟨v, by simp [h]⟩
      unfold cnt
      exact_mod_cast this
    have := cnt_le_oth x hj
    linarith

/-- **Final stage.** -/
theorem fin_stage {ℓ : ℝ} (hℓ : 0 < ℓ) (h5 : 160000 * ℓ ≤ n) (m : Fin k) :
    ∀ T : ℕ, ∀ x ∈ (Fpsi m : Set (Config n k)),
      miss (allM m) T x ≤ (3 / 4) ^ T * psi x m + T * ((k + 4) * exp (-ℓ))
  | 0, x, _ => by
    classical
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
    unfold miss
    simp only [expList, List.foldl_nil]
    by_cases h : x ∈ allM m
    · rw [if_pos h]
      exact psi_nonneg x m
    · rw [if_neg h]
      exact one_le_psi h
  | T + 1, x, hx => by
    classical
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    set p := (k + 4 : ℝ) * exp (-ℓ) with hpdef
    have hp : 0 ≤ p := by positivity
    have hpt (r : Fin n → Fin n) : miss (allM m) T (step x r)
        ≤ (3 / 4) ^ T * psi (step x r) m + T * p + (if step x r ∈ Fpsi m then 0 else 1) := by
      by_cases h : step x r ∈ Fpsi m
      · rw [if_pos h, add_zero]
        exact fin_stage hℓ h5 m T _ h
      · rw [if_neg h]
        have h1 := miss_le_one (allM m) T (step x r)
        have h2 : 0 ≤ (3 / 4 : ℝ) ^ T * psi (step x r) m :=
          mul_nonneg (by positivity) (psi_nonneg _ m)
        have h3 : (0 : ℝ) ≤ T * p := by positivity
        linarith
    have hround : avg (fun r : Fin n → Fin n => if step x r ∈ Fpsi m then (0 : ℝ) else 1)
        ≤ p := round_le hℓ m x _ fun y hy => fpsi_step hn hℓ.le h5 hx hy
    have hexp : avg (fun r : Fin n → Fin n => psi (step x r) m) ≤ 3 / 4 * psi x m := by
      unfold psi
      rw [avg_add, avg_const_mul, avg_oth_step, avg_und_step]
      exact fpsi_expect hn (cnt_le_n x m) (oth_nonneg x m) (und_nonneg x) (muS_le x m)
        (muU_le x m) hx
    rw [miss_succ]
    calc avg (fun r => miss (allM m) T (step x r))
        ≤ avg (fun r => (3 / 4) ^ T * psi (step x r) m + T * p
            + (if step x r ∈ Fpsi m then (0 : ℝ) else 1)) := avg_le_avg hpt
      _ = (3 / 4) ^ T * avg (fun r : Fin n → Fin n => psi (step x r) m) + T * p
            + avg (fun r : Fin n → Fin n => if step x r ∈ Fpsi m then (0 : ℝ) else 1) := by
          rw [avg_add, avg_add, avg_const_mul, avg_const]
      _ ≤ (3 / 4) ^ T * (3 / 4 * psi x m) + T * p + p := by
          have : (3 / 4 : ℝ) ^ T * avg (fun r : Fin n → Fin n => psi (step x r) m)
              ≤ (3 / 4) ^ T * (3 / 4 * psi x m) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
          linarith
      _ = (3 / 4) ^ (T + 1) * psi x m + ((T + 1 : ℕ) : ℝ) * p := by
          push_cast
          ring

end Undecided.Plurality
