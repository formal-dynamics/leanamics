import Undecided.MajorityRound
import Undecided.MajorityArith

/-! # The phases of the majority dynamics (UND-1)

With `Λ ≥ 0` the per-round deviation (later `Λ = √(n log n)`) and `p = 4 exp(-2Λ²/n)` the
probability of a bad round (`bad_round`):

* **Growth** (`growth_stage`): from a bias of at least `402Λ`, after `T + 1` rounds the
  configuration lies in `growthSet n (theta n Λ T)` except with probability `(T + 1) p`;
  the threshold `theta` grows by the factor `201/200` per round up to `7n/10`
  (Clementi et al., MFCS 2018, phases `H4`, `H5`, `H7`).
* **Bridge** (`bridge_stage`): from a bias of at least `7n/10`, after `18` rounds the potential
  `pot = 12 count b + count u` is at most `n/3` except with probability `18 p`.
* **Final phase** (`fin_stage`): from `pot ≤ n/3`, the probability of not being all-`a` after
  `T` rounds is at most `(5/6)^T pot + T p` (`pot` contracts in expectation, and `pot ≤ n/3`
  persists except with probability `p` per round; Clementi et al., phase `H6`).

The stages are composed by `missP_comp`, where `missP B T x` is the probability of missing `B`
after `T` rounds from `x`.
-/

namespace Undecided
open Finset Dynamics Real

variable {n : ℕ}

/-- The bias `count a - count b`. -/
noncomputable def bias (x : Config n) : ℝ := (count x .a : ℝ) - count x .b

/-- The potential `12 count b + count u` of the final phase. -/
noncomputable def pot (x : Config n) : ℝ := 12 * (count x .b : ℝ) + count x .u

/-- Growth phase with threshold `g`: the bias is at least `g`, and there are `n/100` undecided
nodes or the bias is at least `g + n/20`. -/
def growthSet (n : ℕ) (g : ℝ) : Set (Config n) :=
  {x | g ≤ bias x ∧ ((n : ℝ) / 100 ≤ count x .u ∨ g + n / 20 ≤ bias x)}

/-- Bridge phase: the bias is at least `s` and the potential at most `ψ`. -/
def bridgeSet (n : ℕ) (s ψ : ℝ) : Set (Config n) := {x | s ≤ bias x ∧ pot x ≤ ψ}

/-- Final phase: the potential is at most `n/3`. -/
def finSet (n : ℕ) : Set (Config n) := {x | pot x ≤ (n : ℝ) / 3}

/-- All nodes hold `a`. -/
def allA (n : ℕ) : Set (Config n) := {x | x = fun _ => .a}

/-- Probability of missing `B` after `T` rounds started from `x`. -/
noncomputable def missP (B : Set (Config n)) (T : ℕ) (x : Config n) : ℝ := by
  classical
  exact expList (Fin n → Fin n) T (fun l => if l.foldl step x ∈ B then 0 else 1)

/-- Probability of missing `B` after one round started from `x`. -/
noncomputable def missOne (B : Set (Config n)) (x : Config n) : ℝ :=
  avg (fun r : Fin n → Fin n => by classical exact if step x r ∈ B then (0 : ℝ) else 1)

/-! ### Elementary facts -/

lemma pot_nonneg (x : Config n) : 0 ≤ pot x := by
  unfold pot
  have : (0 : ℝ) ≤ count x .b := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ count x .u := Nat.cast_nonneg _
  linarith

/-- A configuration that is not all-`a` has potential at least `1`. -/
lemma one_le_pot {x : Config n} (hx : x ∉ allA n) : 1 ≤ pot x := by
  have hv : ∃ v, x v ≠ .a := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨v, hv⟩ := hv
  have hpos (o : Op) (ho : x v = o) : (1 : ℝ) ≤ count x o := by
    have : 0 < count x o := Finset.card_pos.mpr ⟨v, by simp [ho]⟩
    exact_mod_cast this
  unfold pot
  have : (0 : ℝ) ≤ count x .b := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ count x .u := Nat.cast_nonneg _
  cases h : x v with
  | a => exact absurd h hv
  | b => have := hpos .b h; linarith
  | u => have := hpos .u h; linarith

/-- Rounds do not move a monochromatic configuration. -/
lemma foldl_of_mono {x : Config n} (hx : Mono x) (l : List (Fin n → Fin n)) :
    l.foldl step x = x := by
  induction l with
  | nil => rfl
  | cons r l ih => simp only [List.foldl_cons, step_of_mono x hx r, ih]

/-! ### Missing probabilities -/

lemma missP_zero (B : Set (Config n)) (x : Config n) :
    missP B 0 x = by classical exact if x ∈ B then 0 else 1 := rfl

lemma missP_succ (B : Set (Config n)) (T : ℕ) (x : Config n) :
    missP B (T + 1) x = avg (fun r : Fin n → Fin n => missP B T (step x r)) := rfl

lemma missP_nonneg (B : Set (Config n)) (T : ℕ) (x : Config n) : 0 ≤ missP B T x := by
  classical
  unfold missP
  exact expList_nonneg fun l => by split <;> norm_num

lemma missP_le_one [NeZero n] (B : Set (Config n)) (T : ℕ) (x : Config n) :
    missP B T x ≤ 1 := by
  classical
  unfold missP
  calc _ ≤ expList (Fin n → Fin n) T (fun _ => (1 : ℝ)) :=
        expList_le_expList fun l => by split <;> norm_num
    _ = 1 := expList_const T 1

/-- Missing a smaller set is more likely. -/
lemma missP_mono {B B' : Set (Config n)} (h : B ⊆ B') (T : ℕ) (x : Config n) :
    missP B' T x ≤ missP B T x := by
  classical
  unfold missP
  refine expList_le_expList fun l => ?_
  by_cases hB : l.foldl step x ∈ B
  · simp [hB, h hB]
  · rw [if_neg hB]
    split <;> norm_num

/-- **Composition of stages** (Markov property): if from every state of `B` the chain misses
`D` after `T₂` rounds with probability at most `e`, then from `x` it misses `D` after
`T₁ + T₂` rounds with probability at most `missP B T₁ x + e`. -/
lemma missP_comp [NeZero n] {B D : Set (Config n)} {T₁ T₂ : ℕ} {e : ℝ} (he : 0 ≤ e)
    (hD : ∀ y ∈ B, missP D T₂ y ≤ e) (x : Config n) :
    missP D (T₁ + T₂) x ≤ missP B T₁ x + e := by
  classical
  have key (l₁ : List (Fin n → Fin n)) :
      expList (Fin n → Fin n) T₂ (fun l₂ => if (l₁ ++ l₂).foldl step x ∈ D then (0 : ℝ) else 1)
        = missP D T₂ (l₁.foldl step x) := by
    simp only [missP, List.foldl_append]
  have hpt (l₁ : List (Fin n → Fin n)) : missP D T₂ (l₁.foldl step x)
      ≤ (if l₁.foldl step x ∈ B then (0 : ℝ) else 1) + e := by
    by_cases hB : l₁.foldl step x ∈ B
    · rw [if_pos hB, zero_add]
      exact hD _ hB
    · rw [if_neg hB]
      linarith [missP_le_one D T₂ (l₁.foldl step x)]
  calc missP D (T₁ + T₂) x
      = expList (Fin n → Fin n) T₁ (fun l₁ => missP D T₂ (l₁.foldl step x)) := by
        rw [← funext key]
        exact expList_append T₁ T₂ _
    _ ≤ expList (Fin n → Fin n) T₁
          (fun l₁ => (if l₁.foldl step x ∈ B then (0 : ℝ) else 1) + e) :=
        expList_le_expList hpt
    _ = missP B T₁ x + e := by
        rw [expList_add, expList_const]
        rfl

/-- Once all nodes hold `a`, they keep it. -/
lemma missP_allA_of_mem {y : Config n} (hy : y ∈ allA n) (T : ℕ) : missP (allA n) T y = 0 := by
  classical
  have hm : Mono y := ⟨.a, fun v => by rw [show y = fun _ => .a from hy]⟩
  unfold missP
  simp_rw [foldl_of_mono hm, if_pos hy]
  exact expList_zero_fun T

/-- The probability of not being all-`a` does not increase with time. -/
lemma missP_allA_antitone [NeZero n] (x : Config n) {T T' : ℕ} (h : T ≤ T') :
    missP (allA n) T' x ≤ missP (allA n) T x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := missP_comp (B := allA n) (D := allA n) (T₁ := T) (T₂ := k) le_rfl
    (fun y hy => (missP_allA_of_mem hy k).le) x
  linarith

/-! ### One round in each phase -/

variable [NeZero n]

/-- `bad_round` with the exact expectations of `Undecided.Basic` substituted. -/
lemma round_le (x : Config n) (B : Set (Config n)) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hB : ∀ y : Config n,
      (count x .a : ℝ) * (n - count x .b + count x .u) / n < count y .a + Λ →
      (count y .b : ℝ) < count x .b * (n - count x .a + count x .u) / n + Λ →
      ((count x .u : ℝ) ^ 2 + 2 * count x .a * count x .b) / n < count y .u + Λ →
      (count y .u : ℝ) < (count x .u ^ 2 + 2 * count x .a * count x .b) / n + Λ → y ∈ B) :
    missOne B x ≤ 4 * exp (-(2 * Λ ^ 2 / n)) := by
  refine bad_round x B hΛ fun y h1 h2 h3 h4 => hB y ?_ ?_ ?_ ?_
  · rwa [expected_count_a] at h1
  · rwa [expected_count_b] at h2
  · rwa [expected_count_u] at h3
  · rwa [expected_count_u] at h4

variable {Λ : ℝ}

/-- The first round: from a bias of at least `402Λ` into `growthSet n (400Λ)`. -/
lemma first_round (hn : (0 : ℝ) < n) (hΛ : 0 ≤ Λ) (hΛn : 2000 * Λ ≤ n) (x : Config n)
    (hx : 402 * Λ ≤ bias x) :
    missOne (growthSet n (400 * Λ)) x ≤ 4 * exp (-(2 * Λ ^ 2 / n)) :=
  round_le x _ hΛ fun _ h1 h2 h3 _ =>
    first_det hn hΛ hΛn (Nat.cast_nonneg _) (count_add x) hx h1 h2 h3

/-- A growth round: from `growthSet n g` into `growthSet n (min (201g/200) (7n/10))`. -/
lemma growth_round (hn : (0 : ℝ) < n) (hΛ : 0 ≤ Λ) (hΛn : 2000 * Λ ≤ n) {g : ℝ}
    (hg1 : 400 * Λ ≤ g) (hg2 : g ≤ 7 * n / 10) (x : Config n) (hx : x ∈ growthSet n g) :
    missOne (growthSet n (min (201 / 200 * g) (7 * n / 10))) x
      ≤ 4 * exp (-(2 * Λ ^ 2 / n)) :=
  round_le x _ hΛ fun _ h1 h2 h3 _ =>
    growth_det hn hΛ hΛn hg1 hg2 (Nat.cast_nonneg _) (count_add x) hx.1 hx.2 h1 h2 h3

/-- A bridge round: from `bridgeSet n s ψ` (with `s ≥ 2n/3`, `ψ ≥ 195Λ`) into
`bridgeSet n s' ψ'` for `s' ≤ s - 2Λ` and `ψ' ≥ 9ψ/10`. -/
lemma bridge_round (hn : (0 : ℝ) < n) (hΛ : 0 ≤ Λ) {s ψ s' ψ' : ℝ} (hs : 2 * n / 3 ≤ s)
    (hψ : 195 * Λ ≤ ψ) (hs' : s' ≤ s - 2 * Λ) (hψ' : 9 / 10 * ψ ≤ ψ') (x : Config n)
    (hx : x ∈ bridgeSet n s ψ) :
    missOne (bridgeSet n s' ψ') x ≤ 4 * exp (-(2 * Λ ^ 2 / n)) := by
  refine round_le x _ hΛ fun y h1 h2 _ h4 => ?_
  obtain ⟨hb1, hb2⟩ := bridge_det hn (Nat.cast_nonneg _) (Nat.cast_nonneg _) (count_add x)
    (le_trans hs hx.1) hx.2 hψ h1 h2 h4
  have hx1 : s ≤ bias x := hx.1
  refine ⟨?_, ?_⟩
  · show s' ≤ (count y .a : ℝ) - count y .b
    unfold bias at hx1
    linarith
  · show 12 * (count y .b : ℝ) + count y .u ≤ ψ'
    linarith

/-- A final-phase round stays in `finSet n` except with probability `4 exp(-2Λ²/n)`. -/
lemma fin_round (hn : (0 : ℝ) < n) (hΛ : 0 ≤ Λ) (hΛn : 234 * Λ ≤ n) (x : Config n)
    (hx : x ∈ finSet n) :
    missOne (finSet n) x ≤ 4 * exp (-(2 * Λ ^ 2 / n)) :=
  round_le x _ hΛ fun _ _ h2 _ h4 =>
    fin_det hn hΛn (Nat.cast_nonneg _) (Nat.cast_nonneg _) (count_add x) hx h2 h4

/-- In the final phase the potential contracts by `5/6` in expectation. -/
lemma avg_pot_step (hn : (0 : ℝ) < n) (x : Config n) (hx : x ∈ finSet n) :
    avg (fun r : Fin n → Fin n => pot (step x r)) ≤ 5 / 6 * pot x := by
  unfold pot
  rw [avg_add, avg_const_mul, expected_count_b, expected_count_u]
  exact fin_expect hn (Nat.cast_nonneg _) (Nat.cast_nonneg _) (count_add x) hx

/-! ### The growth stage -/

/-- Growth thresholds: `theta 0 = 400Λ` and `theta (t+1) = min (201/200 · theta t) (7n/10)`. -/
noncomputable def theta (n : ℕ) (Λ : ℝ) : ℕ → ℝ
  | 0 => 400 * Λ
  | t + 1 => min (201 / 200 * theta n Λ t) (7 * n / 10)

omit [NeZero n] in
lemma theta_bounds (hΛ : 0 ≤ Λ) (h : 400 * Λ ≤ 7 * n / 10) :
    ∀ t, 400 * Λ ≤ theta n Λ t ∧ theta n Λ t ≤ 7 * n / 10
  | 0 => ⟨le_rfl, h⟩
  | t + 1 => by
    obtain ⟨h1, _⟩ := theta_bounds hΛ h t
    refine ⟨le_min ?_ h, min_le_right _ _⟩
    nlinarith

omit [NeZero n] in
/-- After `t` steps the threshold is `7n/10` or at least `400Λ (201/200)^t`. -/
lemma theta_reach (hΛ : 0 ≤ Λ) (h : 400 * Λ ≤ 7 * n / 10) :
    ∀ t, 7 * n / 10 ≤ theta n Λ t ∨ 400 * Λ * (201 / 200) ^ t ≤ theta n Λ t
  | 0 => Or.inr (by simp [theta])
  | t + 1 => by
    have hb := theta_bounds hΛ h t
    have hc : (0 : ℝ) ≤ 7 * n / 10 := le_trans (by positivity) h
    show 7 * n / 10 ≤ min (201 / 200 * theta n Λ t) (7 * n / 10) ∨
      400 * Λ * (201 / 200) ^ (t + 1) ≤ min (201 / 200 * theta n Λ t) (7 * n / 10)
    rcases le_total (201 / 200 * theta n Λ t) (7 * n / 10) with hle | hle
    · rw [min_eq_left hle]
      rcases theta_reach hΛ h t with h1 | h1
      · left
        nlinarith
      · right
        rw [pow_succ]
        nlinarith
    · rw [min_eq_right hle]
      exact Or.inl le_rfl

/-- Targets of the growth stage: a bias of at least `402Λ` at time `0`, then
`growthSet n (theta n Λ t)` at time `t + 1`. -/
def growthTarget (n : ℕ) (Λ : ℝ) : ℕ → Set (Config n)
  | 0 => {x | 402 * Λ ≤ bias x}
  | t + 1 => growthSet n (theta n Λ t)

/-- **Growth stage.** From a bias of at least `402Λ`, after `T + 1` rounds the configuration
lies in `growthSet n (theta n Λ T)` except with probability `(T + 1) · 4 exp(-2Λ²/n)`. -/
theorem growth_stage (hn : (0 : ℝ) < n) (hΛ : 0 ≤ Λ) (hΛn : 2000 * Λ ≤ n) (T : ℕ)
    (x : Config n) (hx : 402 * Λ ≤ bias x) :
    missP (growthSet n (theta n Λ T)) (T + 1) x
      ≤ ((T + 1 : ℕ) : ℝ) * (4 * exp (-(2 * Λ ^ 2 / n))) := by
  have hp : 0 ≤ 4 * exp (-(2 * Λ ^ 2 / n)) := by positivity
  refine expList_escape step hp (T + 1) (growthTarget n Λ) x hx ?_
  intro t _ y hy
  cases t with
  | zero => exact first_round hn hΛ hΛn y hy
  | succ s =>
    obtain ⟨h1, h2⟩ := theta_bounds (n := n) hΛ (by linarith) s
    exact growth_round hn hΛ hΛn h1 h2 y hy

/-! ### The bridge stage -/

/-- Targets of the bridge stage: bias at least `7n/10 - 2jΛ`, potential at most
`2n (9/10)^j`. -/
def bridgeTarget (n : ℕ) (Λ : ℝ) (j : ℕ) : Set (Config n) :=
  bridgeSet n (7 * n / 10 - 2 * j * Λ) (2 * n * (9 / 10) ^ j)

/-- **Bridge stage.** From a bias of at least `7n/10`, after `18` rounds the potential is at
most `n/3` except with probability `18 · 4 exp(-2Λ²/n)`. -/
theorem bridge_stage (hn : (0 : ℝ) < n) (hΛ : 0 ≤ Λ) (hΛn : 2000 * Λ ≤ n) (x : Config n)
    (hx : 7 * n / 10 ≤ bias x) :
    missP (finSet n) 18 x ≤ ((18 : ℕ) : ℝ) * (4 * exp (-(2 * Λ ^ 2 / n))) := by
  have hp : 0 ≤ 4 * exp (-(2 * Λ ^ 2 / n)) := by positivity
  have h0 : x ∈ bridgeTarget n Λ 0 := by
    have hs := count_add x
    have hb : (0 : ℝ) ≤ count x .b := Nat.cast_nonneg _
    have hu : (0 : ℝ) ≤ count x .u := Nat.cast_nonneg _
    unfold bias at hx
    refine ⟨?_, ?_⟩
    · show 7 * n / 10 - 2 * ((0 : ℕ) : ℝ) * Λ ≤ (count x .a : ℝ) - count x .b
      simpa using hx
    · show 12 * (count x .b : ℝ) + count x .u ≤ 2 * n * (9 / 10) ^ 0
      simp only [pow_zero, mul_one]
      linarith
  have hsub : bridgeTarget n Λ 18 ⊆ finSet n := by
    intro y hy
    have h2 : pot y ≤ 2 * n * (9 / 10) ^ 18 := hy.2
    show pot y ≤ (n : ℝ) / 3
    have : (2 : ℝ) * n * (9 / 10) ^ 18 ≤ n / 3 := by
      have : (2 : ℝ) * (9 / 10) ^ 18 ≤ 1 / 3 := by norm_num
      nlinarith
    linarith
  refine le_trans (missP_mono hsub 18 x) ?_
  refine expList_escape step hp 18 (bridgeTarget n Λ) x h0 ?_
  intro j hj y hy
  have hj' : (j : ℝ) ≤ 17 := by exact_mod_cast Nat.lt_succ_iff.mp hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpow : (9 / 10 : ℝ) ^ 17 ≤ (9 / 10) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_succ_iff.mp hj)
  have h17 : (1 : ℝ) / 6 ≤ (9 / 10) ^ 17 := by norm_num
  refine bridge_round hn hΛ ?_ ?_ ?_ ?_ y hy
  · nlinarith
  · nlinarith
  · push_cast
    linarith
  · rw [pow_succ]
    linarith

/-! ### The final stage -/

/-- **Final stage.** From `pot ≤ n/3`, the probability of not being all-`a` after `T` rounds
is at most `(5/6)^T pot + T · 4 exp(-2Λ²/n)`. -/
theorem fin_stage (hn : (0 : ℝ) < n) (hΛ : 0 ≤ Λ) (hΛn : 234 * Λ ≤ n) :
    ∀ T : ℕ, ∀ x ∈ finSet n,
      missP (allA n) T x ≤ (5 / 6) ^ T * pot x + T * (4 * exp (-(2 * Λ ^ 2 / n)))
  | 0, x, _ => by
    classical
    rw [missP_zero]
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
    by_cases h : x ∈ allA n
    · rw [if_pos h]
      exact pot_nonneg x
    · rw [if_neg h]
      exact one_le_pot h
  | T + 1, x, hx => by
    classical
    set p := 4 * exp (-(2 * Λ ^ 2 / n)) with hpdef
    have hp : 0 ≤ p := by positivity
    have hpt (r : Fin n → Fin n) : missP (allA n) T (step x r)
        ≤ (5 / 6) ^ T * pot (step x r) + T * p + (if step x r ∈ finSet n then 0 else 1) := by
      by_cases h : step x r ∈ finSet n
      · rw [if_pos h, add_zero]
        exact fin_stage hn hΛ hΛn T _ h
      · rw [if_neg h]
        have h1 := missP_le_one (allA n) T (step x r)
        have h2 : 0 ≤ (5 / 6 : ℝ) ^ T * pot (step x r) :=
          mul_nonneg (by positivity) (pot_nonneg _)
        have h3 : (0 : ℝ) ≤ T * p := by positivity
        linarith
    have hround : avg (fun r : Fin n → Fin n => if step x r ∈ finSet n then (0 : ℝ) else 1)
        ≤ p := fin_round hn hΛ hΛn x hx
    have hexp := avg_pot_step hn x hx
    rw [missP_succ]
    calc avg (fun r => missP (allA n) T (step x r))
        ≤ avg (fun r => (5 / 6) ^ T * pot (step x r) + T * p
            + (if step x r ∈ finSet n then (0 : ℝ) else 1)) := avg_le_avg hpt
      _ = (5 / 6) ^ T * avg (fun r : Fin n → Fin n => pot (step x r)) + T * p
            + avg (fun r : Fin n → Fin n => if step x r ∈ finSet n then (0 : ℝ) else 1) := by
          rw [avg_add, avg_add, avg_const_mul, avg_const]
      _ ≤ (5 / 6) ^ T * (5 / 6 * pot x) + T * p + p := by
          have : (5 / 6 : ℝ) ^ T * avg (fun r : Fin n → Fin n => pot (step x r))
              ≤ (5 / 6) ^ T * (5 / 6 * pot x) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
          linarith
      _ = (5 / 6) ^ (T + 1) * pot x + ((T + 1 : ℕ) : ℝ) * p := by
          push_cast
          ring

end Undecided
