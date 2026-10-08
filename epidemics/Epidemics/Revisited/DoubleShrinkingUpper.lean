import Epidemics.Revisited.DoubleShrinkingStages

/-! # Theorem 43, upper bound (EPI-8, proof)

The three stages of `DoubleShrinkingStages` are composed by the Markov property at fixed times
(`notYet_add_le`), splitting the extra rounds `r` into thirds. The failure probabilities per
phase are polynomially small in `n`, which gives the paper's tail `O(n^{A' - α' r})`; the
number of double exponential phases is `J = ⌊log_ℓ (β ln n / (2 D₀))⌋ ≤ log_ℓ ln n`, and the
factor `2^J` of the phase calculus is a power of `n`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-! ### Real powers of `n` -/

lemma inv_n_eq : 1 / (n : ℝ) = (n : ℝ) ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one, one_div]

/-- Failure probability of a geometric phase. -/
lemma q_geom_le (hn : 1 ≤ n) {m m' c α τ τ' : ℝ} (hm : 0 < m) (hm' : 0 < m') (hc : 0 ≤ c)
    (hα : 0 ≤ α) (hτ' : τ' ≤ τ) (hτ'1 : τ' ≤ 1)
    (hB : (1 + c) / m ^ 2 + 1 / m' ≤ (n : ℝ) ^ (τ' / 2)) :
    (1 + c) * n / (m * n) ^ 2 + (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (m' * n) ≤
      (n : ℝ) ^ (-(τ' / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (1 + c) * n / (m * n) ^ 2 = (1 + c) / m ^ 2 * (1 / n) := by
    field_simp
  have e2 : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (m' * n) =
      1 / m' * (n : ℝ) ^ (-α - τ) := by
    have : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) = (n : ℝ) ^ (-α - τ) * n := by
      rw [← npow_add hn, ← Real.rpow_add_one hn0.ne']
      congr 1
      ring
    rw [this]
    field_simp
  have h1 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-τ') := by rw [inv_n_eq]; exact npow_mono hn (by linarith)
  have h2 : (n : ℝ) ^ (-α - τ) ≤ (n : ℝ) ^ (-τ') := npow_mono hn (by linarith)
  have hA : 0 ≤ (1 + c) / m ^ 2 := by positivity
  have hA' : 0 ≤ 1 / m' := by positivity
  have hsplit : (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') = (n : ℝ) ^ (-(τ' / 2)) := by
    rw [← npow_add hn]; congr 1; ring
  rw [e1, e2]
  calc (1 + c) / m ^ 2 * (1 / n) + 1 / m' * (n : ℝ) ^ (-α - τ)
      ≤ (1 + c) / m ^ 2 * (n : ℝ) ^ (-τ') + 1 / m' * (n : ℝ) ^ (-τ') := by
        gcongr
    _ = ((1 + c) / m ^ 2 + 1 / m') * (n : ℝ) ^ (-τ') := by ring
    _ ≤ (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') :=
        mul_le_mul_of_nonneg_right hB (npow_pos hn _).le
    _ = (n : ℝ) ^ (-(τ' / 2)) := hsplit

/-- Failure probability of a double exponential phase, when `ε ≥ n^{-β}`. -/
lemma q_double_le (hn : 1 ≤ n) {ε c α τ τ' β : ℝ} (hε : (n : ℝ) ^ (-β) ≤ ε) (hc : 0 ≤ c)
    (hβα : β ≤ α) (hβ : β ≤ 1 / 4) (hτ' : τ' ≤ τ) (hτ'1 : τ' ≤ 1 / 2)
    (hB : 4 * (1 + c) + 1 ≤ (n : ℝ) ^ (τ' / 2)) :
    (1 + c) * n / (ε * n / 2) ^ 2 + (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (ε * n) ≤
      (n : ℝ) ^ (-(τ' / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβpos : 0 < (n : ℝ) ^ (-β) := npow_pos hn _
  have hεpos : 0 < ε := lt_of_lt_of_le hβpos hε
  have e1 : (1 + c) * n / (ε * n / 2) ^ 2 = 4 * (1 + c) * (1 / n) / ε ^ 2 := by
    field_simp
    ring
  have e2 : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (ε * n) = (n : ℝ) ^ (-α - τ) / ε := by
    have : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) = (n : ℝ) ^ (-α - τ) * n := by
      rw [← npow_add hn, ← Real.rpow_add_one hn0.ne']
      congr 1
      ring
    rw [this]
    field_simp
  have hsq : (n : ℝ) ^ (-(2 * β)) ≤ ε ^ 2 := by
    have := pow_le_pow_left₀ hβpos.le hε 2
    rwa [npow_pow, show -β * ((2 : ℕ) : ℝ) = -(2 * β) by push_cast; ring] at this
  have h1 : 4 * (1 + c) * (1 / n) / ε ^ 2 ≤ 4 * (1 + c) * (n : ℝ) ^ (-τ') := by
    rw [div_le_iff₀ (by positivity), inv_n_eq]
    have : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-τ') * (n : ℝ) ^ (-(2 * β)) := by
      rw [← npow_add hn]; exact npow_mono hn (by linarith)
    have hm := mul_le_mul_of_nonneg_left hsq (npow_pos hn (-τ')).le
    nlinarith [npow_pos hn (-τ')]
  have h2 : (n : ℝ) ^ (-α - τ) / ε ≤ (n : ℝ) ^ (-τ') := by
    rw [div_le_iff₀ hεpos]
    have : (n : ℝ) ^ (-α - τ) ≤ (n : ℝ) ^ (-τ') * (n : ℝ) ^ (-β) := by
      rw [← npow_add hn]; exact npow_mono hn (by linarith)
    have hm := mul_le_mul_of_nonneg_left hε (npow_pos hn (-τ')).le
    linarith
  have hsplit : (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') = (n : ℝ) ^ (-(τ' / 2)) := by
    rw [← npow_add hn]; congr 1; ring
  rw [e1, e2]
  calc 4 * (1 + c) * (1 / n) / ε ^ 2 + (n : ℝ) ^ (-α - τ) / ε
      ≤ 4 * (1 + c) * (n : ℝ) ^ (-τ') + (n : ℝ) ^ (-τ') := add_le_add h1 h2
    _ = (4 * (1 + c) + 1) * (n : ℝ) ^ (-τ') := by ring
    _ ≤ (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') :=
        mul_le_mul_of_nonneg_right hB (npow_pos hn _).le
    _ = (n : ℝ) ^ (-(τ' / 2)) := hsplit

lemma npow_eq_exp (hn : 1 ≤ n) (x : ℝ) : (n : ℝ) ^ x = Real.exp (Real.log n * x) :=
  Real.rpow_def_of_pos (by exact_mod_cast hn) x

/-- The number of double exponential phases, `J = ⌊log_ℓ (β ln n / (2 D₀))⌋`: the last target
`ε_J` lies between `n^{-β}` and `n^{-β/(2ℓ)}`, and `J ≤ log_ℓ ln n`. -/
lemma J_facts {ℓ κ D₀ β : ℝ} (hℓ : 1 < ℓ) (hκ : 0 ≤ κ) (hD₀ : 0 < D₀) (hβ0 : 0 < β)
    (hβD : β / (2 * D₀) ≤ 1) (hn : 1 ≤ n) (hlog : 2 * D₀ / β + 2 * κ / β ≤ Real.log n)
    (J : ℕ) (hJ : J = ⌊Real.logb ℓ (β * Real.log n / (2 * D₀))⌋₊) :
    (n : ℝ) ^ (-β) ≤ epsSeq ℓ κ D₀ J ∧ epsSeq ℓ κ D₀ J ≤ (n : ℝ) ^ (-(β / (2 * ℓ))) ∧
      (J : ℝ) ≤ Real.logb ℓ (Real.log n) ∧ (J : ℝ) * Real.log ℓ ≤ Real.log n := by
  set L := Real.log n with hL
  set X := β * L / (2 * D₀) with hX
  have hℓ0 : 0 < ℓ := by linarith
  have h2D : 0 < 2 * D₀ := by linarith
  have hDβ : 0 ≤ 2 * D₀ / β := by positivity
  have hκβ : 0 ≤ 2 * κ / β := by positivity
  have hL1 : 2 * D₀ / β ≤ L := by linarith
  have hX1 : 1 ≤ X := by
    rw [hX, le_div_iff₀ h2D]
    have := (div_le_iff₀ hβ0).mp hL1
    linarith
  have hX0 : 0 < X := by linarith
  have hlogbX0 : 0 ≤ Real.logb ℓ X := Real.logb_nonneg hℓ hX1
  have hJle : (J : ℝ) ≤ Real.logb ℓ X := by rw [hJ]; exact Nat.floor_le hlogbX0
  have hJlt : Real.logb ℓ X < (J : ℝ) + 1 := by rw [hJ]; exact Nat.lt_floor_add_one _
  have hℓJ : ℓ ^ J ≤ X := by
    rw [← Real.rpow_natCast]
    calc ℓ ^ (J : ℝ) ≤ ℓ ^ (Real.logb ℓ X) := Real.rpow_le_rpow_of_exponent_le hℓ.le hJle
      _ = X := Real.rpow_logb hℓ0 hℓ.ne' hX0
  have hℓJ1 : X < ℓ * ℓ ^ J := by
    rw [← pow_succ', ← Real.rpow_natCast]
    calc X = ℓ ^ (Real.logb ℓ X) := (Real.rpow_logb hℓ0 hℓ.ne' hX0).symm
      _ < ℓ ^ (((J + 1 : ℕ) : ℝ)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hℓ
        push_cast
        exact hJlt
  have hXD : X * D₀ = β * L / 2 := by rw [hX]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [npow_eq_exp hn]
    unfold epsSeq
    apply Real.exp_le_exp.mpr
    have h1 : ℓ ^ J * D₀ ≤ X * D₀ := mul_le_mul_of_nonneg_right hℓJ hD₀.le
    have h2 : κ ≤ β * L / 2 := by
      have := (div_le_iff₀ hβ0).mp (show 2 * κ / β ≤ L by linarith)
      linarith
    rw [← hL]
    linarith
  · rw [npow_eq_exp hn]
    unfold epsSeq
    apply Real.exp_le_exp.mpr
    have h1 : X * D₀ < ℓ * ℓ ^ J * D₀ := mul_lt_mul_of_pos_right hℓJ1 hD₀
    have h2 : β * L / (2 * ℓ) ≤ ℓ ^ J * D₀ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [← hL]
    have : L * -(β / (2 * ℓ)) = -(β * L / (2 * ℓ)) := by ring
    rw [this]
    linarith
  · have hXL : X ≤ L := by
      rw [hX]
      have hL0 : 0 ≤ L := by linarith
      have : β * L / (2 * D₀) = β / (2 * D₀) * L := by ring
      rw [this]
      nlinarith
    exact le_trans hJle (Real.logb_le_logb_of_le hℓ hX0 hXL)
  · have hXL : X ≤ L := by
      rw [hX]
      have hL0 : 0 ≤ L := by linarith
      have : β * L / (2 * D₀) = β / (2 * D₀) * L := by ring
      rw [this]
      nlinarith
    have hJ' : (J : ℝ) ≤ Real.logb ℓ L := le_trans hJle (Real.logb_le_logb_of_le hℓ hX0 hXL)
    have hlogℓ : 0 < Real.log ℓ := Real.log_pos hℓ
    rw [Real.logb, le_div_iff₀ hlogℓ] at hJ'
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < L)
    linarith

/-- Three stages in sequence, the extra rounds `r` split into thirds. -/
lemma notYet_three_le (P : RumorProcess n) {m₁ m₂ : ℝ} (K J : ℕ) (F₁ F₂ F₃ : ℕ → ℝ)
    (hF₂ : ∀ s, 0 ≤ F₂ s) (hF₃ : ∀ s, 0 ≤ F₃ s) (S : Finset (Fin n))
    (h1 : ∀ s, P.notYet m₁ (K + s) S ≤ F₁ s)
    (h2 : ∀ T : Finset (Fin n), m₁ ≤ (T.card : ℝ) → ∀ s, P.notYet m₂ (J + s) T ≤ F₂ s)
    (h3 : ∀ T : Finset (Fin n), m₂ ≤ (T.card : ℝ) → ∀ s, P.notYet n s T ≤ F₃ s) (r : ℕ) :
    P.notYet n (K + J + r) S ≤ F₁ (r / 3) + F₂ (r / 3) + F₃ (r - 2 * (r / 3)) := by
  have htime : K + J + r = (K + r / 3) + ((J + r / 3) + (r - 2 * (r / 3))) := by omega
  have hB : ∀ T : Finset (Fin n), m₁ ≤ (T.card : ℝ) →
      P.notYet n ((J + r / 3) + (r - 2 * (r / 3))) T ≤ F₂ (r / 3) + F₃ (r - 2 * (r / 3)) := by
    intro T hT
    have := notYet_add_le P (hF₃ _) (J + r / 3) (r - 2 * (r / 3))
      (fun U hU => h3 U hU (r - 2 * (r / 3))) T
    linarith [h2 T hT (r / 3)]
  have := notYet_add_le P (add_nonneg (hF₂ _) (hF₃ _)) (K + r / 3)
    ((J + r / 3) + (r - 2 * (r / 3))) hB S
  rw [htime]
  linarith [h1 (r / 3)]

/-- The exponent bookkeeping of the three stages. -/
lemma three_terms_le (hn : 1 ≤ n) {K : ℕ} {A₂ ω δ τ₃ : ℝ} (hω : 0 < ω) (hωδ : ω ≤ δ / 2)
    (hωτ : ω ≤ τ₃) {J : ℕ} (hJ : (2 : ℝ) ^ J ≤ (n : ℝ) ^ A₂) (r : ℕ) :
    2 ^ K * (n : ℝ) ^ (-(δ / 2) * ((r / 3 : ℕ) : ℝ)) +
        2 ^ J * (n : ℝ) ^ (-(δ / 2) * ((r / 3 : ℕ) : ℝ)) +
        ((n : ℝ) ^ (-τ₃)) ^ (r - 2 * (r / 3)) * n ≤
      (2 ^ K + 2) * (n : ℝ) ^ (max A₂ 1 + 2 * ω / 3 - ω / 3 * r) := by
  set E := (n : ℝ) ^ (max A₂ 1 + 2 * ω / 3 - ω / 3 * r) with hE
  have hr1 : (r : ℝ) - 2 ≤ 3 * ((r / 3 : ℕ) : ℝ) := by
    have : r ≤ 3 * (r / 3) + 2 := by omega
    have : (r : ℝ) ≤ 3 * ((r / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast this
    linarith
  have hr3 : (r : ℝ) - 2 ≤ 3 * ((r - 2 * (r / 3) : ℕ) : ℝ) := by
    have : r ≤ 3 * (r - 2 * (r / 3)) + 2 := by omega
    have : (r : ℝ) ≤ 3 * ((r - 2 * (r / 3) : ℕ) : ℝ) + 2 := by exact_mod_cast this
    linarith
  have hs0 : (0 : ℝ) ≤ ((r / 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs30 : (0 : ℝ) ≤ ((r - 2 * (r / 3) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmax : 1 ≤ max A₂ 1 := le_max_right _ _
  have hmaxA : A₂ ≤ max A₂ 1 := le_max_left _ _
  -- the three exponents
  have e1 : (n : ℝ) ^ (-(δ / 2) * ((r / 3 : ℕ) : ℝ)) ≤ E := by
    apply npow_mono hn
    nlinarith
  have e2 : 2 ^ J * (n : ℝ) ^ (-(δ / 2) * ((r / 3 : ℕ) : ℝ)) ≤ E := by
    calc 2 ^ J * (n : ℝ) ^ (-(δ / 2) * ((r / 3 : ℕ) : ℝ))
        ≤ (n : ℝ) ^ A₂ * (n : ℝ) ^ (-(δ / 2) * ((r / 3 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hJ (npow_pos hn _).le
      _ = (n : ℝ) ^ (A₂ + -(δ / 2) * ((r / 3 : ℕ) : ℝ)) := (npow_add hn _ _).symm
      _ ≤ E := by apply npow_mono hn; nlinarith
  have e3 : ((n : ℝ) ^ (-τ₃)) ^ (r - 2 * (r / 3)) * n ≤ E := by
    rw [npow_pow]
    calc (n : ℝ) ^ (-τ₃ * ((r - 2 * (r / 3) : ℕ) : ℝ)) * n
        = (n : ℝ) ^ (-τ₃ * ((r - 2 * (r / 3) : ℕ) : ℝ) + 1) :=
          (Real.rpow_add_one (by have : (0 : ℝ) < n := by exact_mod_cast hn
                                 exact this.ne') _).symm
      _ ≤ E := by apply npow_mono hn; nlinarith
  have hE0 : 0 ≤ E := (npow_pos hn _).le
  have hK0 : (0 : ℝ) ≤ 2 ^ K := by positivity
  have := mul_le_mul_of_nonneg_left e1 hK0
  nlinarith

/-- Theorem 43 for one value of `n`, given the constants of the three stages: after
`K + J + r` rounds, with `J ≤ ⌈log_ℓ ln n⌉`, the tail is at most
`(2^K + 2) n^{max A₂ 1 + 2ω/3 - (ω/3) r}`. -/
lemma double_shrinking_tail_core (P : RumorProcess n)
    {ℓ a c g α τ lam μ a₁ κ D₀ β τ' δ σ τ₃ ω A₂ : ℝ} (K : ℕ)
    (hℓ : 1 < ℓ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hg : 0 < g) (hα : 0 < α)
    (hlam : lam = a * g ^ (ℓ - 1)) (hlamμ : lam < μ) (hμ1 : μ < 1) (hμ0 : 0 < μ)
    (haa₁ : a ≤ a₁) (ha₁0 : 0 < a₁) (hκ0 : 0 ≤ κ) (hκeq : Real.log (2 * a₁) = κ * (ℓ - 1))
    (hD₀1 : 1 ≤ D₀) (hε0g : epsSeq ℓ κ D₀ 0 ≤ g) (hgK : g * μ ^ K ≤ epsSeq ℓ κ D₀ 0)
    (hβ0 : 0 < β) (hβα : β ≤ α) (hβ4 : β ≤ 1 / 4)
    (hτ'τ : τ' ≤ τ) (hτ'2 : τ' ≤ 1 / 2) (hδ0 : 0 < δ) (h2δ : -(2 * δ) = -(τ' / 2))
    (hσ : σ = β * (ℓ - 1) / (4 * ℓ)) (hτ₃τ : τ₃ ≤ τ) (hτ₃σ : τ₃ ≤ σ)
    (hω0 : 0 < ω) (hωδ : ω ≤ δ / 2) (hωτ : ω ≤ τ₃) (hA₂ : A₂ = Real.log 2 / Real.log ℓ)
    (hn1 : 1 ≤ n) (h2 : 2 ≤ (n : ℝ) ^ (δ / 2))
    (hB1 : (1 + c) / (g * μ ^ K * (μ - lam)) ^ 2 + 1 / (g * μ ^ K) ≤ (n : ℝ) ^ (τ' / 2))
    (hB2 : 4 * (1 + c) + 1 ≤ (n : ℝ) ^ (τ' / 2))
    (hlog : 2 * D₀ / β + 2 * κ / β ≤ Real.log n) (ha₁n : a₁ ≤ (n : ℝ) ^ σ)
    (hDES : P.UpperDoubleShrinking ℓ a c g α) (hFF : P.FastFinishing α τ)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g * n) :
    ∃ J : ℕ, J ≤ ⌈Real.logb ℓ (Real.log n)⌉₊ ∧ ∀ r' : ℕ, P.notYet n (K + J + r') S ≤
      (2 ^ K + 2) * (n : ℝ) ^ (max A₂ 1 + 2 * ω / 3 - ω / 3 * r') := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hℓ1 : 0 < ℓ - 1 := by linarith
  have hlogℓ : 0 < Real.log ℓ := Real.log_pos hℓ
  have hm : 0 < g * μ ^ K * (μ - lam) := by
    have := pow_pos hμ0 K; have : 0 < μ - lam := by linarith
    positivity
  have hm' : 0 < g * μ ^ K := by have := pow_pos hμ0 K; positivity
  -- the number of double exponential phases
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌊Real.logb ℓ (β * Real.log n / (2 * D₀))⌋₊ := ⟨_, rfl⟩
  have hβD : β / (2 * D₀) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  obtain ⟨hεJlo, hεJhi, hJlog, hJlogℓ⟩ :=
    J_facts hℓ hκ0 (by linarith) hβ0 hβD hn1 hlog J hJ
  -- stage 1
  have hq1 := q_geom_le hn1 hm hm' hc hα.le hτ'τ (by linarith) hB1 (α := α)
  rw [← h2δ] at hq1
  have hst1 := stage_geom P K hℓ ha hc hg hlam.ge hlamμ hμ1.le hδ0 hn1 h2 hq1 hDES hFF
  -- stage 2
  have hq2 := q_double_le hn1 hεJlo hc hβα hβ4 hτ'τ hτ'2 hB2 (α := α)
  rw [← h2δ] at hq2
  have hst2 := stage_double P J hℓ haa₁ ha₁0 hc hκeq (by linarith) hε0g hδ0 hn1 h2 hq2
    hDES hFF
  -- stage 3
  have hεJg : epsSeq ℓ κ D₀ J ≤ g :=
    le_trans (epsSeq_anti hℓ.le (by linarith) (Nat.zero_le J)) hε0g
  have hεJpos := epsSeq_pos ℓ κ D₀ J
  have hθd : ∀ u : ℝ, 0 ≤ u → u ≤ epsSeq ℓ κ D₀ J * n →
      a * (u / n) ^ (ℓ - 1) ≤ (n : ℝ) ^ (-τ₃) := by
    intro u hu0 huU
    have hfrac : u / n ≤ (n : ℝ) ^ (-(β / (2 * ℓ))) := by
      rw [div_le_iff₀ hn0]
      exact le_trans huU (mul_le_mul_of_nonneg_right hεJhi hn0.le)
    have hp := Real.rpow_le_rpow (div_nonneg hu0 hn0.le) hfrac hℓ1.le
    rw [← Real.rpow_mul (Nat.cast_nonneg n)] at hp
    have hprod : a * (u / n) ^ (ℓ - 1) ≤
        (n : ℝ) ^ σ * (n : ℝ) ^ (-(β / (2 * ℓ)) * (ℓ - 1)) :=
      mul_le_mul (le_trans haa₁ ha₁n) hp (Real.rpow_nonneg (div_nonneg hu0 hn0.le) _)
        (npow_pos hn1 _).le
    rw [← npow_add hn1] at hprod
    refine le_trans hprod (npow_mono hn1 ?_)
    have hℓ0 : 0 < ℓ := by linarith
    have : σ + -(β / (2 * ℓ)) * (ℓ - 1) = -σ := by rw [hσ]; field_simp; ring
    rw [this]
    linarith
  have hst3 := stage_finish P (U := epsSeq ℓ κ D₀ J * n) (θ := (n : ℝ) ^ (-τ₃))
    (mul_le_mul_of_nonneg_right hεJg hn0.le) (npow_pos hn1 _).le hθd
    (npow_mono hn1 (by linarith)) hDES hFF
  -- composition
  have h2J : (2 : ℝ) ^ J ≤ (n : ℝ) ^ A₂ := by
    rw [npow_eq_exp hn1, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    rw [hA₂]
    have : Real.log 2 * (J : ℝ) = (J * Real.log ℓ) * (Real.log 2 / Real.log ℓ) := by
      field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hJlogℓ (by positivity : 0 ≤ Real.log 2 / Real.log ℓ)
    linarith
  have hmain : ∀ r' : ℕ, P.notYet n (K + J + r') S ≤
      (2 ^ K + 2) * (n : ℝ) ^ (max A₂ 1 + 2 * ω / 3 - ω / 3 * r') := by
    intro r'
    have hc3 := notYet_three_le P (m₁ := (n : ℝ) - g * μ ^ K * n)
      (m₂ := (n : ℝ) - epsSeq ℓ κ D₀ J * n) K J
      (fun s => 2 ^ K * (n : ℝ) ^ (-(δ / 2) * s)) (fun s => 2 ^ J * (n : ℝ) ^ (-(δ / 2) * s))
      (fun s => ((n : ℝ) ^ (-τ₃)) ^ s * n)
      (fun s => mul_nonneg (by positivity) (npow_pos hn1 _).le)
      (fun s => mul_nonneg (pow_nonneg (npow_pos hn1 _).le _) hn0.le) S
      (fun s => hst1 S hS s)
      (fun T hT s => hst2 T (by
        have h' := mul_le_mul_of_nonneg_right hgK hn0.le
        linarith only [hT, h']) s)
      (fun T hT s => hst3 T (by linarith only [hT]) s) r'
    exact le_trans hc3 (three_terms_le hn1 hω0 hωδ hωτ h2J r')
  have hJceil : J ≤ ⌈Real.logb ℓ (Real.log n)⌉₊ := by
    have := le_trans hJlog (Nat.le_ceil _)
    exact_mod_cast this
  exact ⟨J, hJceil, hmain⟩

/-- Theorem 43, tail, in the main case `g > 0`, `α > 0`. -/
theorem double_shrinking_tail_main {ℓ a c g α τ : ℝ} (hℓ : 1 < ℓ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hg : 0 < g) (hα : 0 < α) (hag : a * g ^ (ℓ - 1) < 1) (hτ : 0 < τ) :
    ∃ C A' α' : ℝ, 1 ≤ C ∧ 0 ≤ A' ∧ 0 < α' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ P : RumorProcess n, P.UpperDoubleShrinking ℓ a c g α → P.FastFinishing α τ →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ r : ℕ,
        P.notYet n (⌈Real.logb ℓ (Real.log n)⌉₊ + r) S ≤ C * (n : ℝ) ^ (A' - α' * r) := by
  -- constants of the geometric stage
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = a * g ^ (ℓ - 1) := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (1 + lam) / 2 := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact mul_nonneg ha (Real.rpow_nonneg hg.le _)
  have hlam1 : lam < 1 := by rw [hlam]; exact hag
  have hlamμ : lam < μ := by rw [hμ]; linarith
  have hμ1 : μ < 1 := by rw [hμ]; linarith
  have hμ0 : 0 < μ := by linarith
  -- constants of the double exponential stage
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℝ, a₁ = max a 1 := ⟨_, rfl⟩
  have haa₁ : a ≤ a₁ := by rw [ha₁]; exact le_max_left _ _
  have h1a₁ : 1 ≤ a₁ := by rw [ha₁]; exact le_max_right _ _
  have ha₁0 : 0 < a₁ := by linarith
  have hℓ1 : 0 < ℓ - 1 := by linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Real.log (2 * a₁) / (ℓ - 1) := ⟨_, rfl⟩
  have hlog2a : 0 < Real.log (2 * a₁) := Real.log_pos (by linarith)
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hκeq : Real.log (2 * a₁) = κ * (ℓ - 1) := by rw [hκ]; field_simp
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ℝ, g₀ = min g (Real.exp (-(κ + 1))) := ⟨_, rfl⟩
  have hg₀pos : 0 < g₀ := by rw [hg₀]; exact lt_min hg (Real.exp_pos _)
  have hg₀g : g₀ ≤ g := by rw [hg₀]; exact min_le_left _ _
  have hg₀e : g₀ ≤ Real.exp (-(κ + 1)) := by rw [hg₀]; exact min_le_right _ _
  obtain ⟨D₀, hD₀⟩ : ∃ D₀ : ℝ, D₀ = -Real.log g₀ - κ := ⟨_, rfl⟩
  have hD₀1 : 1 ≤ D₀ := by
    have := Real.log_le_log hg₀pos hg₀e
    rw [Real.log_exp] at this
    rw [hD₀]; linarith
  have hε0 : epsSeq ℓ κ D₀ 0 = g₀ := by
    unfold epsSeq
    rw [pow_zero, one_mul, hD₀, show -(κ + (-Real.log g₀ - κ)) = Real.log g₀ by ring,
      Real.exp_log hg₀pos]
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hg₀pos hg) hμ1
  have hgK : g * μ ^ K ≤ g₀ := by
    have := (lt_div_iff₀ hg).mp hK
    linarith
  -- exponents
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = min α (1 / 4) := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; exact lt_min hα (by norm_num)
  have hβα : β ≤ α := by rw [hβ]; exact min_le_left _ _
  have hβ4 : β ≤ 1 / 4 := by rw [hβ]; exact min_le_right _ _
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ℝ, τ' = min τ (1 / 2) := ⟨_, rfl⟩
  have hτ'0 : 0 < τ' := by rw [hτ']; exact lt_min hτ (by norm_num)
  have hτ'τ : τ' ≤ τ := by rw [hτ']; exact min_le_left _ _
  have hτ'2 : τ' ≤ 1 / 2 := by rw [hτ']; exact min_le_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = τ' / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h2δ : -(2 * δ) = -(τ' / 2) := by rw [hδ]; ring
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = β * (ℓ - 1) / (4 * ℓ) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; exact div_pos (mul_pos hβ0 hℓ1) (by linarith)
  obtain ⟨τ₃, hτ₃⟩ : ∃ τ₃ : ℝ, τ₃ = min τ σ := ⟨_, rfl⟩
  have hτ₃0 : 0 < τ₃ := by rw [hτ₃]; exact lt_min hτ hσ0
  have hτ₃τ : τ₃ ≤ τ := by rw [hτ₃]; exact min_le_left _ _
  have hτ₃σ : τ₃ ≤ σ := by rw [hτ₃]; exact min_le_right _ _
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = min (δ / 2) τ₃ := ⟨_, rfl⟩
  have hω0 : 0 < ω := by rw [hω]; exact lt_min (by linarith) hτ₃0
  have hωδ : ω ≤ δ / 2 := by rw [hω]; exact min_le_left _ _
  have hωτ : ω ≤ τ₃ := by rw [hω]; exact min_le_right _ _
  obtain ⟨A₂, hA₂⟩ : ∃ A₂ : ℝ, A₂ = Real.log 2 / Real.log ℓ := ⟨_, rfl⟩
  have hlogℓ : 0 < Real.log ℓ := Real.log_pos hℓ
  -- thresholds on `n`
  have hm : 0 < g * μ ^ K * (μ - lam) := by
    have := pow_pos hμ0 K; have : 0 < μ - lam := by linarith
    positivity
  have hm' : 0 < g * μ ^ K := by have := pow_pos hμ0 K; positivity
  obtain ⟨N1, hN1⟩ := exists_le_npow 2 (by linarith : 0 < δ / 2)
  obtain ⟨N2, hN2⟩ := exists_le_npow ((1 + c) / (g * μ ^ K * (μ - lam)) ^ 2 + 1 / (g * μ ^ K))
    (by linarith : 0 < τ' / 2)
  obtain ⟨N3, hN3⟩ := exists_le_npow (4 * (1 + c) + 1) (by linarith : 0 < τ' / 2)
  obtain ⟨N4, hN4⟩ := exists_le_log (2 * D₀ / β + 2 * κ / β)
  obtain ⟨N5, hN5⟩ := exists_le_npow a₁ (by linarith : 0 < σ)
  have h2K : (0 : ℝ) < 2 ^ K := pow_pos (by norm_num) K
  have hA'0 : 0 ≤ max A₂ 1 + 2 * ω / 3 + ω / 3 * K := by
    have := le_max_right A₂ 1
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  refine ⟨2 ^ K + 2, max A₂ 1 + 2 * ω / 3 + ω / 3 * K, ω / 3, by linarith, hA'0, by linarith,
    max (max (max N1 N2) (max N3 N4)) (max N5 1), ?_⟩
  intro n hn P hDES hFF S hS r
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hn
  have hnN3 : N3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hn
  have hnN4 : N4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hn
  have hnN5 : N5 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h2 := hN1 n hnN1
  obtain ⟨J, hJceil, hmain⟩ := double_shrinking_tail_core P K hℓ ha hc hg hα hlam hlamμ hμ1 hμ0
    haa₁ ha₁0 hκ0 hκeq hD₀1 (hε0 ▸ hg₀g) (hε0 ▸ hgK) hβ0 hβα hβ4 hτ'τ hτ'2 hδ0 h2δ hσ hτ₃τ
    hτ₃σ hω0 hωδ hωτ hA₂ hn1 h2 (hN2 n hnN2) (hN3 n hnN3) (hN4 n hnN4) (hN5 n hnN5) hDES hFF S hS
  -- the time `⌈log_ℓ ln n⌉ + r`
  have hC1 : (1 : ℝ) ≤ 2 ^ K + 2 := by linarith only [h2K]
  by_cases hrK : K ≤ r
  · have htime : K + J + (r - K) ≤ ⌈Real.logb ℓ (Real.log n)⌉₊ + r := by omega
    have := le_trans (notYet_antitone P n htime S) (hmain (r - K))
    refine le_trans this (le_of_eq ?_)
    congr 2
    rw [Nat.cast_sub hrK]
    ring
  · rw [not_le] at hrK
    have hexp : 0 ≤ max A₂ 1 + 2 * ω / 3 + ω / 3 * K - ω / 3 * r := by
      have h1 : (r : ℝ) < K := by exact_mod_cast hrK
      have h2 := le_max_right A₂ 1
      have h3 : ω / 3 * (r : ℝ) ≤ ω / 3 * K :=
        mul_le_mul_of_nonneg_left h1.le (by linarith only [hω0])
      linarith only [h2, h3, hω0]
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ (max A₂ 1 + 2 * ω / 3 + ω / 3 * K - ω / 3 * r) :=
      Real.one_le_rpow (by exact_mod_cast hn1) hexp
    have h1 := notYet_le_one P n (⌈Real.logb ℓ (Real.log n)⌉₊ + r) S
    have h2 : (1 : ℝ) * 1 ≤ (2 ^ K + 2) *
        (n : ℝ) ^ (max A₂ 1 + 2 * ω / 3 + ω / 3 * K - ω / 3 * r) :=
      mul_le_mul hC1 hone zero_le_one (by linarith only [hC1])
    rw [one_mul] at h2
    exact le_trans h1 h2

end Epidemics.Revisited
