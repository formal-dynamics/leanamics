import Averaging.OpportunisticModel

/-! # Sums of independent uniform signs

Elementary facts about `S = ∑ i, σ i` for a uniform sign vector `σ : I → ℤˣ`: the law of `S` is
the binomial pushforward `k ↦ m - 2 k` (`avg_fun_sum_signVec`), every binomial weight is at most
`1 / √(m + 1)` (`choose_div_le`), hence anti-concentration bounds, the second moment of weighted
sums, the symmetry `S ↦ -S`, and the independence of disjoint blocks of signs (`avg_split`).
-/

namespace Averaging.Opportunistic
open Finset Dynamics

/-! ### Binomial bounds -/

/-- Central binomial bound, even case: `centralBinom j ^ 2 * (2 j + 1) ≤ 16 ^ j`. -/
theorem centralBinom_sq_mul_le (j : ℕ) : j.centralBinom ^ 2 * (2 * j + 1) ≤ 16 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.succ_mul_centralBinom_succ j
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (j + 1) ^ 2 by positivity)
    calc (j + 1) ^ 2 * ((j + 1).centralBinom ^ 2 * (2 * (j + 1) + 1))
        = ((j + 1) * (j + 1).centralBinom) ^ 2 * (2 * j + 3) := by ring
      _ = 4 * (2 * j + 1) * (2 * j + 3) * (j.centralBinom ^ 2 * (2 * j + 1)) := by
          rw [h]; ring
      _ ≤ 4 * (2 * j + 1) * (2 * j + 3) * 16 ^ j := Nat.mul_le_mul_left _ ih
      _ ≤ 4 * (4 * (j + 1) ^ 2) * 16 ^ j := Nat.mul_le_mul_right _ (by nlinarith)
      _ = (j + 1) ^ 2 * 16 ^ (j + 1) := by ring

/-- The odd middle binomial coefficient is half of the next central one. -/
theorem choose_odd_middle_mul_two (j : ℕ) : (2 * j + 1).choose j * 2 = (j + 1).centralBinom := by
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
    Nat.choose_succ_succ, Nat.choose_symm_half]
  ring

/-- Central binomial bound in `ℕ`: `choose m k ^ 2 * (m + 1) ≤ 4 ^ m`. -/
theorem choose_sq_mul_le_nat (m k : ℕ) : m.choose k ^ 2 * (m + 1) ≤ 4 ^ m := by
  calc m.choose k ^ 2 * (m + 1) ≤ m.choose (m / 2) ^ 2 * (m + 1) := by
        gcongr; exact Nat.choose_le_middle k m
    _ ≤ 4 ^ m := ?_
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show 2 * j / 2 = j by omega, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    exact centralBinom_sq_mul_le j
  · rw [show (2 * j + 1) / 2 = j by omega]
    have h2 := centralBinom_sq_mul_le (j + 1)
    rw [← choose_odd_middle_mul_two j] at h2
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 4 by norm_num)
    calc 4 * ((2 * j + 1).choose j ^ 2 * (2 * j + 1 + 1))
        ≤ 4 * ((2 * j + 1).choose j ^ 2 * (2 * j + 3)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = ((2 * j + 1).choose j * 2) ^ 2 * (2 * (j + 1) + 1) := by ring
      _ ≤ 16 ^ (j + 1) := h2
      _ = 4 * 4 ^ (2 * j + 1) := by
          rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]; ring

/-- (T1) Central binomial bound. -/
theorem choose_sq_mul_le (m k : ℕ) : ((m.choose k : ℝ)) ^ 2 * (m + 1) ≤ 4 ^ m := by
  exact_mod_cast choose_sq_mul_le_nat m k

/-- (T1') Each binomial weight is at most `1/√(m+1)`. -/
theorem choose_div_le (m k : ℕ) : (m.choose k : ℝ) / 2 ^ m ≤ 1 / Real.sqrt (m + 1) := by
  have hs : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ (by positivity) hs, one_mul]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm m 2, pow_mul]
  norm_num
  exact choose_sq_mul_le m k

/-! ### The law of the sum of the signs -/

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The indices carrying the sign `-1`. -/
def negSet (τ : I → ℤˣ) : Finset I := univ.filter fun i => τ i = -1

/-- Sign vectors correspond to the sets of their `-1` positions. -/
def signEquiv : (I → ℤˣ) ≃ Finset I where
  toFun := negSet
  invFun s i := if i ∈ s then -1 else 1
  left_inv τ := by
    funext i
    rcases Int.units_eq_one_or (τ i) with h | h <;> simp [negSet, h]
  right_inv s := by
    ext i
    by_cases h : i ∈ s <;> simp [negSet, h]

omit [Fintype I] [DecidableEq I] in
/-- Each sign is `1 - 2 [τ i = -1]`. -/
lemma signVec_eq_one_sub (τ : I → ℤˣ) (i : I) :
    signVec τ i = 1 - 2 * (if τ i = -1 then 1 else 0) := by
  rcases Int.units_eq_one_or (τ i) with h | h <;> norm_num [signVec, h]

omit [DecidableEq I] in
/-- The sum of the signs is `m - 2 #{i | τ i = -1}`. -/
lemma sum_signVec_eq (τ : I → ℤˣ) :
    ∑ i, signVec τ i = Fintype.card I - 2 * (#(negSet τ) : ℝ) := by
  simp_rw [signVec_eq_one_sub, sum_sub_distrib, ← mul_sum, sum_boole, negSet]
  simp

/-- (T0) The law of a sum of `m` independent uniform signs: binomial pushforward. -/
theorem avg_fun_sum_signVec (F : ℝ → ℝ) :
    avg (fun τ : I → ℤˣ => F (∑ i, signVec τ i)) =
      ∑ k ∈ range (Fintype.card I + 1),
        ((Fintype.card I).choose k : ℝ) / 2 ^ Fintype.card I * F (Fintype.card I - 2 * k) := by
  have hsum : ∑ τ : I → ℤˣ, F (∑ i, signVec τ i) = ∑ k ∈ range (Fintype.card I + 1),
      (Fintype.card I).choose k • F (Fintype.card I - 2 * k) := by
    simp_rw [sum_signVec_eq]
    rw [← card_univ (α := I), ← sum_powerset_apply_card, powerset_univ]
    exact Equiv.sum_comp signEquiv (fun s : Finset I => F (#(univ : Finset I) - 2 * #s))
  unfold avg
  rw [hsum, sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul, Fintype.card_fun, Fintype.card_units_int]
  push_cast
  ring

/-- The law of the sum against a nonnegative test function, with every binomial weight bounded
by `1 / √(m + 1)`. -/
theorem avg_fun_sum_signVec_le (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    avg (fun τ : I → ℤˣ => F (∑ i, signVec τ i)) ≤
      (∑ k ∈ range (Fintype.card I + 1), F (Fintype.card I - 2 * k)) /
        Real.sqrt (Fintype.card I + 1) := by
  rw [avg_fun_sum_signVec, sum_div]
  refine sum_le_sum fun k _ => ?_
  calc ((Fintype.card I).choose k : ℝ) / 2 ^ Fintype.card I * F (Fintype.card I - 2 * k)
      ≤ 1 / Real.sqrt (Fintype.card I + 1) * F (Fintype.card I - 2 * k) :=
        mul_le_mul_of_nonneg_right (choose_div_le _ _) (hF _)
    _ = F (Fintype.card I - 2 * k) / Real.sqrt (Fintype.card I + 1) := one_div_mul_eq_div _ _

/-- At most one `k` satisfies `m - 2 k = 0`. -/
lemma sum_range_ite_eq_zero_le (m : ℕ) :
    ∑ k ∈ range (m + 1), (if (m : ℝ) - 2 * k = 0 then (1 : ℝ) else 0) ≤ 1 := by
  rw [sum_boole]
  have h : #((range (m + 1)).filter fun k : ℕ => (m : ℝ) - 2 * k = 0) ≤ 1 :=
    card_le_one.mpr fun a ha b hb => by
      simp only [mem_filter] at ha hb
      exact_mod_cast (by linarith [ha.2, hb.2] : (a : ℝ) = b)
  exact_mod_cast h

/-- (T2a) Point mass at zero. -/
theorem avg_sum_signVec_eq_zero :
    avg (fun τ : I → ℤˣ => if ∑ i, signVec τ i = 0 then (1 : ℝ) else 0) ≤
      1 / Real.sqrt (Fintype.card I + 1) :=
  (avg_fun_sum_signVec_le (fun x => if x = 0 then (1 : ℝ) else 0)
    fun x => by split_ifs <;> norm_num).trans
      (div_le_div_of_nonneg_right (sum_range_ite_eq_zero_le _) (Real.sqrt_nonneg _))

/-- At most `r + 1` indices `k ≤ m` satisfy `|m - 2 k| ≤ r`. -/
lemma card_filter_abs_le (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (#((range (m + 1)).filter fun k : ℕ => |(m : ℝ) - 2 * k| ≤ r) : ℝ) ≤ r + 1 := by
  set s := (range (m + 1)).filter fun k : ℕ => |(m : ℝ) - 2 * k| ≤ r
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, card_empty, Nat.cast_zero]
    linarith
  have hsub : s ⊆ Icc (s.min' hs) (s.min' hs + ⌊r⌋₊) := by
    intro k hk
    have ha := s.min'_le k hk
    have hka : |(m : ℝ) - 2 * k| ≤ r := (mem_filter.mp hk).2
    have hma : |(m : ℝ) - 2 * (s.min' hs)| ≤ r := (mem_filter.mp (s.min'_mem hs)).2
    have hle : ((k - s.min' hs : ℕ) : ℝ) ≤ r := by
      rw [Nat.cast_sub ha]
      linarith [(abs_le.mp hka).1, (abs_le.mp hma).2]
    have := Nat.le_floor hle
    rw [mem_Icc]
    omega
  calc (#s : ℝ) ≤ #(Icc (s.min' hs) (s.min' hs + ⌊r⌋₊)) := by exact_mod_cast card_le_card hsub
    _ = ⌊r⌋₊ + 1 := by
        rw [Nat.card_Icc, show s.min' hs + ⌊r⌋₊ + 1 - s.min' hs = ⌊r⌋₊ + 1 by omega]
        push_cast; ring
    _ ≤ r + 1 := by linarith [Nat.floor_le hr]

/-- (T2b) Anti-concentration in an interval around zero. -/
theorem avg_abs_sum_signVec_le (r : ℝ) (hr : 0 ≤ r) :
    avg (fun τ : I → ℤˣ => if |∑ i, signVec τ i| ≤ r then (1 : ℝ) else 0) ≤
      (r + 1) / Real.sqrt (Fintype.card I + 1) := by
  refine (avg_fun_sum_signVec_le (fun x => if |x| ≤ r then (1 : ℝ) else 0)
    fun x => by split_ifs <;> norm_num).trans
      (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  rw [sum_boole]
  exact card_filter_abs_le _ r hr

/-- `|m - 2 k|` is the cast of the natural number `Int.natAbs (m - 2 k)`. -/
lemma abs_sub_two_mul_eq (m k : ℕ) :
    |(m : ℝ) - 2 * k| = (Int.natAbs ((m : ℤ) - 2 * k) : ℝ) := by
  rw [Nat.cast_natAbs]
  push_cast
  rfl

/-- Each value of `|m - 2 k|` is taken by at most two indices `k`. -/
lemma card_fiber_le_two (m j : ℕ) :
    #((range (m + 1)).filter fun k : ℕ => Int.natAbs ((m : ℤ) - 2 * k) = j) ≤ 2 := by
  calc _ ≤ #(univ : Finset Bool) :=
        card_le_card_of_injOn (fun k => decide (2 * k ≤ m))
          (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
    _ = 2 := rfl
  intro a ha b hb hab
  simp only [coe_filter, Set.mem_setOf_eq, decide_eq_decide] at ha hb hab
  omega

/-- The harmonic number `H_m` as `∑_{j ≤ m} j⁻¹` (the term `0⁻¹ = 0` is harmless). -/
lemma harmonic_eq_sum_range_succ (m : ℕ) :
    ((harmonic m : ℚ) : ℝ) = ∑ j ∈ range (m + 1), (j : ℝ)⁻¹ := by
  rw [sum_range_succ', harmonic]
  push_cast
  simp

/-- `∑_{k ≤ m} |m - 2 k|⁻¹ ≤ 2 H_m`. -/
lemma sum_inv_abs_le (m : ℕ) :
    ∑ k ∈ range (m + 1), |(m : ℝ) - 2 * k|⁻¹ ≤ 2 * ((harmonic m : ℚ) : ℝ) := by
  simp_rw [abs_sub_two_mul_eq]
  rw [← sum_fiberwise_of_maps_to (s := range (m + 1)) (t := range (m + 1))
    (g := fun k : ℕ => Int.natAbs ((m : ℤ) - 2 * k))
    fun k hk => by simp only [mem_range] at hk ⊢; omega,
    harmonic_eq_sum_range_succ, mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [sum_congr rfl (g := fun _ => (j : ℝ)⁻¹) fun k hk => by rw [(mem_filter.mp hk).2],
    sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_fiber_le_two m j) (by positivity)

/-- (T2c) The inverse absolute value of the sum, on the event that it is nonzero. -/
theorem avg_inv_abs_sum_signVec :
    avg (fun τ : I → ℤˣ => if ∑ i, signVec τ i = 0 then (0 : ℝ) else 1 / |∑ i, signVec τ i|) ≤
      2 * (1 + Real.log (Fintype.card I)) / Real.sqrt (Fintype.card I + 1) := by
  have h : ∀ x : ℝ, (if x = 0 then (0 : ℝ) else 1 / |x|) = |x|⁻¹ := fun x => by
    split_ifs with hx <;> simp [hx]
  simp_rw [h]
  refine (avg_fun_sum_signVec_le (fun x => |x|⁻¹) fun x => inv_nonneg.mpr (abs_nonneg x)).trans
    (div_le_div_of_nonneg_right ((sum_inv_abs_le _).trans ?_) (Real.sqrt_nonneg _))
  linarith [harmonic_le_one_add_log (Fintype.card I)]

/-! ### Second moment, symmetry, first moment -/

omit [Fintype I] [DecidableEq I] in
/-- The square of a sign is `1`. -/
lemma signVec_mul_self (τ : I → ℤˣ) (i : I) : signVec τ i * signVec τ i = 1 := by
  rcases Int.units_eq_one_or (τ i) with h | h <;> simp [signVec, h]

omit [Fintype I] in
/-- Multiplying by `Pi.mulSingle i (-1)` flips the sign at `i` only. -/
lemma signVec_mulSingle_mul (τ : I → ℤˣ) (i j : I) :
    signVec (Pi.mulSingle i (-1) * τ) j = if j = i then -signVec τ j else signVec τ j := by
  by_cases h : j = i
  · subst h
    simp [signVec]
  · simp [signVec, h]

/-- An average that changes sign under a bijection of the sample space vanishes. -/
lemma avg_eq_zero_of_equiv_neg {α : Type*} [Fintype α] (e : α ≃ α) (f : α → ℝ)
    (h : ∀ a, f (e a) = -f a) : avg f = 0 := by
  have h1 := avg_equiv e f
  have h2 := avg_const_mul (-1) f
  simp only [h, neg_one_mul] at h1 h2
  linarith

/-- Distinct signs are uncorrelated: `E[σ i σ j] = [i = j]`. -/
lemma avg_signVec_mul_signVec (i j : I) :
    avg (fun τ : I → ℤˣ => signVec τ i * signVec τ j) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    simp_rw [signVec_mul_self]
    exact avg_const 1
  · refine avg_eq_zero_of_equiv_neg (Equiv.mulLeft (Pi.mulSingle i (-1))) _ fun τ => ?_
    simp [signVec_mulSingle_mul, Ne.symm h]

/-- (T4) Second moment of a weighted sum of independent signs. -/
theorem avg_sum_mul_signVec_sq (w : I → ℝ) :
    avg (fun τ : I → ℤˣ => (∑ i, w i * signVec τ i) ^ 2) = ∑ i, w i ^ 2 := by
  have h : ∀ τ : I → ℤˣ, (∑ i, w i * signVec τ i) ^ 2 =
      ∑ i, ∑ j, w i * w j * (signVec τ i * signVec τ j) := fun τ => by
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  simp_rw [h, avg_sum, avg_const_mul, avg_signVec_mul_signVec]
  simp [sq]

omit [DecidableEq I] in
/-- Flipping all signs negates the sum. -/
lemma sum_signVec_neg (τ : I → ℤˣ) : ∑ i, signVec (-τ) i = -∑ i, signVec τ i := by
  simp [signVec]

/-- (T5) Symmetry: flipping all signs. -/
theorem avg_fun_neg_sum_signVec (F : ℝ → ℝ) :
    avg (fun τ : I → ℤˣ => F (-∑ i, signVec τ i)) =
      avg (fun τ : I → ℤˣ => F (∑ i, signVec τ i)) := by
  simp_rw [← sum_signVec_neg]
  exact avg_equiv (Equiv.neg (I → ℤˣ)) fun τ => F (∑ i, signVec τ i)

/-- Jensen for the square: `(E f)² ≤ E f²`. -/
lemma sq_avg_le_avg_sq {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    avg f ^ 2 ≤ avg (fun a => f a ^ 2) := by
  have h0 : 0 ≤ avg (fun a => (f a - avg f) ^ 2) := avg_nonneg fun a => sq_nonneg _
  have e : (fun a => (f a - avg f) ^ 2) =
      fun a => (f a ^ 2 + -2 * avg f * f a) + avg f ^ 2 := funext fun a => by ring
  rw [e, avg_add, avg_add, avg_const_mul, avg_const] at h0
  nlinarith

/-- (T6) First absolute moment. -/
theorem avg_abs_sum_signVec_le_sqrt :
    avg (fun τ : I → ℤˣ => |∑ i, signVec τ i|) ≤ Real.sqrt (Fintype.card I) := by
  have h := sq_avg_le_avg_sq fun τ : I → ℤˣ => |∑ i, signVec τ i|
  have h2 : avg (fun τ : I → ℤˣ => |∑ i, signVec τ i| ^ 2) = Fintype.card I := by
    simpa using avg_sum_mul_signVec_sq (I := I) fun _ => 1
  rw [h2] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- (T7) The sum is positive with probability `(1 - P(sum = 0)) / 2`. -/
theorem avg_sum_signVec_pos :
    avg (fun τ : I → ℤˣ => if 0 < ∑ i, signVec τ i then (1 : ℝ) else 0) =
      (1 - avg (fun τ : I → ℤˣ => if ∑ i, signVec τ i = 0 then (1 : ℝ) else 0)) / 2 := by
  have hneg : avg (fun τ : I → ℤˣ => if ∑ i, signVec τ i < 0 then (1 : ℝ) else 0) =
      avg (fun τ : I → ℤˣ => if 0 < ∑ i, signVec τ i then (1 : ℝ) else 0) := by
    simpa using avg_fun_neg_sum_signVec (I := I) fun x => if 0 < x then (1 : ℝ) else 0
  have hsum : avg (fun τ : I → ℤˣ => if 0 < ∑ i, signVec τ i then (1 : ℝ) else 0) +
      avg (fun τ : I → ℤˣ => if ∑ i, signVec τ i = 0 then (1 : ℝ) else 0) +
      avg (fun τ : I → ℤˣ => if ∑ i, signVec τ i < 0 then (1 : ℝ) else 0) = 1 := by
    rw [← avg_add, ← avg_add]
    refine (congrArg avg (funext fun τ => ?_)).trans (avg_const 1)
    rcases lt_trichotomy (∑ i, signVec τ i) 0 with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  linarith

/-! ### Independence of disjoint blocks of signs -/

/-- The average over a product type is the iterated average. -/
lemma avg_prod_eq {β δ : Type*} [Fintype β] [Fintype δ] (G : β × δ → ℝ) :
    avg G = avg (fun b => avg (fun d => G (b, d))) := by
  unfold avg
  dsimp only
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, sum_div, sum_div]
  exact sum_congr rfl fun b _ => by rw [div_div, mul_comm]

/-- (T3) Independence of the signs on a set of indices and on its complement. -/
theorem avg_split (p : I → Prop) [DecidablePred p]
    (F : ({i // p i} → ℤˣ) → ({i // ¬ p i} → ℤˣ) → ℝ) :
    avg (fun τ : I → ℤˣ => F (fun i => τ i) (fun i => τ i)) =
      avg (fun τ₁ : {i // p i} → ℤˣ => avg (fun τ₂ : {i // ¬ p i} → ℤˣ => F τ₁ τ₂)) := by
  rw [← avg_prod_eq fun q => F q.1 q.2]
  exact avg_equiv (Equiv.piEquivPiSubtypeProd p fun _ : I => ℤˣ) fun q => F q.1 q.2

end Averaging.Opportunistic
