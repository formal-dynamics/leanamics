import Median.ExpanderGeneralDefs

/-! # Phase I: the upper bound on the expected loss

The combinatorial core of the paper's (eq-upperOnDAB) in the proof of Lemma 2 (Cooper, Elsässer
and Radzik, ICALP 2014, arXiv:1404.7479): with `p_v = d_v^B / d`,
`∑_{v ∈ A} p_v² ≤ (A B² / n²)(1 + 15η)`.
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The layer-cake bound -/

/-- The layer-cake bound before the last layer:
`min(p, θ_m)² ≤ θ₀² + ∑_{j < m, θ_j ≤ p} (θ_{j+1}² − θ_j²)`. -/
lemma min_sq_le_layers {θ : ℕ → ℝ} (hθ0 : 0 ≤ θ 0) (hθ : ∀ j, θ j ≤ θ (j + 1)) {p : ℝ}
    (hp : 0 ≤ p) (m : ℕ) :
    min p (θ m) ^ 2
      ≤ θ 0 ^ 2 + ∑ j ∈ range m, if θ j ≤ p then θ (j + 1) ^ 2 - θ j ^ 2 else 0 := by
  induction m with
  | zero =>
    simpa using pow_le_pow_left₀ (le_min hp hθ0) (min_le_right p (θ 0)) 2
  | succ m ih =>
    have hθm : 0 ≤ θ m := hθ0.trans (monotone_nat_of_le_succ hθ (Nat.zero_le m))
    rw [Finset.sum_range_succ]
    split_ifs with h
    · rw [min_eq_right h] at ih
      have := pow_le_pow_left₀ (le_min hp (hθm.trans (hθ m))) (min_le_right p (θ (m + 1))) 2
      linarith
    · rw [min_eq_left (not_le.mp h).le] at ih
      rw [min_eq_left ((not_le.mp h).le.trans (hθ m))]
      linarith

/-- **The layer-cake bound**: for `0 ≤ p ≤ 1` and a non-decreasing sequence `θ` with `θ₀ ≥ 0`,
`p² ≤ θ₀² + ∑_{j < m, θ_j ≤ p} (θ_{j+1}² − θ_j²) + [θ_m ≤ p]`. -/
lemma sq_le_layers {θ : ℕ → ℝ} (hθ0 : 0 ≤ θ 0) (hθ : ∀ j, θ j ≤ θ (j + 1)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    p ^ 2 ≤ θ 0 ^ 2 + (∑ j ∈ range m, if θ j ≤ p then θ (j + 1) ^ 2 - θ j ^ 2 else 0)
      + if θ m ≤ p then 1 else 0 := by
  have h := min_sq_le_layers hθ0 hθ hp0 m
  split_ifs with hm
  · nlinarith [sq_nonneg (min p (θ m))]
  · rw [min_eq_left (not_le.mp hm).le] at h
    linarith

/-- The layer-cake bound summed over a finite set: `∑_{v ∈ s} p_v² ≤ |s| θ₀²
+ ∑_{j < m} |{v ∈ s : θ_j ≤ p_v}| (θ_{j+1}² − θ_j²) + |{v ∈ s : θ_m ≤ p_v}|`. -/
lemma sum_sq_le_layers {ι : Type*} (s : Finset ι) {p : ι → ℝ} (hp0 : ∀ v ∈ s, 0 ≤ p v)
    (hp1 : ∀ v ∈ s, p v ≤ 1) {θ : ℕ → ℝ} (hθ0 : 0 ≤ θ 0) (hθ : ∀ j, θ j ≤ θ (j + 1))
    (m : ℕ) :
    ∑ v ∈ s, p v ^ 2 ≤ s.card * θ 0 ^ 2
      + ∑ j ∈ range m, ((s.filter fun v => θ j ≤ p v).card : ℝ) * (θ (j + 1) ^ 2 - θ j ^ 2)
      + (s.filter fun v => θ m ≤ p v).card := by
  calc ∑ v ∈ s, p v ^ 2
      ≤ ∑ v ∈ s, (θ 0 ^ 2
          + (∑ j ∈ range m, if θ j ≤ p v then θ (j + 1) ^ 2 - θ j ^ 2 else 0)
          + if θ m ≤ p v then 1 else 0) :=
        Finset.sum_le_sum fun v hv => sq_le_layers hθ0 hθ (hp0 v hv) (hp1 v hv) m
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_comm,
        Finset.sum_boole, nsmul_eq_mul]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-! ### The number of layers -/

/-- `(m + 1)³ ≤ 2 · 4^m`. -/
lemma succ_pow_three_le (m : ℕ) : (m + 1) ^ 3 ≤ 2 * 4 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rcases m with _ | m
    · norm_num
    · have h : (m + 1 + 1 + 1) ^ 3 ≤ 4 * (m + 1 + 1) ^ 3 := by
        ring_nf
        nlinarith [Nat.zero_le (m ^ 3), Nat.zero_le (m ^ 2), Nat.zero_le m]
      rw [pow_succ 4 (m + 1)]
      omega

/-- If `625 η³ 4^m ≤ 1` then `(1 + 3m) η ≤ 5`. -/
lemma one_add_three_mul_le {η : ℝ} (hη : 0 ≤ η) {m : ℕ} (h : 625 * η ^ 3 * 4 ^ m ≤ 1) :
    (1 + 3 * m) * η ≤ 5 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hm : ((m : ℝ) + 1) ^ 3 ≤ 2 * 4 ^ m := by exact_mod_cast succ_pow_three_le m
  have hw : 1 < ((m : ℝ) + 1) * η := by nlinarith
  have h1 : 1 < (((m : ℝ) + 1) * η) ^ 3 := one_lt_pow₀ hw (by norm_num)
  have h2 : (((m : ℝ) + 1) * η) ^ 3 ≤ 2 * 4 ^ m * η ^ 3 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hm (pow_nonneg hη 3)
  linarith

/-! ### The size of the upper sets -/

/-- **The size of an upper set** (from (mixing-prop)): a set `D ⊆ A` with
`|D| ≥ (2/3) α c^{3/2} n` on which `p_v ≥ (1 + u η) B / n` satisfies `|D| u² ≤ A`. -/
lemma card_mul_sq_le {d : ℕ} (hd : 0 < d) {c α : ℝ} (hc0 : 0 < c) (hα0 : 0 < α)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hB0 : 0 < minority a x)
    (hA0 : 0 < majority a x) {D : Finset V} (hD : D ⊆ univ.filter (fun v => x v = a))
    {u : ℝ} (hu : 0 ≤ u)
    (hDp : ∀ v ∈ D,
      (1 + u * phaseEta α a x) * minority a x / Fintype.card V ≤ (nbCount G a x v : ℝ) / d)
    (hDc : 2 / 3 * α * (c * √c) * Fintype.card V ≤ D.card) :
    (D.card : ℝ) * u ^ 2 ≤ majority a x := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < Fintype.card V := by
    have := majority_add_minority a x
    exact_mod_cast (by omega : 0 < Fintype.card V)
  have hA : (0 : ℝ) < majority a x := by exact_mod_cast hA0
  have hB' : (0 : ℝ) < minority a x := by exact_mod_cast hB0
  set n : ℝ := (Fintype.card V : ℝ)
  set A : ℝ := (majority a x : ℝ)
  set B : ℝ := (minority a x : ℝ)
  set k : ℝ := (D.card : ℝ) with hk_def
  have hk : 0 < k := lt_of_lt_of_le (by positivity) hDc
  have hη : phaseEta α a x = α * n / √(A * B) := rfl
  have hs0 : 0 < √(A * B) := Real.sqrt_pos.mpr (mul_pos hA hB')
  have hs2 : √(A * B) ^ 2 = A * B := Real.sq_sqrt (mul_pos hA hB').le
  have ht2 : √(k * B) ^ 2 = k * B := Real.sq_sqrt (mul_pos hk hB').le
  have ht0 : 0 ≤ √(k * B) := Real.sqrt_nonneg _
  -- the mixing inequality for `D` and the minority
  have hdisj : Disjoint D (univ.filter fun v => x v ≠ a) :=
    (Finset.disjoint_filter_filter_not univ univ (fun v => x v = a)).mono_left hD
  have hmixD := hmix D _ hdisj hB hDc
  have hE : (edgeCount G D (univ.filter fun v => x v ≠ a) : ℝ)
      = ∑ v ∈ D, (nbCount G a x v : ℝ) := by
    unfold edgeCount
    push_cast
    exact Finset.sum_congr rfl fun v _ => by rw [card_inter_minority]
  have hElow : k * (d * ((1 + u * phaseEta α a x) * B / n)) ≤ ∑ v ∈ D, (nbCount G a x v : ℝ) := by
    rw [hk_def, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun v hv => ?_
    have := hDp v hv
    rw [le_div_iff₀ hd'] at this
    linarith
  rw [hE] at hmixD
  change |∑ v ∈ D, (nbCount G a x v : ℝ) - d * k * B / n| ≤ α * d * √(k * B) at hmixD
  have h1 : d * (k * u * phaseEta α a x * B / n) ≤ d * (α * √(k * B)) := by
    have := (le_abs_self _).trans hmixD
    have e : k * (d * ((1 + u * phaseEta α a x) * B / n)) - d * k * B / n
        = d * (k * u * phaseEta α a x * B / n) := by ring
    linarith
  have h2 := le_of_mul_le_mul_left h1 hd'
  have e2 : k * u * phaseEta α a x * B / n = α * (k * u * B / √(A * B)) := by
    rw [hη]
    field_simp
  rw [e2] at h2
  have h3 := le_of_mul_le_mul_left h2 hα0
  rw [div_le_iff₀ hs0] at h3
  have h4 := pow_le_pow_left₀ (by positivity) h3 2
  rw [mul_pow √(k * B), ht2, hs2] at h4
  have h5 : (k * u ^ 2) * (k * B ^ 2) ≤ A * (k * B ^ 2) := by linarith
  exact le_of_mul_le_mul_right h5 (by positivity)

/-- **The loss bound** (the paper's (eq-upperOnDAB)):
`∑_{v ∈ A} (d_v^B / d)² ≤ (A B² / n²)(1 + 15η)`. -/
theorem sum_sq_nbCount_le {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    ∑ v ∈ univ.filter (fun v => x v = a), ((nbCount G a x v : ℝ) / d) ^ 2
      ≤ (majority a x : ℝ) * (minority a x : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2
        * (1 + 15 * phaseEta α a x) := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn0 | hn0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    simp
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hAB := majority_add_minority a x
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn0
  have hB0 : (0 : ℝ) < minority a x := lt_of_lt_of_le (by positivity) hB
  have hB0' : 0 < minority a x := by exact_mod_cast hB0
  have hA0' : 0 < majority a x := by omega
  have hAB' : (majority a x : ℝ) + minority a x = Fintype.card V := by exact_mod_cast hAB
  have hBA' : (minority a x : ℝ) ≤ majority a x := by exact_mod_cast hBA
  have hA0 : (0 : ℝ) < majority a x := by exact_mod_cast hA0'
  set n : ℝ := (Fintype.card V : ℝ)
  set A : ℝ := (majority a x : ℝ)
  set B : ℝ := (minority a x : ℝ)
  set η := phaseEta α a x
  have hη : η = α * n / √(A * B) := rfl
  have hs0 : 0 < √(A * B) := Real.sqrt_pos.mpr (mul_pos hA0 hB0)
  have hs2 : √(A * B) ^ 2 = A * B := Real.sq_sqrt (mul_pos hA0 hB0).le
  have hr2 : √c ^ 2 = c := Real.sq_sqrt hc0.le
  have hηs : η * √(A * B) = α * n := by
    rw [hη]
    field_simp
  have hη0 : 0 < η := by
    rw [hη]
    positivity
  have hABc : c * n ^ 2 / 2 ≤ A * B := by
    have h1 : 0 ≤ (A - n / 2) * B := mul_nonneg (by linarith) hB0.le
    have h2 : 0 ≤ n / 2 * (B - c * n) := mul_nonneg (by linarith) (by linarith)
    linarith
  -- `η ≤ c / 25`
  have hα2 : α ^ 2 ≤ c ^ 3 / 1296 :=
    calc α ^ 2 ≤ (c * √c / 36) ^ 2 := pow_le_pow_left₀ hα0.le hα 2
      _ = c ^ 3 / 1296 := by
        rw [div_pow, mul_pow, hr2]
        ring
  have hηc : η ≤ c / 25 := by
    by_contra hlt
    have h1 : c / 25 * √(A * B) < α * n := by
      rw [← hηs]
      exact mul_lt_mul_of_pos_right (not_le.mp hlt) hs0
    have h2 := pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    rw [mul_pow, hs2, mul_pow] at h2
    have h3 := mul_le_mul_of_nonneg_left hABc (sq_nonneg (c / 25))
    have h4 := mul_le_mul_of_nonneg_right hα2 (sq_nonneg n)
    have h5 : 0 < c ^ 3 * n ^ 2 := by positivity
    linarith
  have hη1 : η ≤ 1 := by linarith
  -- the probabilities `p_v`
  set p : V → ℝ := fun v => (nbCount G a x v : ℝ) / d
  have hp0 : ∀ v, 0 ≤ p v := fun v => by positivity
  have hp1 : ∀ v, p v ≤ 1 := fun v => by
    have : nbCount G a x v ≤ d := by
      rw [← hreg v, ← G.card_neighborFinset_eq_degree]
      exact Finset.card_filter_le _ _
    show (nbCount G a x v : ℝ) / d ≤ 1
    rw [div_le_one hd']
    exact_mod_cast this
  -- the thresholds `θ_j = (1 + 2^j η) B / n`
  set θ : ℕ → ℝ := fun j => (1 + 2 ^ j * η) * B / n with hθ_def
  have hθ0 : 0 ≤ θ 0 := by
    simp only [hθ_def]
    positivity
  have hθ : ∀ j, θ j ≤ θ (j + 1) := fun j => by
    simp only [hθ_def]
    have h := mul_nonneg (pow_nonneg (zero_le_two (α := ℝ)) j) hη0.le
    have : (2 : ℝ) ^ j * η ≤ 2 ^ (j + 1) * η := by
      rw [pow_succ]
      linarith
    gcongr
  -- the number of layers
  have hR : 1 ≤ n ^ 2 / (η * B ^ 2) := by
    rw [one_le_div (by positivity)]
    calc η * B ^ 2 ≤ 1 * B ^ 2 := mul_le_mul_of_nonneg_right hη1 (sq_nonneg B)
      _ ≤ n ^ 2 := by
        rw [one_mul]
        exact pow_le_pow_left₀ hB0.le (by linarith) 2
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hR (by norm_num : (1 : ℝ) < 4)
  have hm1' : 4 ^ m * (η * B ^ 2) ≤ n ^ 2 := by rwa [le_div_iff₀ (by positivity)] at hm1
  have hm2' : n ^ 2 < 4 ^ (m + 1) * (η * B ^ 2) := by rwa [div_lt_iff₀ (by positivity)] at hm2
  -- (i) the size of the upper sets
  have hsize : ∀ j ≤ m,
      (((univ.filter fun v => x v = a).filter fun v => θ j ≤ p v).card : ℝ) * 4 ^ j ≤ A := by
    intro j hj
    set D := (univ.filter fun v => x v = a).filter fun v => θ j ≤ p v
    by_cases hk : (D.card : ℝ) < A / 4 ^ m
    · rw [lt_div_iff₀ (by positivity)] at hk
      calc (D.card : ℝ) * 4 ^ j ≤ D.card * 4 ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (Nat.cast_nonneg _)
        _ ≤ A := hk.le
    · have h1 : A ≤ D.card * 4 ^ m := (div_le_iff₀ (by positivity)).mp (not_lt.mp hk)
      have h2 : A * (η * B ^ 2) ≤ D.card * n ^ 2 :=
        calc A * (η * B ^ 2) ≤ D.card * 4 ^ m * (η * B ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = D.card * (4 ^ m * (η * B ^ 2)) := by ring
          _ ≤ D.card * n ^ 2 := mul_le_mul_of_nonneg_left hm1' (Nat.cast_nonneg _)
      have h3 : A * B ^ 2 * (α * n) ≤ D.card * n ^ 2 * √(A * B) := by
        rw [← hηs]
        have := mul_le_mul_of_nonneg_right h2 hs0.le
        linarith
      have hs : 2 / 3 * √c * n ≤ √(A * B) := by
        rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, mul_pow, hr2]
        have : 0 ≤ c * n ^ 2 := by positivity
        linarith
      have h4 : 2 / 3 * √c * n * (c * n) ≤ √(A * B) * B :=
        mul_le_mul hs hB (by positivity) hs0.le
      have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ α * √(A * B) * n)
      have h6 : A * B ^ 2 * (α * n) = √(A * B) ^ 2 * B * (α * n) := by
        rw [hs2]
        ring
      have h7 : √(A * B) * (2 / 3 * α * (c * √c) * n) * n ^ 2
          ≤ √(A * B) * D.card * n ^ 2 := by
        linarith
      have hDc := le_of_mul_le_mul_left (le_of_mul_le_mul_right h7 (by positivity)) hs0
      have := card_mul_sq_le hd hc0 hα0 hmix a x hB hB0' hA0' (D := D)
        (Finset.filter_subset _ _) (u := 2 ^ j) (by positivity)
        (fun v hv => (Finset.mem_filter.mp hv).2) hDc
      rwa [← pow_mul, mul_comm j 2, pow_mul, show ((2 : ℝ) ^ 2) = 4 by norm_num] at this
  -- (iii) summing the layer-cake bound over `A`
  set K : ℝ := A * B ^ 2 / n ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hlayers := sum_sq_le_layers (univ.filter fun v => x v = a) (p := p)
    (fun v _ => hp0 v) (fun v _ => hp1 v) hθ0 hθ m
  have hT1 : ((univ.filter fun v => x v = a).card : ℝ) * θ 0 ^ 2 = K * (1 + η) ^ 2 := by
    change A * θ 0 ^ 2 = _
    simp only [hθ_def, hK]
    ring
  have hT2 : ∑ j ∈ range m, (((univ.filter fun v => x v = a).filter fun v => θ j ≤ p v).card : ℝ)
      * (θ (j + 1) ^ 2 - θ j ^ 2) ≤ K * (4 * η) + K * (3 * m * η ^ 2) := by
    calc _ ≤ ∑ j ∈ range m, (K * (2 * η) * (1 / 2) ^ j + K * (3 * η ^ 2)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hδ : 0 ≤ θ (j + 1) ^ 2 - θ j ^ 2 := by
            have := pow_le_pow_left₀
              (hθ0.trans (monotone_nat_of_le_succ hθ (Nat.zero_le j))) (hθ j) 2
            linarith
          have hE := (le_div_iff₀ (by positivity)).mpr (hsize j (Finset.mem_range.mp hj).le)
          calc _ ≤ A / 4 ^ j * (θ (j + 1) ^ 2 - θ j ^ 2) := mul_le_mul_of_nonneg_right hE hδ
            _ = _ := by
              simp only [hθ_def, hK]
              rw [show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num,
                pow_succ (2 : ℝ) j, one_div_pow]
              field_simp
              ring
      _ = K * (2 * η) * ∑ j ∈ range m, (1 / 2 : ℝ) ^ j + K * (3 * m * η ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          ring
      _ ≤ K * (2 * η) * 2 + K * (3 * m * η ^ 2) := by
          gcongr
          exact sum_geometric_two_le m
      _ = K * (4 * η) + K * (3 * m * η ^ 2) := by ring
  have hT3 : (((univ.filter fun v => x v = a).filter fun v => θ m ≤ p v).card : ℝ)
      ≤ K * (4 * η) := by
    set E := (univ.filter fun v => x v = a).filter fun v => θ m ≤ p v
    have h1 : (E.card : ℝ) * n ^ 2 ≤ 4 * A * (η * B ^ 2) :=
      calc (E.card : ℝ) * n ^ 2 ≤ E.card * (4 ^ (m + 1) * (η * B ^ 2)) :=
            mul_le_mul_of_nonneg_left hm2'.le (Nat.cast_nonneg _)
        _ = 4 * (E.card * 4 ^ m) * (η * B ^ 2) := by ring
        _ ≤ 4 * A * (η * B ^ 2) := by
            have := hsize m le_rfl
            gcongr
    rw [hK, show A * B ^ 2 / n ^ 2 * (4 * η) = 4 * A * (η * B ^ 2) / n ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    exact h1
  -- (iv) the number of layers is small: `(1 + 3m) η ≤ 5`
  have hiv : (1 + 3 * m) * η ≤ 5 := by
    apply one_add_three_mul_le hη0.le
    have h625 : 625 * η ^ 2 * n ^ 2 ≤ B ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hηc hn.le
      have := pow_le_pow_left₀ (by positivity : 0 ≤ 25 * η * n) (by linarith : 25 * η * n ≤ B) 2
      linarith
    have : (625 * η ^ 3 * 4 ^ m) * n ^ 2 ≤ 1 * n ^ 2 :=
      calc (625 * η ^ 3 * 4 ^ m) * n ^ 2 = 4 ^ m * η * (625 * η ^ 2 * n ^ 2) := by ring
        _ ≤ 4 ^ m * η * B ^ 2 := mul_le_mul_of_nonneg_left h625 (by positivity)
        _ = 4 ^ m * (η * B ^ 2) := by ring
        _ ≤ n ^ 2 := hm1'
        _ = 1 * n ^ 2 := (one_mul _).symm
    exact le_of_mul_le_mul_right this (by positivity)
  have h5 := mul_le_mul_of_nonneg_left hiv (by positivity : 0 ≤ K * η)
  show ∑ v ∈ univ.filter (fun v => x v = a), p v ^ 2 ≤ K * (1 + 15 * η)
  rw [hT1] at hlayers
  linarith

end Median.ExpanderGeneral
