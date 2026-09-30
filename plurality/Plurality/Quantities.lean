import Mathlib

/-!
# Plurality, bias, `α` and `γ` of a color distribution (Section 3)

For a `k`-color distribution `c : Fin k → ℕ` with `∑ₕ cₕ = n` the paper uses

* `m(c) = maxₕ cₕ` (`maxc`) and `M(c) = {j | cⱼ = m(c)}` (`argmaxSet`);
* the **bias** `s(c) = m(c) - max_{h ∉ M(c)} cₕ` if the plurality color is
  unique and `0` otherwise (`bias`);
* `α(c) = (n - m(c)) s(c) / n²` and `γ(c) = (n m(c) - ∑ₕ cₕ²)/n² - α(c)`;
* `μⱼ(c) = cⱼ (1 + (n cⱼ - ∑ₕ cₕ²)/n²)`, the expected next count of color
  `j` (Lemma 2.1, `Plurality.expected_count`).

Lemma 3.1 bounds these quantities and Lemma 3.2 rewrites `μⱼ` in terms of
them. Everything here is elementary algebra about finite sums of naturals.
-/

namespace Plurality

open Finset

variable {k : ℕ}

/-- `m(c)`: the plurality size. -/
def maxc (c : Fin k → ℕ) : ℕ := univ.sup c

/-- `M(c)`: the plurality colors. -/
def argmaxSet (c : Fin k → ℕ) : Finset (Fin k) := univ.filter fun h => c h = maxc c

/-- The largest count among the colors outside `M(c)` (`0` if there is none). -/
def secondc (c : Fin k → ℕ) : ℕ := (univ.filter fun h => c h ≠ maxc c).sup c

/-- `s(c)`: the bias, i.e. the gap between the plurality color and every other
color when the plurality color is unique, and `0` otherwise. -/
def bias (c : Fin k → ℕ) : ℕ := if (argmaxSet c).card = 1 then maxc c - secondc c else 0

/-- `α(c) = (n - m(c)) s(c) / n²`. -/
noncomputable def alpha (n : ℕ) (c : Fin k → ℕ) : ℝ := ((n : ℝ) - maxc c) * bias c / (n : ℝ) ^ 2

/-- `γ(c) = (n m(c) - ∑ₕ cₕ²) / n² - α(c)`. -/
noncomputable def gamma (n : ℕ) (c : Fin k → ℕ) : ℝ :=
  ((n : ℝ) * maxc c - ∑ h, (c h : ℝ) ^ 2) / (n : ℝ) ^ 2 - alpha n c

/-- `μⱼ(c) = cⱼ (1 + (n cⱼ - ∑ₕ cₕ²)/n²)`, the expected next count of `j`. -/
noncomputable def mu (n : ℕ) (c : Fin k → ℕ) (j : Fin k) : ℝ :=
  c j * (1 + ((n : ℝ) * c j - ∑ h, (c h : ℝ) ^ 2) / (n : ℝ) ^ 2)

/-! ### Basic facts -/

lemma le_maxc (c : Fin k → ℕ) (h : Fin k) : c h ≤ maxc c := le_sup (mem_univ h)

lemma exists_eq_maxc (hk : 0 < k) (c : Fin k → ℕ) : ∃ m, c m = maxc c := by
  obtain ⟨m, _, hm⟩ := exists_mem_eq_sup univ ⟨⟨0, hk⟩, mem_univ _⟩ c
  exact ⟨m, hm.symm⟩

lemma mem_argmaxSet {c : Fin k → ℕ} {j : Fin k} : j ∈ argmaxSet c ↔ c j = maxc c := by
  simp [argmaxSet]

lemma maxc_le_of_sum {c : Fin k → ℕ} {n : ℕ} (hc : ∑ h, c h = n) : maxc c ≤ n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [maxc]
  obtain ⟨m, hm⟩ := exists_eq_maxc hk c
  rw [← hm, ← hc]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ m)

lemma secondc_le_maxc (c : Fin k → ℕ) : secondc c ≤ maxc c :=
  Finset.sup_le fun h _ => le_maxc c h

lemma bias_le_maxc (c : Fin k → ℕ) : bias c ≤ maxc c := by
  unfold bias; split_ifs <;> omega

/-- A unique plurality color `m`. -/
lemma argmaxSet_eq_singleton {c : Fin k → ℕ} {m : Fin k} (hM : argmaxSet c = {m}) :
    c m = maxc c := by
  have : m ∈ argmaxSet c := by rw [hM]; exact mem_singleton_self m
  exact mem_argmaxSet.mp this

lemma lt_of_argmaxSet_eq_singleton {c : Fin k → ℕ} {m : Fin k} (hM : argmaxSet c = {m})
    {j : Fin k} (hj : j ≠ m) : c j < maxc c := by
  refine lt_of_le_of_ne (le_maxc c j) fun h => hj ?_
  have : j ∈ argmaxSet c := mem_argmaxSet.mpr h
  rw [hM] at this
  exact mem_singleton.mp this

lemma bias_of_singleton {c : Fin k → ℕ} {m : Fin k} (hM : argmaxSet c = {m}) :
    bias c = maxc c - secondc c := by
  simp [bias, hM]

/-- **Every other color trails a plurality color by at least the bias.** -/
lemma add_bias_le {c : Fin k → ℕ} {m : Fin k} (hm : c m = maxc c) {h : Fin k} (hh : h ≠ m) :
    c h + bias c ≤ maxc c := by
  unfold bias
  split_ifs with h1
  · obtain ⟨m', hm'⟩ := card_eq_one.mp h1
    have hmM : m ∈ argmaxSet c := mem_argmaxSet.mpr hm
    rw [hm', mem_singleton] at hmM
    subst hmM
    have hne : c h ≠ maxc c := by
      intro heq
      have : h ∈ argmaxSet c := mem_argmaxSet.mpr heq
      rw [hm', mem_singleton] at this
      exact hh this
    have : c h ≤ secondc c := le_sup (mem_filter.mpr ⟨mem_univ h, hne⟩)
    have := secondc_le_maxc c
    omega
  · simpa using le_maxc c h

/-- **The bias is attained**: with at least two colors, some color other than a
plurality color `m` has exactly `m(c) - s(c)` nodes. -/
lemma exists_add_bias_eq (hk : 2 ≤ k) {c : Fin k → ℕ} {m : Fin k} (hm : c m = maxc c) :
    ∃ ℓ, ℓ ≠ m ∧ c ℓ + bias c = maxc c := by
  unfold bias
  split_ifs with h1
  · obtain ⟨m', hm'⟩ := card_eq_one.mp h1
    have hmM : m ∈ argmaxSet c := mem_argmaxSet.mpr hm
    rw [hm', mem_singleton] at hmM
    subst hmM
    have hne : (univ.filter fun h => c h ≠ maxc c).Nonempty := by
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin k, ℓ ≠ m := by
        by_cases h0 : (m : ℕ) = 0
        · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff, h0] at h⟩
        · exact ⟨⟨0, by omega⟩, fun h => h0 (by simp [← h])⟩
      refine ⟨ℓ, mem_filter.mpr ⟨mem_univ ℓ, fun heq => hℓ ?_⟩⟩
      have : ℓ ∈ argmaxSet c := mem_argmaxSet.mpr heq
      rw [hm'] at this
      exact mem_singleton.mp this
    obtain ⟨ℓ, hℓ, hℓs⟩ := exists_mem_eq_sup _ hne c
    refine ⟨ℓ, fun h => (mem_filter.mp hℓ).2 (h ▸ hm), ?_⟩
    have : secondc c = c ℓ := hℓs
    have := secondc_le_maxc c
    omega
  · have hmM : m ∈ argmaxSet c := mem_argmaxSet.mpr hm
    have hcard : 1 < (argmaxSet c).card := by
      have := card_pos.mpr ⟨m, hmM⟩
      omega
    obtain ⟨ℓ, hℓ, hne⟩ := exists_mem_ne hcard m
    exact ⟨ℓ, hne, by simpa using mem_argmaxSet.mp hℓ⟩

/-- `n m - ∑ₕ cₕ² = ∑ₕ cₕ (m - cₕ)` when the counts sum to `n`. -/
lemma sum_mul_sub_eq {c : Fin k → ℕ} {n : ℕ} (hc : ∑ h, c h = n) :
    (n : ℝ) * maxc c - ∑ h, (c h : ℝ) ^ 2 = ∑ h, (c h : ℝ) * (maxc c - c h) := by
  have hc' : (n : ℝ) = ∑ h, (c h : ℝ) := by exact_mod_cast hc.symm
  rw [hc', sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun h _ => by ring

/-- The key identity: `γ(c) n² = ∑_{h ≠ m} cₕ (m(c) - s(c) - cₕ)`. -/
lemma gamma_mul_sq {c : Fin k → ℕ} {n : ℕ} (hc : ∑ h, c h = n) (hn : 0 < n) {m : Fin k}
    (hm : c m = maxc c) :
    gamma n c * (n : ℝ) ^ 2
      = ∑ h ∈ univ.erase m, (c h : ℝ) * ((maxc c : ℝ) - bias c - c h) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : (n : ℝ) - maxc c = ∑ h ∈ univ.erase m, (c h : ℝ) := by
    have hc' : (n : ℝ) = ∑ h, (c h : ℝ) := by exact_mod_cast hc.symm
    rw [hc', ← add_sum_erase univ _ (mem_univ m), hm]
    ring
  have h1 : (n : ℝ) * maxc c - ∑ h, (c h : ℝ) ^ 2
      = ∑ h ∈ univ.erase m, (c h : ℝ) * (maxc c - c h) := by
    rw [sum_mul_sub_eq hc, ← add_sum_erase univ _ (mem_univ m), hm]
    ring
  unfold gamma alpha
  field_simp
  rw [h1, hsum, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun h _ => by ring

/-! ### Lemma 3.1 -/

/-- **Lemma 3.1 (a).** `0 ≤ s(c) ≤ m(c) - (n - m(c))/(k - 1)`. -/
theorem lemma_3_1_a {c : Fin k → ℕ} {n : ℕ} (hc : ∑ h, c h = n) :
    (0 : ℝ) ≤ bias c ∧ (bias c : ℝ) ≤ maxc c - ((n : ℝ) - maxc c) / ((k : ℝ) - 1) := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  rcases lt_or_ge k 2 with hk | hk
  · -- `k ≤ 1`: the only color carries all the nodes, and `k - 1 ≤ 0`
    have hk1 : ((k : ℝ) - 1) ≤ 0 := by
      have : (k : ℝ) ≤ 1 := by exact_mod_cast (by omega : k ≤ 1)
      linarith
    have hnm : (maxc c : ℝ) ≤ n := by exact_mod_cast maxc_le_of_sum hc
    have hdiv : ((n : ℝ) - maxc c) / ((k : ℝ) - 1) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by linarith) hk1
    have : (bias c : ℝ) ≤ maxc c := by exact_mod_cast bias_le_maxc c
    linarith
  obtain ⟨m, hm⟩ := exists_eq_maxc (by omega) c
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- each of the `k - 1` other colors has at most `m(c) - s(c)` nodes
  have hsum : (n : ℝ) - maxc c = ∑ h ∈ univ.erase m, (c h : ℝ) := by
    have hc' : (n : ℝ) = ∑ h, (c h : ℝ) := by exact_mod_cast hc.symm
    rw [hc', ← add_sum_erase univ _ (mem_univ m), hm]
    ring
  have hle : ∑ h ∈ univ.erase m, (c h : ℝ) ≤ ((k : ℝ) - 1) * ((maxc c : ℝ) - bias c) := by
    calc ∑ h ∈ univ.erase m, (c h : ℝ)
        ≤ ∑ _h ∈ univ.erase m, ((maxc c : ℝ) - bias c) := by
          refine sum_le_sum fun h hh => ?_
          have := add_bias_le hm (ne_of_mem_erase hh)
          have : ((c h + bias c : ℕ) : ℝ) ≤ maxc c := by exact_mod_cast this
          push_cast at this
          linarith
      _ = ((k : ℝ) - 1) * ((maxc c : ℝ) - bias c) := by
          rw [sum_const, card_erase_of_mem (mem_univ m), card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_sub (by omega)]
          push_cast
          ring
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hk1]
  linarith

/-- **Lemma 3.1 (b).** `0 ≤ α(c) ≤ min {s(c)/n, 1/4}`. -/
theorem lemma_3_1_b {c : Fin k → ℕ} {n : ℕ} (hc : ∑ h, c h = n) :
    0 ≤ alpha n c ∧ alpha n c ≤ min ((bias c : ℝ) / n) (1 / 4) := by
  have hnm : (maxc c : ℝ) ≤ n := by exact_mod_cast maxc_le_of_sum hc
  have hsm : (bias c : ℝ) ≤ maxc c := by exact_mod_cast bias_le_maxc c
  have hs0 : (0 : ℝ) ≤ bias c := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ maxc c := Nat.cast_nonneg _
  unfold alpha
  refine ⟨by apply div_nonneg <;> [nlinarith; positivity], le_min ?_ ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) hn0]
    nlinarith [mul_nonneg (mul_nonneg hs0 hm0) hn0.le]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ((n : ℝ) - 2 * maxc c)]

/-- **Lemma 3.1 (c).** `0 ≤ γ(c) ≤ 1/8`. -/
theorem lemma_3_1_c {c : Fin k → ℕ} {n : ℕ} (hc : ∑ h, c h = n) (hn : 0 < n) :
    0 ≤ gamma n c ∧ gamma n c ≤ 1 / 8 := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hc; omega
    · exact hk
  obtain ⟨m, hm⟩ := exists_eq_maxc hk c
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hkey := gamma_mul_sq hc hn hm
  -- `d = m(c) - s(c)` bounds every other color
  set d : ℝ := (maxc c : ℝ) - bias c with hd
  have hle (h : Fin k) (hh : h ∈ univ.erase m) : (c h : ℝ) ≤ d := by
    have := add_bias_le hm (ne_of_mem_erase hh)
    have : ((c h + bias c : ℕ) : ℝ) ≤ maxc c := by exact_mod_cast this
    push_cast at this
    linarith
  constructor
  · have : 0 ≤ gamma n c * (n : ℝ) ^ 2 := by
      rw [hkey]
      exact sum_nonneg fun h hh => mul_nonneg (Nat.cast_nonneg _) (by linarith [hle h hh])
    exact nonneg_of_mul_nonneg_left this hn0
  · suffices gamma n c * (n : ℝ) ^ 2 ≤ 1 / 8 * (n : ℝ) ^ 2 from
      le_of_mul_le_mul_right this hn0
    rw [hkey]
    have hsum : (n : ℝ) - maxc c = ∑ h ∈ univ.erase m, (c h : ℝ) := by
      have hc' : (n : ℝ) = ∑ h, (c h : ℝ) := by exact_mod_cast hc.symm
      rw [hc', ← add_sum_erase univ _ (mem_univ m), hm]
      ring
    have hd0 : 0 ≤ d := by
      have := bias_le_maxc c
      have : (bias c : ℝ) ≤ maxc c := by exact_mod_cast this
      linarith
    have hdm : d ≤ maxc c := by
      have : (0 : ℝ) ≤ bias c := Nat.cast_nonneg _
      linarith
    rcases lt_or_ge k 2 with hk2 | hk2
    · -- a single color: the sum is empty
      have : univ.erase m = ∅ := by
        ext h
        simp only [mem_erase, mem_univ, and_true, Finset.notMem_empty, iff_false]
        intro hne
        exact hne (Fin.ext (by omega))
      rw [this, sum_empty]
      positivity
    obtain ⟨ℓ, hℓm, hℓ⟩ := exists_add_bias_eq hk2 hm
    have hℓd : (c ℓ : ℝ) = d := by
      have : ((c ℓ + bias c : ℕ) : ℝ) = maxc c := by exact_mod_cast hℓ
      push_cast at this
      linarith
    have hℓmem : ℓ ∈ univ.erase m := mem_erase.mpr ⟨hℓm, mem_univ ℓ⟩
    rw [← add_sum_erase _ _ hℓmem, hℓd, sub_self, mul_zero, zero_add]
    have hrest : ∑ h ∈ (univ.erase m).erase ℓ, (c h : ℝ) * (d - c h)
        ≤ d * ((n : ℝ) - maxc c - d) := by
      calc ∑ h ∈ (univ.erase m).erase ℓ, (c h : ℝ) * (d - c h)
          ≤ ∑ h ∈ (univ.erase m).erase ℓ, (c h : ℝ) * d :=
            sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) (c h)])
              (Nat.cast_nonneg _)
        _ = d * ((n : ℝ) - maxc c - d) := by
            rw [← sum_mul, mul_comm, hsum, ← add_sum_erase _ _ hℓmem, hℓd]
            ring
    have hfinal : d * ((n : ℝ) - maxc c - d) ≤ (n : ℝ) ^ 2 / 8 := by
      nlinarith [sq_nonneg ((n : ℝ) - 4 * d)]
    have e : ∀ h ∈ (univ.erase m).erase ℓ,
        (c h : ℝ) * (↑(maxc c) - ↑(bias c) - ↑(c h)) = (c h : ℝ) * (d - c h) := by
      intro h _; rfl
    rw [sum_congr rfl e]
    linarith

/-! ### Lemma 3.2 -/

/-- **Lemma 3.2 (a).** For a plurality color `m`, `μₘ(c) = cₘ (1 + γ(c) + α(c))`. -/
theorem lemma_3_2_a {c : Fin k → ℕ} {n : ℕ} {m : Fin k} (hm : m ∈ argmaxSet c) :
    mu n c m = c m * (1 + gamma n c + alpha n c) := by
  rw [mem_argmaxSet.mp hm]
  unfold mu gamma
  rw [mem_argmaxSet.mp hm]
  ring

/-- **Lemma 3.2 (b).** For every non-plurality color `j`,
`μⱼ(c) = cⱼ (1 + γ(c) + α(c) - (m(c) - cⱼ)/n)`. -/
theorem lemma_3_2_b {c : Fin k → ℕ} {n : ℕ} (hn : 0 < n) (j : Fin k) :
    mu n c j = c j * (1 + gamma n c + alpha n c - ((maxc c : ℝ) - c j) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold mu gamma
  field_simp
  ring

/-- **Lemma 3.2 (c).** If `m` is a plurality color and `ℓ` has the most nodes
among the other colors, `μ_ℓ(c) = c_ℓ (1 + γ(c) + α(c) - s(c)/n)`. -/
theorem lemma_3_2_c {c : Fin k → ℕ} {n : ℕ} (hn : 0 < n) {m ℓ : Fin k}
    (hm : m ∈ argmaxSet c) (hℓm : ℓ ≠ m) (hℓ : c ℓ = (univ.erase m).sup c) :
    mu n c ℓ = c ℓ * (1 + gamma n c + alpha n c - (bias c : ℝ) / n) := by
  -- the maximum over the other colors is exactly `m(c) - s(c)`
  have hcm := mem_argmaxSet.mp hm
  have hk : 2 ≤ k := by
    by_contra h
    exact hℓm (Fin.ext (by omega))
  have hgap : c ℓ + bias c = maxc c := by
    obtain ⟨ℓ', hℓ'm, hℓ'⟩ := exists_add_bias_eq hk hcm
    have h1 : c ℓ' ≤ c ℓ := hℓ ▸ le_sup (mem_erase.mpr ⟨hℓ'm, mem_univ ℓ'⟩)
    have h2 := add_bias_le hcm hℓm
    omega
  rw [lemma_3_2_b hn ℓ]
  congr 2
  have : ((c ℓ + bias c : ℕ) : ℝ) = maxc c := by exact_mod_cast hgap
  push_cast at this
  rw [← this]
  ring

end Plurality
