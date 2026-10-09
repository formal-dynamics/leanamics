import Undecided.LowerBoundArith

/-! # Deterministic bounds on one good round

Every one-round statement of the lower bound is a deterministic consequence of the good event
`Good ℓ m` (`PluralityRound.lean`), at deviation level `ℓ = 3 log n`. The probability of a bad
round is at most `(k + 4) / n³` (`bad_le`, `exp_neg_three_log`).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

lemma cast_maxCount_le {z : Config n k} {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, cnt z i ≤ B) :
    (maxCount z : ℝ) ≤ B := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · haveI : IsEmpty (Fin k) := ⟨fun i => by have := i.isLt; omega⟩
    rw [maxCount, Finset.univ_eq_empty, Finset.sup_empty]
    simpa using hB
  · obtain ⟨m, -, hm⟩ :=
      Finset.exists_mem_eq_sup (univ : Finset (Fin k)) ⟨⟨0, hk⟩, mem_univ _⟩
        (fun i => count z (some i))
    rw [maxCount_def, hm]
    exact h m

lemma sum_cnt_eq (z : Config n k) : ∑ i, cnt z i = n - und z := by
  linarith [und_add_sum z]

lemma sum_sq_le_max_mul (z : Config n k) :
    ∑ i, cnt z i ^ 2 ≤ (maxCount z : ℝ) * (n - und z) := by
  calc ∑ i, cnt z i ^ 2 ≤ ∑ i, (maxCount z : ℝ) * cnt z i := by
        refine sum_le_sum fun i _ => ?_
        have hc : cnt z i ≤ (maxCount z : ℝ) := by
          unfold cnt
          exact_mod_cast count_le_maxCount z i
        have h0 := cnt_nonneg z i
        nlinarith
    _ = (maxCount z : ℝ) * ∑ i, cnt z i := by rw [mul_sum]
    _ = (maxCount z : ℝ) * (n - und z) := by rw [sum_cnt_eq]

lemma sum_sq_ge (z : Config n k) :
    (n - und z) ^ 2 ≤ (k : ℝ) * ∑ i, cnt z i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin k))) (f := fun i => cnt z i)
  rw [card_univ, Fintype.card_fin, sum_cnt_eq] at h
  exact h

lemma sq_pair_ge (q N : ℝ) : N ^ 2 / 2 ≤ q ^ 2 + (N - q) ^ 2 := by
  nlinarith [sq_nonneg (q - N / 2)]

lemma mu_of_und_zero (x : Config n k) (i : Fin k) (hq : und x = 0) (hn : (n : ℝ) ≠ 0) :
    mu x i = cnt x i ^ 2 / n := by
  unfold mu
  rw [hq]
  field_simp
  ring

lemma muU_of_und_zero (x : Config n k) (hq : und x = 0) (hn : (n : ℝ) ≠ 0) :
    muU x = n - (∑ i, cnt x i ^ 2) / n := by
  unfold muU
  rw [hq]
  field_simp
  ring

lemma maxCount_eq_of_plurality (x : Config n k) {m : Fin k}
    (hm : ∀ i, count x (some i) ≤ count x (some m)) :
    maxCount x = count x (some m) :=
  le_antisymm (Finset.sup_le fun i _ => hm i) (count_le_maxCount x m)

/-- A round misses `S` with probability at most `(k + 4) e^{-ℓ}` when every good round lands
in `S`. -/
lemma miss_round_le [NeZero n] {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin k) (x : Config n k)
    (S : Set (Config n k)) (hS : ∀ y, Good ℓ m x y → y ∈ S) :
    miss S 1 x ≤ ((k : ℝ) + 4) * exp (-ℓ) := by
  classical
  unfold miss
  rw [expList_succ (T := 0)]
  simp only [expList_zero, List.foldl_cons, List.foldl_nil]
  exact round_le hℓ m x S hS

lemma k_pos_of_D {D : ℝ} {k : ℕ} (hD : 0 < D) (hk : D ≤ k) : 0 < k := by
  have : (0 : ℝ) < k := lt_of_lt_of_le hD hk
  exact_mod_cast this

/-- `C k ≤ (n / log n)^a` with `1 ≤ C`, `a ≤ 1` and `1 ≤ log n` gives `k ≤ n`. -/
lemma k_le_n_of_range {C a : ℝ} {n k : ℕ} (hC : 1 ≤ C) (ha : a ≤ 1)
    (hlog1 : 1 ≤ log n) (hk : C * k ≤ ((n : ℝ) / log n) ^ a) : k ≤ n := by
  have hlog : 0 < log n := by linarith
  have hn0 : (0 : ℝ) < n := by
    rcases n with _ | n
    · simp at hlog
    · exact_mod_cast Nat.succ_pos n
  have hbase : (1 : ℝ) ≤ (n : ℝ) / log n := by
    rw [le_div_iff₀ hlog]
    have : log n ≤ (n : ℝ) - 1 := log_le_sub_one_of_pos hn0
    linarith
  have hpow : ((n : ℝ) / log n) ^ a ≤ (n : ℝ) / log n := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase ha
  have hCk : C * (k : ℝ) ≤ n := by
    calc C * (k : ℝ) ≤ ((n : ℝ) / log n) ^ a := hk
      _ ≤ (n : ℝ) / log n := hpow
      _ ≤ n := by
          rw [div_le_iff₀ hlog]
          nlinarith
  have hk' : (k : ℝ) ≤ C * (k : ℝ) := by nlinarith
  have : (k : ℝ) ≤ n := by linarith
  exact_mod_cast this

/-- On a good first round from a configuration without undecided nodes, the plurality is at least
`n / (2 R²)`, every colour is at most `2 n / R²`, and the undecided count lies in
`[n (1 - 2/Λ), n (1 - 1/(2Λ))]`. -/
lemma first_of_good {ℓ : ℝ} {m : Fin k} {x y : Config n k}
    (hn : 0 < (n : ℝ)) (hℓ : 0 ≤ ℓ) (hq : count x none = 0)
    (hplur : ∀ i, count x (some i) ≤ count x (some m))
    (hhalf : dev ℓ (mu x m) ≤ mu x m / 2)
    (hdevU : dev ℓ (muU x) ≤ n / (2 * ratioLam x)) :
    Good ℓ m x y →
      (n : ℝ) / (2 * ratioR x ^ 2) ≤ cnt y m ∧
        (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 ∧
        n * (1 - 2 / ratioLam x) ≤ und y ∧
        und y ≤ n * (1 - 1 / (2 * ratioLam x)) := by
  intro hG
  have hn0 : (n : ℝ) ≠ 0 := hn.ne'
  have hund0 : und x = 0 := by
    unfold und
    exact_mod_cast hq
  have hmax := maxCount_eq_of_plurality x hplur
  have hc : cnt x m = (maxCount x : ℝ) := by
    unfold cnt
    rw [hmax]
  have hMpos : (0 : ℝ) < maxCount x := by
    exact_mod_cast maxCount_pos_of_und_zero x hq (by exact_mod_cast hn)
  have hR : ratioR x = n / maxCount x := ratioR_of_und_zero x hq
  have hμ : mu x m = cnt x m ^ 2 / n := mu_of_und_zero x m hund0 hn0
  have hμR : mu x m = n / ratioR x ^ 2 := by
    rw [hμ, hc, hR]
    field_simp
  have hΛ : ratioLam x = (n : ℝ) ^ 2 / ∑ i, cnt x i ^ 2 := by
    simpa [cnt] using ratioLam_of_und_zero x hq (by exact_mod_cast hn)
  have hsumpos : 0 < ∑ i, cnt x i ^ 2 := by
    have : 0 < cnt x m ^ 2 := by
      have : 0 < cnt x m := by simpa [hc] using hMpos
      positivity
    exact lt_of_lt_of_le this (single_le_sum (fun i _ => sq_nonneg _) (mem_univ m))
  have hΛpos : 0 < ratioLam x := by
    rw [hΛ]
    positivity
  have hμU : muU x = n * (1 - 1 / ratioLam x) := by
    rw [muU_of_und_zero x hund0 hn0, hΛ]
    field_simp
  have hμmono : ∀ i, mu x i ≤ mu x m := by
    intro i
    exact mu_le_mu x (by unfold cnt; exact_mod_cast hplur i)
  have hdevmono : ∀ i, dev ℓ (mu x i) ≤ dev ℓ (mu x m) :=
    fun i => dev_mono hℓ (hμmono i)
  have hlow : n / (2 * ratioR x ^ 2) ≤ cnt y m := by
    have hGμ := hG.2.1
    calc n / (2 * ratioR x ^ 2) = mu x m / 2 := by rw [hμR]; ring
      _ ≤ mu x m - dev ℓ (mu x m) := by linarith [hhalf]
      _ ≤ cnt y m := hGμ
  have hup : ∀ i, cnt y i ≤ 2 * n / ratioR x ^ 2 := by
    intro i
    have hGi := hG.1 i
    calc cnt y i ≤ mu x i + dev ℓ (mu x i) := hGi
      _ ≤ mu x m + dev ℓ (mu x m) := by linarith [hμmono i, hdevmono i]
      _ ≤ mu x m + mu x m / 2 := by linarith [hhalf]
      _ ≤ 2 * mu x m := by linarith [mu_nonneg x m]
      _ = 2 * n / ratioR x ^ 2 := by rw [hμR]; ring
  have hmaxy : (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 :=
    cast_maxCount_le (by positivity) hup
  have hdev := hdevU
  have hUlow : n * (1 - 2 / ratioLam x) ≤ und y := by
    have hGq := hG.2.2.2.1
    have hcmp : n * (1 - 2 / ratioLam x) ≤ n * (1 - 1 / ratioLam x) - n / (2 * ratioLam x) := by
      have hΛ := hΛpos.ne'
      have h1 : n * (1 - 2 / ratioLam x) = n * (1 - 1 / ratioLam x) - n / ratioLam x := by
        field_simp [hΛ]
        ring
      have h2 : n / ratioLam x = n / (2 * ratioLam x) + n / (2 * ratioLam x) := by
        field_simp [hΛ]
        ring
      rw [h1, h2]
      have hb : 0 ≤ n / (2 * ratioLam x) := by positivity
      linarith
    calc n * (1 - 2 / ratioLam x) ≤ muU x - n / (2 * ratioLam x) := by
          rw [hμU]
          linarith
      _ ≤ muU x - dev ℓ (muU x) := by linarith
      _ ≤ und y := hGq
  have hUup : und y ≤ n * (1 - 1 / (2 * ratioLam x)) := by
    have hGq := hG.2.2.2.2
    calc und y ≤ muU x + dev ℓ (muU x) := hGq
      _ ≤ muU x + n / (2 * ratioLam x) := by linarith
      _ = n * (1 - 1 / (2 * ratioLam x)) := by rw [hμU]; field_simp; ring
  exact ⟨hlow, hmaxy, hUlow, hUup⟩

/-- On a good round, `Q` cannot fall below `n/2 - 2 γ² n / D` when every colour is at most
`γ n / D` and the deviation is at most `n / D`. -/
lemma not_below_of_good {ℓ γ D : ℝ} {m : Fin k} {y z : Config n k}
    (hn : 0 < (n : ℝ)) (hℓ : 0 ≤ ℓ) (h6 : 6 * ℓ ≤ n) (hγ : 1 ≤ γ) (hD : 0 < D)
    (hmax : (maxCount y : ℝ) ≤ γ * n / D)
    (hdev : 2 * √(ℓ * n) ≤ n / D) (hG : Good ℓ m y z) :
    n / 2 - 2 * γ ^ 2 * n / D ≤ und z := by
  have hsum : ∑ i, cnt y i ^ 2 ≤ γ * n ^ 2 / D := by
    calc ∑ i, cnt y i ^ 2 ≤ (maxCount y : ℝ) * (n - und y) := sum_sq_le_max_mul y
      _ ≤ (maxCount y : ℝ) * n := by
          have := und_nonneg y
          have hle : n - und y ≤ n := by linarith
          have hM : 0 ≤ (maxCount y : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_left hle hM
      _ ≤ (γ * n / D) * n := mul_le_mul_of_nonneg_right hmax (Nat.cast_nonneg n)
      _ = γ * n ^ 2 / D := by ring
  have hmu : n / 2 - γ * n / D ≤ muU y := by
    unfold muU
    rw [le_div_iff₀ hn]
    have hpair := sq_pair_ge (und y) (n : ℝ)
    have hleft : (n / 2) * n ≤ und y ^ 2 + (n - und y) ^ 2 := by
      have : (n : ℝ) ^ 2 / 2 = (n / 2) * n := by ring
      linarith
    have hright : ∑ i, cnt y i ^ 2 ≤ (γ * n / D) * n := by
      have : (γ * n / D) * n = γ * n ^ 2 / D := by ring
      linarith [hsum]
    have hsplit : (n / 2 - γ * n / D) * n = (n / 2) * n - (γ * n / D) * n := by ring
    linarith
  have hgap : γ * n / D + n / D ≤ 2 * γ ^ 2 * n / D := by
    have hpoly : γ + 1 ≤ 2 * γ ^ 2 := by nlinarith
    have heq : γ * n / D + n / D = (γ + 1) * n / D := by ring
    rw [heq, div_le_div_iff₀ hD hD]
    have hmul : (γ + 1) * n ≤ 2 * γ ^ 2 * n := by nlinarith
    exact mul_le_mul_of_nonneg_right hmul hD.le
  have hdev' : dev ℓ (muU y) ≤ 2 * √(ℓ * n) := dev_le hℓ (muU_le_n y hn) h6
  linarith [hG.2.2.2.1]

/-- On a good round from `q = (1 + δ) n / 2` with margin `1 - δ ≥ 1/(2k)`, the undecided count
stays at most `(1 + δ²) n / 2` when the deviation is at most the Cauchy–Schwarz gap. -/
lemma square_of_good {ℓ δ : ℝ} {m : Fin k} {y z : Config n k}
    (hn : 0 < (n : ℝ)) (hk : 0 < k) (hℓ : 0 ≤ ℓ) (h6 : 6 * ℓ ≤ n)
    (hδ : und y = (1 + δ) * n / 2) (hmargin : 1 / (2 * (k : ℝ)) ≤ 1 - δ)
    (hdev : 2 * √(ℓ * n) ≤ n / (16 * (k : ℝ) ^ 3)) (hG : Good ℓ m y z) :
    und z ≤ (1 + δ ^ 2) * n / 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hnq : n - und y = (1 - δ) * n / 2 := by rw [hδ]; ring
  have hmargin' : n / (4 * (k : ℝ)) ≤ n - und y := by
    rw [hnq]
    have hmul : (1 / (2 * (k : ℝ))) * n ≤ (1 - δ) * n :=
      mul_le_mul_of_nonneg_right hmargin hn.le
    have hhalf : (1 / (2 * (k : ℝ))) * n / 2 ≤ (1 - δ) * n / 2 :=
      div_le_div_of_nonneg_right hmul (by norm_num)
    have heq : (1 / (2 * (k : ℝ))) * n / 2 = n / (4 * (k : ℝ)) := by field_simp; ring
    linarith
  have hsq : n ^ 2 / (16 * (k : ℝ) ^ 3) ≤ ∑ i, cnt y i ^ 2 := by
    have hcs := sum_sq_ge y
    have hsum : (n - und y) ^ 2 / k ≤ ∑ i, cnt y i ^ 2 := by
      rw [div_le_iff₀ hk0, mul_comm]
      exact hcs
    have hbase : 0 ≤ n / (4 * (k : ℝ)) := by positivity
    calc n ^ 2 / (16 * (k : ℝ) ^ 3) = (n / (4 * (k : ℝ))) ^ 2 / k := by field_simp; ring
      _ ≤ (n - und y) ^ 2 / k := by
          gcongr
      _ ≤ ∑ i, cnt y i ^ 2 := hsum
  have hgap : 2 * √(ℓ * n) ≤ (∑ i, cnt y i ^ 2) / n := by
    have hsum' : n / (16 * (k : ℝ) ^ 3) ≤ (∑ i, cnt y i ^ 2) / n := by
      rw [le_div_iff₀ hn]
      have heq : n / (16 * (k : ℝ) ^ 3) * n = n ^ 2 / (16 * (k : ℝ) ^ 3) := by ring
      rw [heq]
      exact hsq
    linarith [hdev]
  have hmu : muU y ≤ (1 + δ ^ 2) * n / 2 - (∑ i, cnt y i ^ 2) / n := by
    unfold muU
    rw [hδ]
    have hnq' : (n : ℝ) - (1 + δ) * n / 2 = (1 - δ) * n / 2 := by ring
    rw [hnq']
    have hpair : ((1 + δ) * n / 2) ^ 2 + ((1 - δ) * n / 2) ^ 2 =
        (1 + δ ^ 2) * n ^ 2 / 2 := by ring
    have hdiv : (((1 + δ) * n / 2) ^ 2 + ((1 - δ) * n / 2) ^ 2 - ∑ i, cnt y i ^ 2) / n =
        (1 + δ ^ 2) * n / 2 - (∑ i, cnt y i ^ 2) / n := by
      rw [hpair]
      field_simp
    rw [hdiv]
  have hdev' : dev ℓ (muU y) ≤ 2 * √(ℓ * n) := dev_le hℓ (muU_le_n y hn) h6
  linarith [hG.2.2.2.2]

end Undecided.Plurality
