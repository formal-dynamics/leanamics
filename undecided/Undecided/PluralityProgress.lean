import Undecided.PluralitySteps

/-! # Progress of the `k`-colour dynamics in one good round (UND-3)

* `phi_step`: from `Inv` with `Φ = µ_m ≥ φ`, outside the final set `Fpsi`, a good round
  multiplies `Φ` by at least `1 + κ/(8000B)`. By `mu_add_two_muU`,
  `µ_m + 2µ_q = n + (n - c - 2q)²/n + 2W/n` with `W ≥ κcS`; if `Φ < n/(8(1 + B))` the square is
  at least `n/4` (`sq_gap_of_small`), otherwise the right-hand side exceeds `n(1 + κ/(4000B))`
  (`gap_nonfinal`); then `phi_next`. This is the paper's plurality drift (Lemma 1) and minimal
  drift (Lemma 9) in one potential.
* `fpsi_step`: the final set `Fpsi` is kept by a good round.
* `first_step`: the first round from a configuration without undecided nodes in which every
  other colour has at most `θ c_m` nodes: `µᵢ = cᵢ²/n ≤ θ²µ_m` (the ratios square, as in the
  paper's Lemma 3) and `µ_S = (md - 1) µ_m` (the paper's Lemma 4), so a good round enters
  `Inv ℓ θ (2 md) m` with `Φ ≥ φ`.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ} {ℓ θ B φ : ℝ} {m : Fin k} {x y : Config n k}

lemma mu_next (y : Config n k) (m : Fin k) :
    mu y m = cnt y m * (cnt y m + 2 * und y) / n := rfl

lemma cnt_und_oth (x : Config n k) (m : Fin k) : cnt x m + und x + oth x m = n := by
  unfold oth; ring

lemma cnt_le_n (x : Config n k) (m : Fin k) : cnt x m ≤ n := by
  linarith [cnt_add_und_le x m, und_nonneg x]

/-- After a good round the undecided count is at least `µ_q - 2√(ℓn)`. -/
lemma und_next_ge (hn : (0 : ℝ) < n) (hℓ : 0 ≤ ℓ) (h6 : 6 * ℓ ≤ n) (hG : Good ℓ m x y) :
    muU x - 2 * √(ℓ * n) ≤ und y := by
  have := dev_le hℓ (muU_le_n x hn) h6
  linarith [hG.2.2.2.1]

/-- `√(ℓn) ≤ n/s` from `s²ℓ ≤ n`. -/
lemma sqrt_ln_le {ℓ s : ℝ} (hℓ : 0 ≤ ℓ) (hs : 0 < s) (h : s ^ 2 * ℓ ≤ n) :
    √(ℓ * n) ≤ n / s :=
  sqrt_le_div hℓ hs h

/-- **Growth of `Φ`** outside the final set. -/
theorem phi_step (H : Hyp n ℓ θ B φ) (hx : x ∈ Inv ℓ θ B m) (hφ : φ ≤ mu x m)
    (hF : x ∉ Fpsi m) (hG : Good ℓ m x y) :
    (1 + (1 - θ) / (4000 * B) / 2) * mu x m ≤ mu y m := by
  have hn := H.hn
  have hℓ := H.hℓ
  have hB := H.hB
  have hκ := H.kappa_pos
  have hθ0 := H.hθ0
  have hc := H.cnt_pos hφ
  have hμ0 := mu_nonneg x m
  have hμ1 := H.mu_big_one hφ
  have hμn := mu_le_n x m hn
  have hq0 := und_nonneg x
  have hS0 := oth_nonneg x m
  have hSB := inv_oth_le hx hB
  have hsum := cnt_und_oth x m
  have hW := W_ge x m (fun j hj => inv_col_le hx hj)
  have hid := mu_add_two_muU x m hn
  have hC' := H.cnt_next hφ hG
  have h6 : 6 * ℓ ≤ n := by linarith [H.h5]
  have hQ' := und_next_ge hn hℓ.le h6 hG
  have hsμ := sqrt_nonneg (ℓ * mu x m)
  have hsn := sqrt_nonneg (ℓ * n)
  set η₀ := (1 - θ) / (4000 * B) with hη₀
  have hη₀0 : 0 < η₀ := by positivity
  have hη₀1 : η₀ ≤ 1 / 4000 := by
    rw [hη₀, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set W := cnt x m * (n - und x) - ∑ j, cnt x j ^ 2 with hWdef
  have hW0 : 0 ≤ W := le_trans (by positivity) hW
  rw [mu_next y m]
  by_cases hsmall : mu x m < n / (8 * (1 + B))
  · -- small `Φ`: `(n - c - 2q)² ≥ n²/4`
    have hgap := sq_gap_of_small hn hc.le hq0 hS0 (by linarith) (by linarith) hSB hsmall
    have hsum' : (n : ℝ) * (1 + 1 / 4) ≤ mu x m + 2 * muU x := by
      rw [hid]
      have h1 : (n : ℝ) / 4 ≤ (n - cnt x m - 2 * und x) ^ 2 / n := by
        rw [le_div_iff₀ hn]; nlinarith
      have h2 : 0 ≤ 2 * W / n := by positivity
      linarith
    have ha : 2 * √(ℓ * mu x m) ≤ 1 / 16 * mu x m := by
      have := sqrt_le_div (μ := mu x m) hℓ.le (by norm_num : (0 : ℝ) < 32) (by linarith)
      linarith
    have hb : 6 * √(ℓ * n) ≤ 1 / 16 * n := by
      have := sqrt_ln_le hℓ.le (by norm_num : (0 : ℝ) < 96) (by linarith [H.h5])
      linarith
    have := phi_next hn hℓ.le hμ0 hμn hC' hQ' hsum' ha hb (by norm_num) (by norm_num)
    have hlam : (1 + η₀ / 2) * mu x m ≤ (1 - 1 / 16) * (1 + 1 / 4 - 1 / 16) * mu x m := by
      apply mul_le_mul_of_nonneg_right _ hμ0
      linarith
    linarith
  · -- large `Φ` outside the final set: `η ≥ η₀`
    replace hsmall := not_lt.mp hsmall
    have hnf : (n : ℝ) / 10 < 4 * oth x m + und x := by
      by_contra h
      exact hF (not_lt.mp h)
    have hgap := gap_nonfinal hn hc.le hS0 hB hκ (by linarith) hsum hSB hW hnf
    have hsum' : (n : ℝ) * (1 + η₀) ≤ mu x m + 2 * muU x := by
      rw [hid]
      have h1 : η₀ * n ≤ ((n - cnt x m - 2 * und x) ^ 2 + 2 * W) / n := by
        rw [le_div_iff₀ hn]
        have e : η₀ * n * n = (1 - θ) * n ^ 2 / (4000 * B) := by rw [hη₀]; ring
        rw [e, div_le_iff₀ (by positivity)]
        linarith
      have e : ((n - cnt x m - 2 * und x) ^ 2 + 2 * W) / n =
          (n - cnt x m - 2 * und x) ^ 2 / n + 2 * W / n := by ring
      linarith
    have ha : 2 * √(ℓ * mu x m) ≤ η₀ / 8 * mu x m := by
      have hs : (16 / η₀) ^ 2 * ℓ ≤ mu x m := by
        have e : 16 / η₀ = 16 * (4000 * B) / (1 - θ) := by rw [hη₀]; field_simp
        rw [e]
        exact H.h3.trans hsmall
      have := sqrt_le_div hℓ.le (by positivity) hs
      have e2 : mu x m / (16 / η₀) = η₀ / 16 * mu x m := by field_simp
      linarith
    have hb : 6 * √(ℓ * n) ≤ η₀ / 8 * n := by
      have hs : (48 / η₀) ^ 2 * ℓ ≤ n := by
        have e : 48 / η₀ = 48 * (4000 * B) / (1 - θ) := by rw [hη₀]; field_simp
        rw [e]
        exact H.h4
      have := sqrt_ln_le hℓ.le (by positivity) hs
      have e2 : (n : ℝ) / (48 / η₀) = η₀ / 48 * n := by field_simp
      linarith
    have := phi_next hn hℓ.le hμ0 hμn hC' hQ' hsum' ha hb (by linarith) (by linarith)
    have hlam : (1 + η₀ / 2) * mu x m ≤ (1 - η₀ / 8) * (1 + η₀ - η₀ / 8) * mu x m := by
      apply mul_le_mul_of_nonneg_right _ hμ0
      nlinarith
    linarith

/-- **The final set is kept** by a good round. -/
theorem fpsi_step (hn : (0 : ℝ) < n) (hℓ : 0 ≤ ℓ) (h5 : 160000 * ℓ ≤ n) (hx : x ∈ Fpsi m)
    (hG : Good ℓ m x y) : y ∈ Fpsi m := by
  have h6 : 6 * ℓ ≤ n := by linarith
  have hS' : oth y m ≤ muS x m + 2 * √(ℓ * n) := by
    have := dev_le hℓ (muS_le_n x m hn) h6
    linarith [hG.2.2.1]
  have hQ' : und y ≤ muU x + 2 * √(ℓ * n) := by
    have := dev_le hℓ (muU_le_n x hn) h6
    linarith [hG.2.2.2.2]
  have hexp := fpsi_expect hn (cnt_le_n x m) (oth_nonneg x m) (und_nonneg x) (muS_le x m)
    (muU_le x m) hx
  have hdev : 10 * √(ℓ * n) ≤ n / 40 := by
    have := sqrt_ln_le hℓ (by norm_num : (0 : ℝ) < 400) (by linarith)
    linarith
  exact fpsi_keep hS' hQ' hexp hx hdev

/-- With no undecided nodes, `µ_S = (md - 1) µ_m` when `m` is a plurality colour. -/
lemma muS_first (hq : und x = 0) (hplur : ∀ i, cnt x i ≤ cnt x m) (hc : 0 < cnt x m) :
    muS x m = (md x - 1) * mu x m := by
  have hmd : md x = ∑ i, (cnt x i / cnt x m) ^ 2 := by
    rw [md_eq_of_plurality x (m := m) (fun i => by
      have := hplur i; unfold cnt at this; exact_mod_cast this)]
    rfl
  have hsq : ∑ i, cnt x i ^ 2 = md x * cnt x m ^ 2 := by
    rw [hmd, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    field_simp
  rw [muS_eq_sum]
  have e : ∀ j, mu x j = cnt x j ^ 2 / n := fun j => by unfold mu; rw [hq]; ring
  simp_rw [e]
  rw [← sum_div]
  rw [← sum_erase_add _ _ (mem_univ m)] at hsq
  have h2 : ∑ j ∈ univ.erase m, cnt x j ^ 2 = md x * cnt x m ^ 2 - cnt x m ^ 2 := by
    linarith
  rw [h2]
  ring

/-- **The first round.** From a configuration without undecided nodes in which every other
colour has at most `θ c_m` nodes and `µ_m ≥ 2φ`, a good round enters `Inv ℓ θ B m` with
`Φ ≥ φ`, where `B = 2 md(x)`. -/
theorem first_step (H : Hyp n ℓ θ B φ) (hq : und x = 0)
    (hθx : ∀ i, i ≠ m → cnt x i ≤ θ * cnt x m) (hmd : B = 2 * md x) (hφ : 2 * φ ≤ mu x m)
    (hG : Good ℓ m x y) : y ∈ Inv ℓ θ B m ∧ φ ≤ mu y m := by
  have hn := H.hn
  have hℓ := H.hℓ
  have hθ0 := H.hθ0
  have hθ1 := H.hθ1
  have hκ := H.kappa_pos
  have hB := H.hB
  have hφ0 : 0 ≤ φ := by
    by_contra h
    have : θ ^ 2 * (1 - θ) ^ 2 * φ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_le.mp h).le
    linarith [H.h1]
  have hφ' : φ ≤ mu x m := by linarith
  have hc := H.cnt_pos hφ'
  have hμ0 := mu_nonneg x m
  have hμ1 := H.mu_big_one hφ'
  have hμθ := H.mu_big_θ hφ'
  have hμκ := H.mu_big hφ'
  have hC' := H.cnt_next hφ' hG
  have hsμ := sqrt_nonneg (ℓ * mu x m)
  have hμsq : mu x m = cnt x m ^ 2 / n := by unfold mu; rw [hq]; ring
  have hplur : ∀ i, cnt x i ≤ cnt x m := fun i => by
    by_cases hi : i = m
    · rw [hi]
    · have := hθx i hi
      nlinarith
  have hz : √(ℓ * mu x m) ≤ mu x m / 32 := sqrt_le_div hℓ.le (by norm_num) (by linarith)
  refine ⟨⟨fun i hi => ?_, ?_⟩, ?_⟩
  · -- a colour `i ≠ m`: `µᵢ = cᵢ²/n ≤ θ² µ_m`
    have hci := hθx i hi
    have hci0 := cnt_nonneg x i
    have hμi : mu x i ≤ θ ^ 2 * mu x m := by
      have e : mu x i = cnt x i ^ 2 / n := by unfold mu; rw [hq]; ring
      rw [e, hμsq, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hn.le
      have := mul_le_mul hci hci hci0 (by positivity)
      nlinarith
    have hX' : cnt y i ≤ mu x i + 2 * √(ℓ * mu x m) := by
      have := dev_le hℓ.le (mu_le_mu x (hplur i)) (by linarith)
      linarith [hG.1 i]
    have hzθ : √(ℓ * mu x m) ≤ mu x m / (32 / (θ * (1 - θ))) :=
      sqrt_le_div hℓ.le (by positivity) (by rw [div_pow]; field_simp; nlinarith)
    have e : mu x m / (32 / (θ * (1 - θ))) = θ * (1 - θ) * mu x m / 32 := by field_simp
    rw [e] at hzθ
    refine thr_step hℓ.le hθ0 (by norm_num) (by linarith) (by linarith) hC' ?_
    refine key_ratio hX' hμi ?_
    have h16 : (2 * θ + 12 + 2) * √(ℓ * mu x m) ≤ 16 * √(ℓ * mu x m) :=
      mul_le_mul_of_nonneg_right (by linarith) hsμ
    have : 0 ≤ θ * (1 - θ) * mu x m := by positivity
    nlinarith
  · -- the other colours: `µ_S = (md - 1) µ_m`
    have hmd1 : 1 ≤ md x := one_le_md x ⟨m, by
      have := hc; unfold cnt at this; exact_mod_cast this⟩
    have hμS := muS_first hq hplur hc
    have hμSB : muS x m ≤ B * mu x m := by
      rw [hμS, hmd]
      have := mul_le_mul_of_nonneg_right (by linarith : md x - 1 ≤ 2 * md x) hμ0
      linarith
    have hX' : oth y m ≤ muS x m + 2 * B * √(ℓ * mu x m) := by
      have h6 : 6 * ℓ ≤ B * mu x m := by nlinarith
      have h7 := dev_le hℓ.le hμSB h6
      have h8 : √(ℓ * (B * mu x m)) ≤ B * √(ℓ * mu x m) := by
        rw [show ℓ * (B * mu x m) = B * (ℓ * mu x m) by ring]
        exact sqrt_mul_le_mul_sqrt hB
      linarith [hG.2.2.1]
    refine thr_step hℓ.le (by linarith) (by positivity) (by linarith) ?_ hC' ?_
    · have : (12 * B) ^ 2 * ℓ = B ^ 2 * (144 * ℓ) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by linarith : 144 * ℓ ≤ 2 * mu x m) (sq_nonneg B)
      linarith
    · refine key_ratio (r := md x - 1) hX' hμS.le ?_
      rw [hmd]
      have : (2 * (2 * md x) + 12 * (2 * md x) + 2 * (2 * md x)) * √(ℓ * mu x m) =
          md x * (32 * √(ℓ * mu x m)) := by ring
      rw [this]
      have h32 : 32 * √(ℓ * mu x m) ≤ mu x m := by linarith
      have := mul_le_mul_of_nonneg_left h32 (by linarith : 0 ≤ md x)
      nlinarith
  · -- `Φ` after the first round
    have h6 : 6 * ℓ ≤ n := by linarith [H.h5]
    have hQ' := und_next_ge hn hℓ.le h6 hG
    have hW := W_ge x m (θ := 1) (fun j _ => by linarith [hplur j])
    have hsum' : (n : ℝ) * (1 + 0) ≤ mu x m + 2 * muU x := by
      rw [mu_add_two_muU x m hn]
      have h1 : 0 ≤ (n - cnt x m - 2 * und x) ^ 2 / n := by positivity
      have h2 : 0 ≤ 2 * (cnt x m * (n - und x) - ∑ j, cnt x j ^ 2) / n := by
        apply div_nonneg _ hn.le
        have : 0 ≤ (1 - 1) * cnt x m * oth x m := by norm_num
        linarith
      linarith
    have ha : 2 * √(ℓ * mu x m) ≤ 1 / 16 * mu x m := by linarith
    have hb : 6 * √(ℓ * n) ≤ 1 / 16 * n := by
      have := sqrt_ln_le hℓ.le (by norm_num : (0 : ℝ) < 96) (by linarith [H.h5])
      linarith
    have := phi_next hn hℓ.le hμ0 (mu_le_n x m hn) hC' hQ' hsum' ha hb (by norm_num)
      (by norm_num)
    rw [mu_next y m]
    nlinarith

end Undecided.Plurality
