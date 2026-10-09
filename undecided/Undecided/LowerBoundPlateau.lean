import Undecided.LowerBoundRound

/-! # The `Ω(md(c))` lower bound (UND-3): the plateau (SODA 2015, Lemma 7)

[BCNPS15, Lemma 7] ("Plateau"): let `k ≤ ε (n / log n)^{1/4}`. If at some round
`|q - n/2| ≤ 2γ² n / md(c̄)` and `c_m ≤ γ n / md(c̄)`, then the plurality stays below
`2γ n / md(c̄)` for the next `Ω(md(c̄))` rounds w.h.p.

The proof shows that one round keeps the window `|q - n/2| ≤ 2γ² n / md(c̄)` and multiplies the
plurality by at most `1 + a / md(c̄)` w.h.p.; then `(1 + a / md)^T ≤ 2` for `T = O(md)`.
The one-round step (`plateau_step`) has failure probability `C / n²`, so that it can be iterated
over `T ≤ D / C ≤ n` rounds. Here the monochromatic distance `md(c̄)` of the initial
configuration is a real parameter `D ≤ k` (as `md(c̄) ≤ k`, `md_le_card`).

Corrections (see `FORMALIZATION_DIFFERENCES.md`):
* the bound is kept for **every** colour (`maxCount`): the proof bounds `∑ⱼ cⱼ²` and uses
  `c_m ≥ (n - q)/k`, which hold for the largest colour, not for a fixed colour `m`;
* the growth factor is `1 + (4γ² + 2γ + 1)/D`, not `1 + (2γ(γ + 1) + 1)/D`: from
  `|q - n/2| ≤ 2γ² n / D` the term `2δ/n` in `µ_m = (1 + (2δ + c_m)/n) c_m` is at most `4γ²/D`;
* the lower bound `E[Q' - n/2] ≥ -(4/9) n / D` needs a minor correction (it bounds `∑ⱼ cⱼ²` from
  above by `k ((n - q)/k)²`, which is a lower bound): with `∑ⱼ cⱼ² ≤ maxⱼ cⱼ · (n - q)` one gets
  `E[Q' - n/2] ≥ -(4γ/3) n / D`, which stays inside the window for `γ ≥ 1` (not for an arbitrary
  `γ > 0`: for `γ < 1/2` the window is left in one round from configurations with many equal
  colours).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

lemma miss_one_eq [NeZero n] (S : Set (Config n k)) (x : Config n k) :
    miss S 1 x =
      avg (fun r : Fin n → Fin n => by classical exact if step x r ∈ S then (0 : ℝ) else 1) := by
  classical
  unfold miss
  rw [expList_succ (T := 0)]
  simp only [expList_zero, List.foldl_cons, List.foldl_nil]
  rfl

/-- One good round keeps the plateau window and multiplies every colour by at most
`1 + (4γ² + 2γ + 1) / D`. The numeric hypotheses are the deviation and margin bounds
discharged from `C ≥ 16γ²` in `plateau_step`. -/
lemma plateau_of_good {ℓ γ D B : ℝ} {m : Fin k} {y z : Config n k}
    (hn : 0 < (n : ℝ)) (hℓ : 0 ≤ ℓ) (hγ : 1 ≤ γ) (hD : 0 < D)
    (hBlo : γ * n / D ≤ B) (hBhi : B ≤ 2 * γ * n / D)
    (hwin : |und y - n / 2| ≤ 2 * γ ^ 2 * n / D) (hmax : (maxCount y : ℝ) ≤ B)
    (h6B : 6 * ℓ ≤ 2 * B) (hdevB : 2 * √(2 * ℓ * B) ≤ B / D)
    (h6n : 6 * ℓ ≤ n) (hdevn : 2 * √(ℓ * n) ≤ γ ^ 2 * n / D)
    (hdevThird : 2 * √(ℓ * n) ≤ (2 / 3) * n / D)
    (hD8 : 8 * γ ^ 2 ≤ D) (hthird : n / 2 + 2 * γ ^ 2 * n / D ≤ 2 * n / 3)
    (hfac : 4 * γ ^ 2 + 2 * γ ≤ D) (hG : Good ℓ m y z) :
    (maxCount z : ℝ) ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B ∧
      |und z - n / 2| ≤ 2 * γ ^ 2 * n / D := by
  have hγ0 : 0 ≤ γ := by linarith
  have hB0 : 0 ≤ B :=
    le_trans (div_nonneg (mul_nonneg hγ0 hn.le) hD.le) hBlo
  have hδle : und y - n / 2 ≤ 2 * γ ^ 2 * n / D := by
    rw [abs_le] at hwin
    linarith
  have hup : ∀ i, cnt z i ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B := by
    intro i
    have hcB : cnt y i ≤ B := by
      refine le_trans ?_ hmax
      unfold cnt
      exact_mod_cast count_le_maxCount y i
    have hc0 : 0 ≤ cnt y i := cnt_nonneg y i
    have hq0 : 0 ≤ und y := und_nonneg y
    have hprod : cnt y i * (cnt y i + 2 * und y) ≤ B * (B + 2 * und y) := by
      have hle : cnt y i + 2 * und y ≤ B + 2 * und y := by linarith
      have hnn : 0 ≤ cnt y i + 2 * und y := by linarith
      exact mul_le_mul hcB hle hnn hB0
    have hμle : mu y i ≤ B * (B + 2 * und y) / n := by
      unfold mu
      exact div_le_div_of_nonneg_right hprod hn.le
    have heq : B * (B + 2 * und y) / n =
        B * (1 + (2 * (und y - n / 2) + B) / n) := by
      field_simp
      ring
    have hcoef : (2 * (und y - n / 2) + B) / n ≤ (4 * γ ^ 2 + 2 * γ) / D := by
      have h1 : 2 * (und y - n / 2) / n ≤ 4 * γ ^ 2 / D := by
        have hmul : 2 * (und y - n / 2) ≤ 4 * γ ^ 2 * n / D := by
          have hstep : 2 * (und y - n / 2) ≤ 2 * (2 * γ ^ 2 * n / D) :=
            mul_le_mul_of_nonneg_left hδle (by norm_num)
          have heq2 : 2 * (2 * γ ^ 2 * n / D) = 4 * γ ^ 2 * n / D := by ring
          exact hstep.trans (le_of_eq heq2)
        have hdiv : 2 * (und y - n / 2) / n ≤ (4 * γ ^ 2 * n / D) / n :=
          div_le_div_of_nonneg_right hmul hn.le
        have heq1 : (4 * γ ^ 2 * n / D) / n = 4 * γ ^ 2 / D := by field_simp
        exact hdiv.trans (le_of_eq heq1)
      have h2 : B / n ≤ 2 * γ / D := by
        have hBD : B * D ≤ 2 * γ * n := by
          have := hBhi
          rwa [le_div_iff₀ hD] at this
        rw [div_le_iff₀ hn]
        have heq2 : (2 * γ / D) * n = 2 * γ * n / D := by ring
        rw [heq2, le_div_iff₀ hD]
        exact hBD
      have hadd : (2 * (und y - n / 2) + B) / n =
          2 * (und y - n / 2) / n + B / n := by ring
      rw [hadd]
      have hsplit : (4 * γ ^ 2 + 2 * γ) / D = 4 * γ ^ 2 / D + 2 * γ / D := by ring
      rw [hsplit]
      exact add_le_add h1 h2
    have hμB : mu y i ≤ B * (1 + (4 * γ ^ 2 + 2 * γ) / D) := by
      calc mu y i ≤ B * (1 + (2 * (und y - n / 2) + B) / n) := by linarith [heq]
        _ ≤ B * (1 + (4 * γ ^ 2 + 2 * γ) / D) :=
            mul_le_mul_of_nonneg_left (by linarith) hB0
    have htwo : 1 + (4 * γ ^ 2 + 2 * γ) / D ≤ 2 := by
      have : (4 * γ ^ 2 + 2 * γ) / D ≤ 1 := by
        rwa [div_le_one hD]
      linarith
    have hμ2 : mu y i ≤ 2 * B := by
      calc mu y i ≤ B * (1 + (4 * γ ^ 2 + 2 * γ) / D) := hμB
        _ ≤ B * 2 := mul_le_mul_of_nonneg_left htwo hB0
        _ = 2 * B := by ring
    have hdevi : dev ℓ (mu y i) ≤ 2 * √(2 * ℓ * B) := by
      have hdev := dev_le hℓ hμ2 h6B
      have heqS : ℓ * (2 * B) = 2 * ℓ * B := by ring
      simpa [heqS] using hdev
    have hcnt : cnt z i ≤ mu y i + dev ℓ (mu y i) := hG.1 i
    have hsumB : B * (1 + (4 * γ ^ 2 + 2 * γ) / D) + B / D =
        (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B := by
      field_simp
      ring
    linarith [hdevB]
  have hmaxz : (maxCount z : ℝ) ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B := by
    have hnonneg : 0 ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B := by
      have hnum : 0 ≤ 4 * γ ^ 2 + 2 * γ + 1 := by nlinarith only [hγ0]
      have hdiv : 0 ≤ (4 * γ ^ 2 + 2 * γ + 1) / D := div_nonneg hnum hD.le
      have hone : (0 : ℝ) ≤ 1 := by norm_num
      exact mul_nonneg (add_nonneg hone hdiv) hB0
    exact cast_maxCount_le hnonneg hup
  have hsub := muU_sub_half y (by exact_mod_cast hn)
  have hupExp : muU y - n / 2 ≤ 2 * (und y - n / 2) ^ 2 / n := by
    rw [hsub]
    have hnn : 0 ≤ ∑ j, cnt y j ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have : 2 * (und y - n / 2) ^ 2 - ∑ j, cnt y j ^ 2 ≤ 2 * (und y - n / 2) ^ 2 := by
      linarith only [hnn]
    exact div_le_div_of_nonneg_right this hn.le
  have hbox : 0 ≤ 2 * γ ^ 2 * n / D :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg γ)) hn.le) hD.le
  have hδsq : (und y - n / 2) ^ 2 ≤ (2 * γ ^ 2 * n / D) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hbox]
    exact hwin
  have h8eq : 2 * (2 * γ ^ 2 * n / D) ^ 2 / n = 8 * γ ^ 4 * n / D ^ 2 := by
    field_simp
    ring
  have h8 : 2 * (und y - n / 2) ^ 2 / n ≤ 8 * γ ^ 4 * n / D ^ 2 := by
    have hmul : 2 * (und y - n / 2) ^ 2 ≤ 2 * (2 * γ ^ 2 * n / D) ^ 2 :=
      mul_le_mul_of_nonneg_left hδsq (by norm_num)
    exact (div_le_div_of_nonneg_right hmul hn.le).trans (le_of_eq h8eq)
  have h8le : 8 * γ ^ 4 * n / D ^ 2 ≤ γ ^ 2 * n / D := by
    have hD2 : 0 < D ^ 2 := by positivity
    rw [div_le_div_iff₀ hD2 hD]
    have hcore : 8 * γ ^ 4 * D ≤ γ ^ 2 * D ^ 2 := by
      have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
      calc 8 * γ ^ 4 * D = γ ^ 2 * (8 * γ ^ 2 * D) := by ring
        _ ≤ γ ^ 2 * (D * D) := by
            have : 8 * γ ^ 2 * D ≤ D * D := by nlinarith
            exact mul_le_mul_of_nonneg_left this hγ2
        _ = γ ^ 2 * D ^ 2 := by ring
    have hmul := mul_le_mul_of_nonneg_right hcore hn.le
    calc 8 * γ ^ 4 * n * D = 8 * γ ^ 4 * D * n := by ring
      _ ≤ γ ^ 2 * D ^ 2 * n := hmul
      _ = γ ^ 2 * n * D ^ 2 := by ring
  have hδge : -(2 * γ ^ 2 * n / D) ≤ und y - n / 2 := (abs_le.mp hwin).1
  have hnq : n - und y ≤ 2 * n / 3 := by
    have : n - und y ≤ n / 2 + 2 * γ ^ 2 * n / D := by
      linarith only [hδge]
    exact this.trans hthird
  have hsqle : ∑ j, cnt y j ^ 2 ≤ B * (2 * n / 3) := by
    have hnu : 0 ≤ n - und y := by
      have hsum : 0 ≤ ∑ i, cnt y i := sum_nonneg fun _ _ => cnt_nonneg _ _
      linarith [und_add_sum y]
    calc ∑ j, cnt y j ^ 2 ≤ (maxCount y : ℝ) * (n - und y) := sum_sq_le_max_mul y
      _ ≤ B * (n - und y) := mul_le_mul_of_nonneg_right hmax hnu
      _ ≤ B * (2 * n / 3) := mul_le_mul_of_nonneg_left hnq hB0
  have hsqn : (∑ j, cnt y j ^ 2) / n ≤ (2 / 3) * B := by
    have hdiv : (∑ j, cnt y j ^ 2) / n ≤ (B * (2 * n / 3)) / n :=
      div_le_div_of_nonneg_right hsqle hn.le
    have heqS : (B * (2 * n / 3)) / n = (2 / 3) * B := by field_simp
    exact hdiv.trans (le_of_eq heqS)
  have hlowExp : -(2 / 3) * B ≤ muU y - n / 2 := by
    rw [hsub]
    have hdrop : -(∑ j, cnt y j ^ 2) ≤ 2 * (und y - n / 2) ^ 2 - ∑ j, cnt y j ^ 2 := by
      linarith only [sq_nonneg (und y - n / 2)]
    have hdiv : -(∑ j, cnt y j ^ 2) / n ≤
        (2 * (und y - n / 2) ^ 2 - ∑ j, cnt y j ^ 2) / n :=
      div_le_div_of_nonneg_right hdrop hn.le
    have heqN : -(∑ j, cnt y j ^ 2) / n = -((∑ j, cnt y j ^ 2) / n) := by ring
    have hneg0 : -(2 / 3 * B) ≤ -((∑ j, cnt y j ^ 2) / n) := neg_le_neg hsqn
    have hnegEq : -(2 / 3 * B) = -(2 / 3) * B := by ring
    have hneg : -(2 / 3) * B ≤ -((∑ j, cnt y j ^ 2) / n) := by
      rw [← hnegEq]
      exact hneg0
    exact hneg.trans (by rw [← heqN]; exact hdiv)
  have hBlow : -(4 / 3) * γ * n / D ≤ -(2 / 3) * B := by
    have hmul : (2 / 3) * B ≤ (2 / 3) * (2 * γ * n / D) :=
      mul_le_mul_of_nonneg_left hBhi (by norm_num)
    have heqS : (2 / 3) * (2 * γ * n / D) = (4 / 3) * γ * n / D := by ring
    have hle : (2 / 3) * B ≤ (4 / 3) * γ * n / D := hmul.trans (le_of_eq heqS)
    have hneg : -((4 / 3) * γ * n / D) ≤ -((2 / 3) * B) := neg_le_neg hle
    have hL : -((4 / 3) * γ * n / D) = -(4 / 3) * γ * n / D := by ring
    have hR : -((2 / 3) * B) = -(2 / 3) * B := by ring
    rw [← hL, ← hR]
    exact hneg
  have hdevU : dev ℓ (muU y) ≤ 2 * √(ℓ * n) := dev_le hℓ (muU_le_n y hn) h6n
  have hlow : -(2 * γ ^ 2 * n / D) ≤ und z - n / 2 := by
    have hpoly : (4 / 3) * γ + 2 / 3 ≤ 2 * γ ^ 2 := by nlinarith only [hγ]
    have hsum : 2 * √(ℓ * n) + (4 / 3) * γ * n / D ≤ 2 * γ ^ 2 * n / D := by
      have hleft : 2 * √(ℓ * n) + (4 / 3) * γ * n / D ≤
          (2 / 3) * n / D + (4 / 3) * γ * n / D := by
        linarith only [hdevThird]
      have heqS : (2 / 3) * n / D + (4 / 3) * γ * n / D =
          ((4 / 3) * γ + 2 / 3) * n / D := by ring
      have hright : ((4 / 3) * γ + 2 / 3) * n / D ≤ 2 * γ ^ 2 * n / D := by
        have hmul : ((4 / 3) * γ + 2 / 3) * n ≤ 2 * γ ^ 2 * n := by
          nlinarith only [hpoly, hn]
        exact div_le_div_of_nonneg_right hmul hD.le
      exact hleft.trans (by rw [heqS]; exact hright)
    have hGq := hG.2.2.2.1
    have h1 : muU y - n / 2 - dev ℓ (muU y) ≤ und z - n / 2 := by
      linarith only [hGq]
    have h2 : -(2 / 3) * B - dev ℓ (muU y) ≤ muU y - n / 2 - dev ℓ (muU y) := by
      linarith only [hlowExp]
    have h3 : -(4 / 3) * γ * n / D - dev ℓ (muU y) ≤ -(2 / 3) * B - dev ℓ (muU y) := by
      linarith only [hBlow]
    have h4 : -(4 / 3) * γ * n / D - 2 * √(ℓ * n) ≤
        -(4 / 3) * γ * n / D - dev ℓ (muU y) := by
      linarith only [hdevU]
    have h5 : -(2 * γ ^ 2 * n / D) ≤ -(4 / 3) * γ * n / D - 2 * √(ℓ * n) := by
      have hneg := neg_le_neg hsum
      have heqS : -(2 * √(ℓ * n) + (4 / 3) * γ * n / D) =
          -(4 / 3) * γ * n / D - 2 * √(ℓ * n) := by ring
      exact hneg.trans (le_of_eq heqS)
    exact h5.trans (h4.trans (h3.trans (h2.trans h1)))
  have hhigh : und z - n / 2 ≤ 2 * γ ^ 2 * n / D := by
    have hGq := hG.2.2.2.2
    have h1 : und z - n / 2 ≤ muU y - n / 2 + dev ℓ (muU y) := by
      linarith only [hGq]
    have h2 : muU y - n / 2 + dev ℓ (muU y) ≤
        2 * (und y - n / 2) ^ 2 / n + dev ℓ (muU y) := by
      linarith only [hupExp]
    have h3 : 2 * (und y - n / 2) ^ 2 / n + dev ℓ (muU y) ≤
        8 * γ ^ 4 * n / D ^ 2 + dev ℓ (muU y) := by
      linarith only [h8]
    have h4 : 8 * γ ^ 4 * n / D ^ 2 + dev ℓ (muU y) ≤
        8 * γ ^ 4 * n / D ^ 2 + 2 * √(ℓ * n) := by
      linarith only [hdevU]
    have h5 : 8 * γ ^ 4 * n / D ^ 2 + 2 * √(ℓ * n) ≤
        γ ^ 2 * n / D + γ ^ 2 * n / D := by
      have h5a : 8 * γ ^ 4 * n / D ^ 2 + 2 * √(ℓ * n) ≤
          γ ^ 2 * n / D + 2 * √(ℓ * n) := by
        linarith only [h8le]
      have h5b : γ ^ 2 * n / D + 2 * √(ℓ * n) ≤ γ ^ 2 * n / D + γ ^ 2 * n / D := by
        linarith only [hdevn]
      exact h5a.trans h5b
    have heqS : γ ^ 2 * n / D + γ ^ 2 * n / D = 2 * γ ^ 2 * n / D := by ring
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (le_of_eq heqS)))))
  exact ⟨hmaxz, abs_le.mpr ⟨hlow, hhigh⟩⟩

/-- From `(C D)^4 L ≤ N` and `C ≤ D`, the three scales used by the deviation estimates. -/
lemma plateau_scale {C D L N : ℝ} (hC : 0 < C) (hD : 0 < D) (hL : 0 ≤ L) (hCD : C ≤ D)
    (h : (C * D) ^ 4 * L ≤ N) :
    D ^ 4 * L ≤ N / C ^ 4 ∧ D ^ 3 * L ≤ N / C ^ 5 ∧ D ^ 2 * L ≤ N / C ^ 6 := by
  have h4 : D ^ 4 * L ≤ N / C ^ 4 := by
    rw [le_div_iff₀ (pow_pos hC 4)]
    have heq : D ^ 4 * L * C ^ 4 = (C * D) ^ 4 * L := by ring
    rwa [heq]
  have hmul3 : C * (D ^ 3 * L) ≤ N / C ^ 4 := by
    have hle : C * D ^ 3 ≤ D ^ 4 := by
      calc C * D ^ 3 ≤ D * D ^ 3 := mul_le_mul_of_nonneg_right hCD (by positivity)
        _ = D ^ 4 := by ring
    have heq : C * (D ^ 3 * L) = C * D ^ 3 * L := by ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hle hL).trans h4
  have h3 : D ^ 3 * L ≤ N / C ^ 5 := by
    rw [le_div_iff₀ (pow_pos hC 5)]
    have heq : D ^ 3 * L * C ^ 5 = C * (D ^ 3 * L) * C ^ 4 := by ring
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hmul3 (pow_nonneg hC.le 4)
    have heq2 : N / C ^ 4 * C ^ 4 = N := by field_simp
    exact hmul.trans (le_of_eq heq2)
  have hmul2 : C * (D ^ 2 * L) ≤ N / C ^ 5 := by
    have hle : C * D ^ 2 ≤ D ^ 3 := by
      calc C * D ^ 2 ≤ D * D ^ 2 := mul_le_mul_of_nonneg_right hCD (by positivity)
        _ = D ^ 3 := by ring
    have heq : C * (D ^ 2 * L) = C * D ^ 2 * L := by ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hle hL).trans h3
  have h2 : D ^ 2 * L ≤ N / C ^ 6 := by
    rw [le_div_iff₀ (pow_pos hC 6)]
    have heq : D ^ 2 * L * C ^ 6 = C * (D ^ 2 * L) * C ^ 5 := by ring
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hmul2 (pow_nonneg hC.le 5)
    have heq2 : N / C ^ 5 * C ^ 5 = N := by field_simp
    exact hmul.trans (le_of_eq heq2)
  exact ⟨h4, h3, h2⟩

/-- `C ≥ 16` gives the powers that absorb the deviation coefficients `18`, `24` and `27`. -/
lemma sixteen_pow_bounds {C : ℝ} (h : (16 : ℝ) ≤ C) :
    (18 : ℝ) ≤ C ^ 4 ∧ (24 : ℝ) ≤ C ^ 5 ∧ (27 : ℝ) ≤ C ^ 6 := by
  have h0 : (0 : ℝ) ≤ 16 := by norm_num
  have n4 : (18 : ℝ) ≤ (16 : ℝ) ^ 4 := by norm_num
  have n5 : (24 : ℝ) ≤ (16 : ℝ) ^ 5 := by norm_num
  have n6 : (27 : ℝ) ≤ (16 : ℝ) ^ 6 := by norm_num
  exact ⟨n4.trans (pow_le_pow_left₀ h0 h 4), n5.trans (pow_le_pow_left₀ h0 h 5),
    n6.trans (pow_le_pow_left₀ h0 h 6)⟩

/-- `2 √(2 ℓ B) ≤ B / D` once `8 ℓ D² ≤ B`. -/
lemma colour_dev_le {ℓ B D : ℝ} (hℓ : 0 ≤ ℓ) (hB : 0 < B) (hD : 0 < D)
    (h : 8 * ℓ * D ^ 2 ≤ B) : 2 * √(2 * ℓ * B) ≤ B / D := by
  have hnn : 0 ≤ 2 * ℓ * B := by nlinarith only [hℓ, hB.le]
  have hsq : (2 * √(2 * ℓ * B)) ^ 2 = 8 * ℓ * B := by
    rw [mul_pow, Real.sq_sqrt hnn]
    ring
  have hgoal : (2 * √(2 * ℓ * B)) ^ 2 ≤ (B / D) ^ 2 := by
    rw [hsq]
    have heq : (B / D) ^ 2 = B ^ 2 / D ^ 2 := by ring
    rw [heq, le_div_iff₀ (pow_pos hD 2)]
    have hmul := mul_le_mul_of_nonneg_right h hB.le
    calc 8 * ℓ * B * D ^ 2 = 8 * ℓ * D ^ 2 * B := by ring
      _ ≤ B * B := hmul
      _ = B ^ 2 := by ring
  have hL : 0 ≤ 2 * √(2 * ℓ * B) := mul_nonneg (by norm_num) (sqrt_nonneg _)
  exact (sq_le_sq₀ hL (div_nonneg hB.le hD.le)).mp hgoal

/-- **One round of the plateau** (proof of [BCNPS15, Lemma 7], corrected growth factor). Let
`γ ≥ 1`. There is `C > 0` such that, for every `n` with `log n ≥ C`, every `k` with
`C k ≤ (n / log n)^{1/4}`, every `D` with `C ≤ D ≤ k`, every configuration `y` with
`|q - n/2| ≤ 2γ² n / D` and every `B ∈ [γ n / D, 2γ n / D]` bounding all colours of `y`, after
one round, with probability at least `1 - C / n²`, all colours are at most
`(1 + (4γ² + 2γ + 1)/D) B` and still `|q - n/2| ≤ 2γ² n / D`. -/
theorem plateau_step : ∀ γ : ℝ, 1 ≤ γ → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) → ∀ D : ℝ, C ≤ D → D ≤ k →
    ∀ (y : Config n k) (B : ℝ), γ * n / D ≤ B → B ≤ 2 * γ * n / D →
      |und y - n / 2| ≤ 2 * γ ^ 2 * n / D → (maxCount y : ℝ) ≤ B →
      miss {z | (maxCount z : ℝ) ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B ∧
        |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} 1 y ≤ C / n ^ 2 := by
  intro γ hγ
  refine ⟨16 * γ ^ 2, ?_, ?_⟩
  · have hγ2 : (1 : ℝ) ≤ γ ^ 2 := by nlinarith only [hγ]
    nlinarith
  intro n hL k hk D hCD hDk y B hBlo hBhi hwin hmax
  let C : ℝ := 16 * γ ^ 2
  have hCpos : 0 < C := by
    have hγ2 : (1 : ℝ) ≤ γ ^ 2 := by nlinarith only [hγ]
    nlinarith
  have hγ2 : (1 : ℝ) ≤ γ ^ 2 := by nlinarith only [hγ]
  have h16 : (16 : ℝ) ≤ C := by
    calc (16 : ℝ) = 16 * 1 := by ring
      _ ≤ 16 * γ ^ 2 := mul_le_mul_of_nonneg_left hγ2 (by norm_num)
      _ = C := by ring
  have hlogpos : 0 < log n := log_pos_of_log hCpos hL
  have hlog0 : 0 ≤ log n := hlogpos.le
  have hlog1 : (1 : ℝ) ≤ log n := by linarith
  have hn1 : 1 < n := one_lt_n_of_log hCpos hL
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hD : 0 < D := lt_of_lt_of_le hCpos hCD
  have hkpos : 0 < k := k_pos_of_D hD hDk
  have hk_le : k ≤ n :=
    k_le_n_of_range (by linarith : (1 : ℝ) ≤ C) (by norm_num : (1 : ℝ) / 4 ≤ 1) hlog1 hk
  have hpoly : (C * (k : ℝ)) ^ 4 * log n ≤ n :=
    pow_of_rpow (by norm_num : 0 < 4) (by positivity) hlogpos (Nat.cast_nonneg n) hk
  have hDkR : D ≤ (k : ℝ) := by exact_mod_cast hDk
  have hCD4 : (C * D) ^ 4 * log n ≤ n := by
    have hmul : C * D ≤ C * (k : ℝ) := mul_le_mul_of_nonneg_left hDkR hCpos.le
    have hpow : (C * D) ^ 4 ≤ (C * (k : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg hCpos.le hD.le) hmul 4
    exact (mul_le_mul_of_nonneg_right hpow hlog0).trans hpoly
  obtain ⟨_, hD3, hD2⟩ := plateau_scale hCpos hD hlog0 hCD hCD4
  obtain ⟨h18, h24, h27⟩ := sixteen_pow_bounds h16
  have mul_bound {P X c : ℝ} (hP : 0 < P) (hc0 : 0 ≤ c) (hc : c ≤ P) (hX : X ≤ n / P) :
      c * X ≤ n := by
    have h1 : c * X ≤ c * (n / P) := mul_le_mul_of_nonneg_left hX hc0
    have h2 : c * (n / P) ≤ n := by
      have heq : c * (n / P) = c * n / P := by ring
      rw [heq, div_le_iff₀ hP]
      calc c * n ≤ P * n := mul_le_mul_of_nonneg_right hc hnR.le
        _ = n * P := by ring
    exact h1.trans h2
  have h18n : 18 * log n ≤ n := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hCk : C ≤ C * (k : ℝ) := le_mul_of_one_le_right hCpos.le hk1
    have hpow : C ^ 4 ≤ (C * (k : ℝ)) ^ 4 := pow_le_pow_left₀ hCpos.le hCk 4
    calc 18 * log n ≤ C ^ 4 * log n := mul_le_mul_of_nonneg_right h18 hlog0
      _ ≤ (C * (k : ℝ)) ^ 4 * log n := mul_le_mul_of_nonneg_right hpow hlog0
      _ ≤ n := hpoly
  have h6n : 6 * (3 * log n) ≤ n := by
    calc 6 * (3 * log n) = 18 * log n := by ring
      _ ≤ n := h18n
  have h9 : 9 * D * log n ≤ n := by
    have hD1 : (1 : ℝ) ≤ D := by linarith
    have hDsq : (1 : ℝ) ≤ D ^ 2 := by nlinarith only [hD1]
    have hcmp : D * log n ≤ D ^ 3 * log n := by
      calc D * log n = 1 * (D * log n) := by ring
        _ ≤ D ^ 2 * (D * log n) :=
            mul_le_mul_of_nonneg_right hDsq (mul_nonneg hD.le hlog0)
        _ = D ^ 3 * log n := by ring
    have h9c : (9 : ℝ) ≤ C ^ 5 := by linarith
    calc 9 * D * log n = 9 * (D * log n) := by ring
      _ ≤ 9 * (D ^ 3 * log n) := mul_le_mul_of_nonneg_left hcmp (by norm_num)
      _ ≤ n := mul_bound (pow_pos hCpos 5) (by norm_num) h9c hD3
  have hnD : n / D ≤ B := by
    calc n / D = 1 * (n / D) := by ring
      _ ≤ γ * (n / D) := mul_le_mul_of_nonneg_right hγ (div_nonneg hnR.le hD.le)
      _ = γ * n / D := by ring
      _ ≤ B := hBlo
  have h18B : 18 * log n ≤ 2 * (n / D) := by
    have hmul : 18 * D * log n ≤ 2 * n := by
      calc 18 * D * log n = 2 * (9 * D * log n) := by ring
        _ ≤ 2 * n := mul_le_mul_of_nonneg_left h9 (by norm_num)
    have heq : 2 * (n / D) = 2 * n / D := by ring
    rw [heq, le_div_iff₀ hD]
    calc 18 * log n * D = 18 * D * log n := by ring
      _ ≤ 2 * n := hmul
  have h6B : 6 * (3 * log n) ≤ 2 * B := by
    calc 6 * (3 * log n) = 18 * log n := by ring
      _ ≤ 2 * (n / D) := h18B
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hnD (by norm_num)
  have h24B : 24 * D ^ 2 * log n ≤ B := by
    have hdiv : 24 * D ^ 2 * log n ≤ n / D := by
      rw [le_div_iff₀ hD]
      have heq : 24 * D ^ 2 * log n * D = 24 * (D ^ 3 * log n) := by ring
      rw [heq]
      exact mul_bound (pow_pos hCpos 5) (by norm_num) h24 hD3
    exact hdiv.trans hnD
  have hBpos : 0 < B := lt_of_lt_of_le (div_pos (mul_pos (by linarith : 0 < γ) hnR) hD) hBlo
  have hdevB : 2 * √(2 * (3 * log n) * B) ≤ B / D := by
    have h8 : 8 * (3 * log n) * D ^ 2 ≤ B := by
      have : 8 * (3 * log n) * D ^ 2 = 24 * D ^ 2 * log n := by ring
      linarith
    exact colour_dev_le (by linarith : 0 ≤ 3 * log n) hBpos hD h8
  have h12 : 12 * D ^ 2 * log n ≤ n := by
    have h := mul_bound (P := C ^ 6) (X := D ^ 2 * log n) (c := 12) (pow_pos hCpos 6)
      (by norm_num) (le_trans (by norm_num : (12 : ℝ) ≤ 27) h27) hD2
    rwa [show 12 * D ^ 2 * log n = 12 * (D ^ 2 * log n) by ring]
  have h27n : 27 * D ^ 2 * log n ≤ n := by
    have h := mul_bound (P := C ^ 6) (X := D ^ 2 * log n) (c := 27) (pow_pos hCpos 6)
      (by norm_num) h27 hD2
    rwa [show 27 * D ^ 2 * log n = 27 * (D ^ 2 * log n) by ring]
  have hγ4 : (1 : ℝ) ≤ γ ^ 4 := by
    calc (1 : ℝ) = 1 ^ 2 := by ring
      _ ≤ (γ ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hγ2 2
      _ = γ ^ 4 := by ring
  have hdevn : 2 * √((3 * log n) * n) ≤ γ ^ 2 * n / D := by
    have hs : (2 * D / γ ^ 2) ^ 2 * (3 * log n) ≤ n := by
      have heq : (2 * D / γ ^ 2) ^ 2 * (3 * log n) = 12 * D ^ 2 * log n / γ ^ 4 := by
        field_simp
        ring
      rw [heq]
      have hdiv : 12 * D ^ 2 * log n / γ ^ 4 ≤ 12 * D ^ 2 * log n := by
        rw [div_le_iff₀ (by positivity : 0 < γ ^ 4)]
        exact le_mul_of_one_le_right (by nlinarith [h12]) hγ4
      exact hdiv.trans h12
    have hsqrt :=
      sqrt_ln_le (by linarith : 0 ≤ 3 * log n) (by positivity : 0 < 2 * D / γ ^ 2) hs
    have heq : 2 * (n / (2 * D / γ ^ 2)) = γ ^ 2 * n / D := by
      field_simp
    exact (mul_le_mul_of_nonneg_left hsqrt (by norm_num)).trans (le_of_eq heq)
  have hdevThird : 2 * √((3 * log n) * n) ≤ (2 / 3) * n / D := by
    have hs : (3 * D) ^ 2 * (3 * log n) ≤ n := by
      have heq : (3 * D) ^ 2 * (3 * log n) = 27 * D ^ 2 * log n := by ring
      linarith
    have hsqrt := sqrt_ln_le (by linarith : 0 ≤ 3 * log n) (by positivity : 0 < 3 * D) hs
    have heq : 2 * (n / (3 * D)) = (2 / 3) * n / D := by
      field_simp
    exact (mul_le_mul_of_nonneg_left hsqrt (by norm_num)).trans (le_of_eq heq)
  have hD8 : 8 * γ ^ 2 ≤ D := by
    calc 8 * γ ^ 2 ≤ 16 * γ ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg γ)
      _ = C := by ring
      _ ≤ D := hCD
  have hthird : n / 2 + 2 * γ ^ 2 * n / D ≤ 2 * n / 3 := by
    have h12γ : 12 * γ ^ 2 ≤ D := by
      calc 12 * γ ^ 2 ≤ 16 * γ ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg γ)
        _ = C := by ring
        _ ≤ D := hCD
    have hgap : 2 * γ ^ 2 * n / D ≤ n / 6 := by
      rw [div_le_div_iff₀ hD (by norm_num : (0 : ℝ) < 6)]
      calc 2 * γ ^ 2 * n * 6 = 12 * γ ^ 2 * n := by ring
        _ ≤ D * n := mul_le_mul_of_nonneg_right h12γ hnR.le
        _ = n * D := by ring
    calc n / 2 + 2 * γ ^ 2 * n / D ≤ n / 2 + n / 6 := by linarith only [hgap]
      _ = 2 * n / 3 := by ring
  have hfac : 4 * γ ^ 2 + 2 * γ ≤ D := by
    have h2γ : 2 * γ ≤ 2 * γ ^ 2 := by nlinarith only [hγ]
    calc 4 * γ ^ 2 + 2 * γ ≤ 4 * γ ^ 2 + 2 * γ ^ 2 := by linarith only [h2γ]
      _ = 6 * γ ^ 2 := by ring
      _ ≤ 16 * γ ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg γ)
      _ = C := by ring
      _ ≤ D := hCD
  let m : Fin k := ⟨0, hkpos⟩
  have hS : ∀ z, Good (3 * log n) m y z →
      z ∈ {z | (maxCount z : ℝ) ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B ∧
        |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} := by
    intro z hG
    exact plateau_of_good hnR (by linarith : 0 ≤ 3 * log n) hγ hD hBlo hBhi hwin hmax
      h6B hdevB h6n hdevn hdevThird hD8 hthird hfac hG
  have hmiss := miss_round_le (by linarith : 0 < 3 * log n) m y _ hS
  calc
      miss {z | (maxCount z : ℝ) ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B ∧
          |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} 1 y
        ≤ ((k : ℝ) + 4) * exp (-(3 * log n)) := hmiss
    _ = ((k : ℝ) + 4) / n ^ 3 := by
        rw [exp_neg_three_log hnR]
        ring
    _ ≤ 5 / n ^ 2 := bad_prob_le (by omega) hk_le
    _ ≤ C / n ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hnR 2) (pow_pos hnR 2)]
        exact mul_le_mul_of_nonneg_right (by nlinarith [h16] : (5 : ℝ) ≤ C) (sq_nonneg (n : ℝ))

/-- **Lemma 7 of [BCNPS15]** (plateau). Let `γ ≥ 1`. There is `C > 0` such that, for every `n`
with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/4}`, every `D` with `C ≤ D ≤ k` (the
monochromatic distance of the initial configuration), every configuration `y` with
`|q - n/2| ≤ 2γ² n / D` and all colours at most `γ n / D`, and every `T` with `C T ≤ D`: after
`T` rounds, with probability at least `1 - C / n`, all colours are at most `2γ n / D` and
`|q - n/2| ≤ 2γ² n / D`. -/
theorem plateau : ∀ γ : ℝ, 1 ≤ γ → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) → ∀ D : ℝ, C ≤ D → D ≤ k →
    ∀ y : Config n k, |und y - n / 2| ≤ 2 * γ ^ 2 * n / D → (maxCount y : ℝ) ≤ γ * n / D →
    ∀ T : ℕ, C * T ≤ D →
      miss {z | (maxCount z : ℝ) ≤ 2 * γ * n / D ∧ |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} T y
        ≤ C / n := by
  intro γ hγ
  obtain ⟨C0, hC0, hstep⟩ := plateau_step γ hγ
  refine ⟨C0 + 14 * γ ^ 2, ?_, ?_⟩
  · have : 0 ≤ 14 * γ ^ 2 := by nlinarith only [hγ]
    linarith
  intro n hL k hk D hCD hDk y hwin hmax T hT
  let C : ℝ := C0 + 14 * γ ^ 2
  have hγ2 : (1 : ℝ) ≤ γ ^ 2 := by nlinarith only [hγ]
  have hCpos : 0 < C := by
    have : 0 ≤ 14 * γ ^ 2 := by nlinarith only [hγ]
    linarith
  have hCge : 14 * γ ^ 2 ≤ C := by linarith
  have hC1 : (1 : ℝ) ≤ C := by
    calc (1 : ℝ) ≤ 14 * 1 := by norm_num
      _ ≤ 14 * γ ^ 2 := mul_le_mul_of_nonneg_left hγ2 (by norm_num)
      _ ≤ C := hCge
  have hlog1 : (1 : ℝ) ≤ log n := by linarith
  have hn1 : 1 < n := one_lt_n_of_log hCpos hL
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hD : 0 < D := lt_of_lt_of_le hCpos hCD
  have hC0le : C0 ≤ C := by linarith
  have hC0D : C0 ≤ D := by linarith
  have hlog0 : C0 ≤ log n := by linarith
  have hk0 : C0 * (k : ℝ) ≤ ((n : ℝ) / log n) ^ ((1 : ℝ) / 4) := by
    calc C0 * (k : ℝ) ≤ C * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hC0le (Nat.cast_nonneg k)
      _ ≤ ((n : ℝ) / log n) ^ ((1 : ℝ) / 4) := hk
  let a : ℝ := 4 * γ ^ 2 + 2 * γ + 1
  have ha0 : 0 ≤ a := by nlinarith only [hγ]
  have ha : a ≤ 7 * γ ^ 2 := by
    have h2γ : 2 * γ ≤ 2 * γ ^ 2 := by nlinarith only [hγ]
    calc a = 4 * γ ^ 2 + 2 * γ + 1 := rfl
      _ ≤ 4 * γ ^ 2 + 2 * γ ^ 2 + γ ^ 2 := by linarith only [h2γ, hγ2]
      _ = 7 * γ ^ 2 := by ring
  have haC : a / C ≤ 1 / 2 := by
    have ha2 : a ≤ C / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc a * 2 ≤ (7 * γ ^ 2) * 2 := mul_le_mul_of_nonneg_right ha (by norm_num)
        _ = 14 * γ ^ 2 := by ring
        _ ≤ C := hCge
    have hdiv : a / C ≤ (C / 2) / C := div_le_div_of_nonneg_right ha2 hCpos.le
    have heq : (C / 2) / C = 1 / 2 := by field_simp
    exact hdiv.trans (le_of_eq heq)
  let G : ℕ → Set (Config n k) := fun t =>
    {z | (maxCount z : ℝ) ≤ (γ * n / D) * (1 + a / D) ^ t ∧
      |und z - n / 2| ≤ 2 * γ ^ 2 * n / D}
  have hone : (1 : ℝ) ≤ 1 + a / D := by
    have : 0 ≤ a / D := div_nonneg ha0 hD.le
    linarith
  have hpow_le : ∀ t : ℕ, t ≤ T → (1 + a / D) ^ t ≤ 2 := by
    intro t ht
    have hpow := pow_one_add_le_exp (div_nonneg ha0 hD.le) t
    have heq : (a / D) * (t : ℝ) = a * (t : ℝ) / D := by ring
    have hsmall : a * (t : ℝ) / D ≤ 1 / 2 := by
      have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
      have hTdiv : (T : ℝ) / D ≤ 1 / C := by
        rw [div_le_div_iff₀ hD hCpos]
        calc (T : ℝ) * C = C * (T : ℝ) := by ring
          _ ≤ D := hT
          _ = 1 * D := by ring
      calc a * (t : ℝ) / D ≤ a * (T : ℝ) / D :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htT ha0) hD.le
        _ = a * ((T : ℝ) / D) := by ring
        _ ≤ a * (1 / C) := mul_le_mul_of_nonneg_left hTdiv ha0
        _ = a / C := by ring
        _ ≤ 1 / 2 := haC
    calc (1 + a / D) ^ t ≤ exp ((a / D) * (t : ℝ)) := hpow
      _ = exp (a * (t : ℝ) / D) := by rw [heq]
      _ ≤ exp (1 / 2) := exp_le_exp.mpr hsmall
      _ ≤ 2 := exp_half_le_two
  have hy0 : y ∈ G 0 := by
    refine ⟨?_, hwin⟩
    rw [pow_zero, mul_one]
    exact hmax
  have hp : 0 ≤ C0 / n ^ 2 := div_nonneg hC0.le (sq_nonneg _)
  have hnn0 : 0 ≤ γ * n / D := div_nonneg (mul_nonneg (by linarith) hnR.le) hD.le
  have hescape : miss (G T) T y ≤ T * (C0 / n ^ 2) := by
    refine expList_escape step hp T G y hy0 ?_
    intro t ht z hz
    have htT : t ≤ T := le_of_lt ht
    let Bt : ℝ := (γ * n / D) * (1 + a / D) ^ t
    have hpowg : (1 : ℝ) ≤ (1 + a / D) ^ t := one_le_pow₀ hone
    have hBlo_t : γ * n / D ≤ Bt := by
      calc γ * n / D = (γ * n / D) * 1 := by ring
        _ ≤ (γ * n / D) * (1 + a / D) ^ t := mul_le_mul_of_nonneg_left hpowg hnn0
    have hBhi_t : Bt ≤ 2 * γ * n / D := by
      calc Bt ≤ (γ * n / D) * 2 := mul_le_mul_of_nonneg_left (hpow_le t htT) hnn0
        _ = 2 * γ * n / D := by ring
    have hsub : {w | (maxCount w : ℝ) ≤ (1 + a / D) * Bt ∧
        |und w - n / 2| ≤ 2 * γ ^ 2 * n / D} ⊆ G (t + 1) := by
      intro w hw
      refine ⟨?_, hw.2⟩
      calc (maxCount w : ℝ) ≤ (1 + a / D) * Bt := hw.1
        _ = (γ * n / D) * (1 + a / D) ^ (t + 1) := by
            rw [pow_succ]
            ring
    rw [← miss_one_eq]
    calc miss (G (t + 1)) 1 z ≤
          miss {w | (maxCount w : ℝ) ≤ (1 + a / D) * Bt ∧
            |und w - n / 2| ≤ 2 * γ ^ 2 * n / D} 1 z := miss_mono hsub 1 z
      _ ≤ C0 / n ^ 2 :=
          hstep n hlog0 k hk0 D hC0D hDk z Bt hBlo_t hBhi_t hz.2 hz.1
  have hsubT : G T ⊆ {z | (maxCount z : ℝ) ≤ 2 * γ * n / D ∧
      |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} := by
    intro z hz
    refine ⟨?_, hz.2⟩
    calc (maxCount z : ℝ) ≤ (γ * n / D) * (1 + a / D) ^ T := hz.1
      _ ≤ (γ * n / D) * 2 := mul_le_mul_of_nonneg_left (hpow_le T le_rfl) hnn0
      _ = 2 * γ * n / D := by ring
  have hTle : (T : ℝ) ≤ n := by
    have hTD : (T : ℝ) ≤ D := by
      exact (le_mul_of_one_le_left (Nat.cast_nonneg T) hC1).trans hT
    have hk_le : k ≤ n :=
      k_le_n_of_range hC1 (by norm_num : (1 : ℝ) / 4 ≤ 1) hlog1 hk
    exact (hTD.trans (by exact_mod_cast hDk)).trans (by exact_mod_cast hk_le)
  have hnum : T * (C0 / n ^ 2) ≤ C / n := by
    calc (T : ℝ) * (C0 / n ^ 2) ≤ n * (C0 / n ^ 2) :=
          mul_le_mul_of_nonneg_right hTle hp
      _ = C0 / n := by field_simp
      _ ≤ C / n := div_le_div_of_nonneg_right hC0le hnR.le
  calc miss {z | (maxCount z : ℝ) ≤ 2 * γ * n / D ∧
        |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} T y
      ≤ miss (G T) T y := miss_mono hsubT T y
    _ ≤ T * (C0 / n ^ 2) := hescape
    _ ≤ C / n := hnum

end Undecided.Plurality
