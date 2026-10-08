import Median.AdversaryMany

/-! # Almost stable consensus against an adaptive adversary

Doerr, Goldberg, Minder, Sauerwald and Scheideler, *Stabilizing consensus with the power of two
choices* (2009 version: Theorems 2, 3 and 10; SPAA 2011: Theorem 1.1). Against an adversary that
knows the history and recolours at most `F ≤ √n / C` nodes per round, the median rule reaches
almost stable consensus within `O(log n)` rounds with high probability: from round
`T₀ = ⌈C log n⌉` on, all but `C (F + log n)` nodes hold the same value, and keep holding it for
`H` more rounds, except with probability at most `(C log n + H)/n²` per threshold (pair of
consecutive legal values).

* `binary_almost_stable_of_isAdvRun`, `binary_almost_stable`: two values (2-Choices), from any
  configuration;
* `median_almost_stable`: any number `m` of legal values, the adversary writing legal values
  only; the failure probability is at most `(m - 1)` times the binary one.
-/

namespace Median
open Finset Dynamics

variable {α : Type*} [LinearOrder α]

/-- A run against a bounded adversary is a perturbed run of the median rule. -/
theorem runAdv_isAdvRun {n : ℕ} {F : ℕ} {A : Adversary n α} (hA : A.Bounded F)
    (x : Config n α) : IsAdvRun F x (runAdv A x) :=
  ⟨rfl, fun l r => by rw [runAdv_append_singleton]; exact hA _ _⟩

/-- **2-Choices against an adaptive adversary, perturbed-run form.** From any binary
configuration `x`, for any run `P` of the median rule perturbed by at most `F ≤ √n / C`
recolourings per round, all but at most `C (F + log n)` nodes hold a common value `b` at every
time from `⌈C log n⌉` to `⌈C log n⌉ + H`, except with probability at most `(C log n + H)/n²`. -/
theorem binary_almost_stable_of_isAdvRun : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n],
    C ≤ Real.log n → ∀ F : ℕ, C * F ≤ √(n : ℝ) →
    ∀ (x : Config n Bool) (P : List (Round n) → Config n Bool), IsAdvRun F x P → ∀ H : ℕ,
      expList (Round n) (⌈C * Real.log n⌉₊ + H)
          (notAlmostStable (C * (F + Real.log n)) ⌈C * Real.log n⌉₊ H P)
        ≤ (C * Real.log n + H) / (n : ℝ) ^ 2 := by
  refine ⟨2 ^ 20, by norm_num, fun n _ hL F hF x P hP H => ?_⟩
  have hL0 : 0 ≤ Real.log n := by linarith
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg F
  have hF' : 1024 * (F : ℝ) ≤ √(n : ℝ) := by linarith
  refine le_trans (expList_le_expList fun l => notAlmostStable_mono ?_ _ _ _ l)
    (adv_binary_window hL hF' hP H)
  exact max_le (by nlinarith) (by nlinarith)

/-- **2-Choices against an adaptive adversary** (the paper's two-value case: Theorem 10 of the
2009 version, `O(√n)`-bounded adversary). From any binary configuration, against any adversary
that knows the history and recolours at most `F ≤ √n / C` nodes per round, all but at most
`C (F + log n)` nodes hold a common value `b` at every time from `⌈C log n⌉` to `⌈C log n⌉ + H`,
except with probability at most `(C log n + H)/n²`. -/
theorem binary_almost_stable : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ F : ℕ, C * F ≤ √(n : ℝ) → ∀ A : Adversary n Bool, A.Bounded F →
    ∀ (x : Config n Bool) (H : ℕ),
      expList (Round n) (⌈C * Real.log n⌉₊ + H)
          (notAlmostStable (C * (F + Real.log n)) ⌈C * Real.log n⌉₊ H (runAdv A x))
        ≤ (C * Real.log n + H) / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := binary_almost_stable_of_isAdvRun
  exact ⟨C, hC, fun n _ hL F hF A hA x H => h n hL F hF x _ (runAdv_isAdvRun hA x) H⟩

/-- **Almost stable consensus against an adaptive adversary** (the paper's main theorem with
adversary: Theorem 1.1 of SPAA 2011, Theorems 2, 3 and 20 of the 2009 version). Let `S` be a set
of `m` legal values containing the values of the configuration `x` (in the paper, the initial
values; a larger `S` also covers a corruption before the first round). Against any adversary
that knows the history, recolours at most `F ≤ √n / C` nodes per round and only writes values
of `S`, all but at most `C (F + log n)` nodes hold a common value at every time from
`⌈C log n⌉` to `⌈C log n⌉ + H`, except with probability at most `(m - 1) (C log n + H)/n²`. -/
theorem median_almost_stable : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ F : ℕ, C * F ≤ √(n : ℝ) → ∀ (S : Finset α) (x : Config n α), (∀ v, x v ∈ S) →
    ∀ A : Adversary n α, A.Bounded F → A.UsesValues (S : Set α) → ∀ H : ℕ,
      expList (Round n) (⌈C * Real.log n⌉₊ + H)
          (notAlmostStable (C * (F + Real.log n)) ⌈C * Real.log n⌉₊ H (runAdv A x))
        ≤ ((S.card : ℝ) - 1) * ((C * Real.log n + H) / (n : ℝ) ^ 2) := by
  refine ⟨2 ^ 20, by norm_num, fun n _ hL F hF S x hxS A hA hAS H => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hL0 : 0 ≤ Real.log n := by linarith
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg F
  have hF' : 1024 * (F : ℝ) ≤ √(n : ℝ) := by linarith
  have hne : S.Nonempty := ⟨x ⟨0, NeZero.pos n⟩, hxS _⟩
  have hPS : ∀ l v, runAdv A x l v ∈ S := fun l v =>
    Finset.mem_coe.mp (runAdv_mem A hAS x (fun v => Finset.mem_coe.mpr (hxS v)) l v)
  obtain ⟨K, hK⟩ : ∃ K, K = max (16 * (F : ℝ)) (1024 * Real.log n) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ le_trans (by positivity) (le_max_right _ _)
  have hKC : 2 * K ≤ 2 ^ 20 * ((F : ℝ) + Real.log n) := by
    rw [hK]
    rcases le_total (16 * (F : ℝ)) (1024 * Real.log n) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  calc expList (Round n) (⌈2 ^ 20 * Real.log n⌉₊ + H)
        (notAlmostStable (2 ^ 20 * (F + Real.log n)) ⌈2 ^ 20 * Real.log n⌉₊ H (runAdv A x))
      ≤ expList (Round n) (⌈2 ^ 20 * Real.log n⌉₊ + H)
        (notAlmostStable (2 * K) ⌈2 ^ 20 * Real.log n⌉₊ H (runAdv A x)) :=
        expList_le_expList fun l => notAlmostStable_mono hKC _ _ _ l
    -- the union bound over the thresholds at the legal values above the minimum
    _ ≤ expList (Round n) (⌈2 ^ 20 * Real.log n⌉₊ + H) (fun l => ∑ b ∈ S.erase (S.min' hne),
          notAlmostStable K ⌈2 ^ 20 * Real.log n⌉₊ H
            (fun l v => decide (b ≤ runAdv A x l v)) l) :=
        expList_le_expList fun l => notAlmostStable_le_sum (min'_mem S hne)
          (fun b hb => min'_le S b hb) hK0 _ _ _ hPS l
    _ = ∑ b ∈ S.erase (S.min' hne), expList (Round n) (⌈2 ^ 20 * Real.log n⌉₊ + H)
          (notAlmostStable K ⌈2 ^ 20 * Real.log n⌉₊ H
            (fun l v => decide (b ≤ runAdv A x l v))) := expList_sum _ _ _
    -- each threshold run is a perturbed run of 2-Choices
    _ ≤ ∑ b ∈ S.erase (S.min' hne), (2 ^ 20 * Real.log n + H) / (n : ℝ) ^ 2 :=
        sum_le_sum fun b _ => hK ▸
          adv_binary_window hL hF' (isAdvRun_threshold (runAdv_isAdvRun hA x) b) H
    _ = ((S.card : ℝ) - 1) * ((2 ^ 20 * Real.log n + H) / (n : ℝ) ^ 2) := by
        rw [sum_const, nsmul_eq_mul, card_erase_of_mem (min'_mem S hne),
          Nat.cast_pred (card_pos.mpr hne)]

end Median
