import Epidemics.Revisited.ShrinkingPotential

/-! # Lemma 20: one round and the path bound

* `overshoot_round_proof`: by Lemma 9 and Chebyshev's inequality, a round started with
  `k < f n` informed nodes ends with at least `f' n` informed nodes with probability at most
  `(p + c) / ((f' - f - p (1 - f))² n)`. The expected number of newly informed nodes is at
  most `p (n - k)`, and `k + p (n - k) ≤ n (f + p (1 - f))` because `p ≤ 1`.
* `jumpProb_le_sum`: if every round started below `lo` from a nonempty set reaches `hi` with
  probability at most `ε`, the path jumps over `[lo, hi[` within `t` rounds with probability at
  most `ε` times the expected number of those rounds that start below `lo`. The proof is an
  induction on `t` along `Kernel.trajectory`: the jump happens in the first round or in the
  path that follows it.
-/

namespace Epidemics.Revisited
open Finset Dynamics

section Trajectory
variable {α : Type*} [Fintype α]

lemma traj_mono (K : Kernel α) (t : ℕ) (a : α) {F G : List α → α → ℝ}
    (h : ∀ l b, F l b ≤ G l b) : K.trajectory t a F ≤ K.trajectory t a G := by
  induction t generalizing a F G with
  | zero => exact h [] a
  | succ t ih =>
    show (K a).expect (fun b => K.trajectory t b (fun l c => F (a :: l) c)) ≤
      (K a).expect (fun b => K.trajectory t b (fun l c => G (a :: l) c))
    exact (K a).expect_mono (fun b => ih b (fun l c => h (a :: l) c))

lemma traj_add (K : Kernel α) (t : ℕ) (a : α) (F G : List α → α → ℝ) :
    K.trajectory t a (fun l b => F l b + G l b) = K.trajectory t a F + K.trajectory t a G := by
  induction t generalizing a F G with
  | zero => rfl
  | succ t ih =>
    show (K a).expect (fun b => K.trajectory t b (fun l c => F (a :: l) c + G (a :: l) c)) =
      (K a).expect (fun b => K.trajectory t b (fun l c => F (a :: l) c)) +
        (K a).expect (fun b => K.trajectory t b (fun l c => G (a :: l) c))
    simp_rw [ih]
    exact Distribution.expect_add _ _ _

lemma traj_const (K : Kernel α) (t : ℕ) (a : α) (c : ℝ) :
    K.trajectory t a (fun _ _ => c) = c := by
  have h := K.trajectory_endpoint t a (fun _ => c)
  rw [K.iterate_const] at h
  exact h

/-- A functional of the first state of the path `a, S₁, …` is evaluated at `a`. -/
lemma traj_head (K : Kernel α) (t : ℕ) (a : α) (G : α → ℝ) :
    K.trajectory t a (fun l b => G ((l ++ [b]).headD b)) = G a := by
  cases t with
  | zero => rfl
  | succ t =>
    show (K a).expect (fun b => K.trajectory t b
      (fun l c => G (((a :: l) ++ [c]).headD c))) = G a
    simp only [List.cons_append, List.headD_cons, traj_const, Distribution.expect_const]

end Trajectory

variable {n : ℕ}

/-- A jump along `S :: path` happens in the first round or along `path`. -/
lemma jumpsOver_cons {lo hi : ℝ} {S : Finset (Fin n)} {l : List (Finset (Fin n))}
    {c : Finset (Fin n)} (h : JumpsOver lo hi (S :: (l ++ [c]))) :
    ((S.card : ℝ) < lo ∧ hi ≤ ((l ++ [c]).headD c).card) ∨ JumpsOver lo hi (l ++ [c]) := by
  generalize hpath : l ++ [c] = path at h ⊢
  have hne : path ≠ [] := by
    rw [← hpath]
    simp
  obtain ⟨y, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨e, he, h1, h2⟩ := h
  simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
  rcases he with rfl | he
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨e, he, h1, h2⟩

open Classical in
lemma jumpInd_cons_le (lo hi : ℝ) (S : Finset (Fin n)) (l : List (Finset (Fin n)))
    (c : Finset (Fin n)) :
    (if JumpsOver lo hi (S :: (l ++ [c])) then (1 : ℝ) else 0) ≤
      (if (S.card : ℝ) < lo ∧ hi ≤ (((l ++ [c]).headD c).card : ℝ) then 1 else 0) +
        (if JumpsOver lo hi (l ++ [c]) then 1 else 0) := by
  by_cases hj : JumpsOver lo hi (S :: (l ++ [c]))
  · rw [if_pos hj]
    rcases jumpsOver_cons hj with h | h
    · rw [if_pos h]
      split_ifs <;> norm_num
    · rw [if_pos h]
      split_ifs <;> norm_num
  · rw [if_neg hj]
    split_ifs <;> norm_num

open Classical in
/-- One step of the path: `P[jump within t + 1 rounds] ≤ E_{S₁}[1[|S| < lo ≤ hi ≤ |S₁|] +
P_{S₁}[jump within t rounds]]`. -/
lemma jumpProb_succ_le (P : RumorProcess n) (lo hi : ℝ) (t : ℕ) (S : Finset (Fin n)) :
    P.jumpProb lo hi (t + 1) S ≤ (P.K S).expect (fun S₁ =>
      (if (S.card : ℝ) < lo ∧ hi ≤ (S₁.card : ℝ) then (1 : ℝ) else 0) +
        P.jumpProb lo hi t S₁) := by
  show (P.K S).expect (fun S₁ => P.K.trajectory t S₁
      (fun l c => if JumpsOver lo hi ((S :: l) ++ [c]) then (1 : ℝ) else 0)) ≤ _
  apply (P.K S).expect_mono
  intro S₁
  have hmono := traj_mono P.K t S₁ (fun l c => jumpInd_cons_le lo hi S l c)
  rw [traj_add, traj_head P.K t S₁
    (fun y => if (S.card : ℝ) < lo ∧ hi ≤ (y.card : ℝ) then (1 : ℝ) else 0)] at hmono
  exact hmono

lemma jumpProb_zero (P : RumorProcess n) (lo hi : ℝ) (S : Finset (Fin n)) :
    P.jumpProb lo hi 0 S = 0 := by
  have hnot : ¬ JumpsOver lo hi [S] := by
    rintro ⟨e, he, -⟩
    simp at he
  classical
  show (if JumpsOver lo hi ([] ++ [S]) then (1 : ℝ) else 0) = 0
  rw [List.nil_append, if_neg hnot]

/-- Lemma 20, path form with a per-round bound `ε`: the probability of jumping over `[lo, hi[`
within `t` rounds is at most `ε` times the expected number of those rounds started below `lo`.
-/
lemma jumpProb_le_sum (P : RumorProcess n) {lo hi ε : ℝ}
    (hround : ∀ S : Finset (Fin n), S.Nonempty → (S.card : ℝ) < lo →
      (P.K S).prob (fun S' => hi ≤ (S'.card : ℝ)) ≤ ε)
    (t : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    P.jumpProb lo hi t S ≤ ε * ∑ i ∈ range t, P.notYet lo i S := by
  classical
  induction t generalizing S with
  | zero => simp [jumpProb_zero]
  | succ t ih =>
    have hstep := jumpProb_succ_le P lo hi t S
    rw [Distribution.expect_add] at hstep
    have hpt : ∀ T, S ⊆ T → P.jumpProb lo hi t T ≤ ε * ∑ i ∈ range t, P.notYet lo i T :=
      fun T hT => ih T (hS.mono hT)
    have hrest := expect_le_of_weight P S hpt
    rw [Distribution.expect_mul, expect_finset_sum] at hrest
    have hsucc : ∑ i ∈ range t, (P.K S).expect (fun T => P.notYet lo i T) =
        ∑ i ∈ range t, P.notYet lo (i + 1) S :=
      sum_congr rfl (fun i _ => (notYet_succ P lo i S).symm)
    rw [hsucc] at hrest
    have hfirst : (P.K S).expect (fun S₁ =>
        if (S.card : ℝ) < lo ∧ hi ≤ (S₁.card : ℝ) then (1 : ℝ) else 0) ≤ ε * below lo S := by
      by_cases hlt : (S.card : ℝ) < lo
      · have hb : below lo S = 1 := by simp [below, hlt]
        have hprob := prob_indicator_eq (P.K S) (fun S' => hi ≤ (S'.card : ℝ))
          (fun S₁ => if (S.card : ℝ) < lo ∧ hi ≤ (S₁.card : ℝ) then (1 : ℝ) else 0)
          (fun S₁ h => by simp [h]) (fun S₁ h => by simp [hlt, h])
        rw [hb, mul_one, ← hprob]
        exact hround S hS hlt
      · have hb : below lo S = 0 := by simp [below, hlt]
        have hzero : (fun S₁ : Finset (Fin n) =>
            if (S.card : ℝ) < lo ∧ hi ≤ (S₁.card : ℝ) then (1 : ℝ) else 0) = fun _ => 0 := by
          funext S₁
          simp [hlt]
        rw [hb, mul_zero, hzero, Distribution.expect_const]
    rw [sum_range_succ', notYet_zero]
    have hsplit : ε * (∑ i ∈ range t, P.notYet lo (i + 1) S + below lo S) =
        ε * below lo S + ε * ∑ i ∈ range t, P.notYet lo (i + 1) S := by ring
    linarith only [hstep, hrest, hfirst, hsplit]

/-- Lemma 20, one round (proof of `overshoot_round`). -/
lemma overshoot_round_proof {f p c f' : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c)
    (hff' : f + p * (1 - f) < f') :
    ∃ C : ℝ, ∀ n : ℕ, ∀ P : RumorProcess n, ∀ S : Finset (Fin n), (S.card : ℝ) < f * n →
      (∀ x ∉ S, P.informProb S x ≤ p) → (∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c / n) →
      (P.K S).prob (fun S' => f' * n ≤ (S'.card : ℝ)) ≤ C / n := by
  set δ : ℝ := f' - f - p * (1 - f) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith only [hff']
  refine ⟨(p + c) / δ ^ 2, ?_⟩
  intro n P S hk hinf hcov
  have hn : 0 < (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have := Nat.cast_nonneg (α := ℝ) S.card
      simp only [Nat.cast_zero, mul_zero] at hk
      linarith only [hk, this]
    · exact_mod_cast hpos
  set D := P.K S with hD
  set k : ℝ := (S.card : ℝ) with hkdef
  set u : ℝ := (n : ℝ) - k with hu
  set μ : ℝ := D.expect (fun T => (T.card : ℝ)) with hμ
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hu0 : 0 ≤ u := sub_nonneg.mpr (card_cast_le S)
  have hun : u ≤ n := by linarith only [hk0]
  -- expectation of the number of informed nodes
  have hμeq : μ = k + ∑ x ∈ (univ : Finset (Fin n)) \ S, P.informProb S x := expect_card_eq P S
  have hsum : ∑ x ∈ (univ : Finset (Fin n)) \ S, P.informProb S x ≤ p * u := by
    have h := sum_le_sum (fun x (hx : x ∈ (univ : Finset (Fin n)) \ S) =>
      hinf x (mem_sdiff.mp hx).2)
    rw [sum_const, nsmul_eq_mul, card_compl_cast] at h
    linarith only [h]
  -- variance (Lemma 9)
  have hvar := variance_card_le P S (div_nonneg hc hn.le) hcov
  have hcu : c / n * ((n : ℝ) - S.card) ^ 2 ≤ c * n := by
    have hsq : u ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hu0 hun 2
    have h1 := mul_le_mul_of_nonneg_left hsq (div_nonneg hc hn.le)
    have h2 : c / n * (n : ℝ) ^ 2 = c * n := by field_simp
    linarith only [h1, h2]
  have hV : D.expect (fun T => ((T.card : ℝ) - μ) ^ 2) ≤ (p + c) * n := by
    have hpu : p * u ≤ p * n := mul_le_mul_of_nonneg_left hun hp0
    linarith only [hvar, hcu, hμeq, hsum, hpu]
  -- the event is inside a deviation of at least `n δ`
  have hsub : ∀ T : Finset (Fin n), f' * n ≤ (T.card : ℝ) → n * δ ≤ |(T.card : ℝ) - μ| := by
    intro T hT
    have hkf : (1 - p) * k ≤ (1 - p) * (f * n) :=
      mul_le_mul_of_nonneg_left hk.le (sub_nonneg.mpr hp1)
    have hdev : n * δ ≤ (T.card : ℝ) - μ := by
      rw [hδ]
      linarith only [hT, hμeq, hsum, hkf]
    exact le_trans hdev (le_abs_self _)
  have hmono := prob_mono D hsub
  have hcheb := chebyshev D (fun T => (T.card : ℝ)) (mul_pos hn hδ0)
  have hfin : D.expect (fun T => ((T.card : ℝ) - μ) ^ 2) / (n * δ) ^ 2 ≤ (p + c) / δ ^ 2 / n := by
    have hpos : 0 < (n * δ) ^ 2 := pow_pos (mul_pos hn hδ0) 2
    calc D.expect (fun T => ((T.card : ℝ) - μ) ^ 2) / (n * δ) ^ 2
        ≤ (p + c) * n / (n * δ) ^ 2 := div_le_div_of_nonneg_right hV hpos.le
      _ = (p + c) / δ ^ 2 / n := by field_simp
  exact le_trans hmono (le_trans hcheb hfin)

/-- Lemma 20, path form (proof of `jumpProb_le`). -/
lemma jumpProb_le_proof {f p c : ℝ} (hf1 : f < 1) (hp0 : 0 < p) (hp1 : p < 1) (hc : 0 < c) :
    ∃ f' : ℝ, f < f' ∧ f' < 1 ∧ ∃ C : ℝ, ∀ n : ℕ, ∀ P : RumorProcess n,
      (∀ S : Finset (Fin n), S.Nonempty → (S.card : ℝ) < f * n →
        (∀ x ∉ S, P.informProb S x ≤ p) ∧ (∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c / n)) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ t : ℕ,
        P.jumpProb (f * n) (f' * n) t S ≤ C / n * ∑ i ∈ range t, P.notYet (f * n) i S := by
  have hpf : 0 < p * (1 - f) := mul_pos hp0 (by linarith only [hf1])
  have hpf1 : p * (1 - f) < 1 - f := by
    have := mul_lt_mul_of_pos_right hp1 (by linarith only [hf1] : 0 < 1 - f)
    linarith only [this]
  have hff' : f + p * (1 - f) < (f + p * (1 - f) + 1) / 2 := by linarith only [hpf1]
  obtain ⟨C, hC⟩ := overshoot_round_proof hp0.le hp1.le hc.le hff'
  refine ⟨(f + p * (1 - f) + 1) / 2, by linarith only [hpf, hpf1], by linarith only [hpf1], C,
    ?_⟩
  intro n P hyp S hS t
  exact jumpProb_le_sum P (fun T hT hlt => hC n P T hlt (hyp T hT hlt).1 (hyp T hT hlt).2) t S hS

end Epidemics.Revisited
