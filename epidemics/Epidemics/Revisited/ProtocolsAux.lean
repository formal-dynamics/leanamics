import Epidemics.Revisited.Protocols
import Epidemics.GiantCoins
import Epidemics.Revisited.GrowthAux

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-- Product formula for the uniform calls: the coordinates are independent and uniform. -/
lemma prob_calls_forall (A : Fin n → Finset (Fin n)) :
    (calls n).prob (fun c => ∀ v, c v ∈ A v) = ∏ v, ((A v).card : ℝ) / n := by
  classical
  haveI : Nonempty (Fin n → Fin n) := ⟨id⟩
  rw [Distribution.prob_eq_expect]
  unfold calls
  rw [Distribution.uniform_expect, avg_indicator]
  have hfil : (univ.filter fun c : Fin n → Fin n => ∀ v, c v ∈ A v) = Fintype.piFinset A := by
    ext c
    simp [Fintype.mem_piFinset]
  rw [hfil, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin, prod_div_distrib,
    prod_const, card_univ, Fintype.card_fin]
  push_cast
  rfl

lemma prob_map {α β : Type*} [Fintype α] [Fintype β] (D : Distribution α) (f : α → β)
    (s : β → Prop) : (D.map f).prob s = D.prob (fun a => s (f a)) := by
  classical
  rw [Distribution.prob_eq_expect, Distribution.prob_eq_expect, Distribution.map_expect]

/-- Inclusion–exclusion for two events. -/
lemma prob_and_eq {α : Type*} [Fintype α] (D : Distribution α) (A B : α → Prop) :
    D.prob (fun a => A a ∧ B a) =
      1 - D.prob (fun a => ¬ A a) - D.prob (fun a => ¬ B a) +
        D.prob (fun a => ¬ A a ∧ ¬ B a) := by
  classical
  rw [D.prob_eq_expect, D.prob_eq_expect, D.prob_eq_expect, D.prob_eq_expect,
    ← D.expect_const 1, ← Distribution.expect_sub, ← Distribution.expect_sub,
    ← Distribution.expect_add]
  congr 1
  funext a
  by_cases hA : A a <;> by_cases hB : B a <;> simp [hA, hB]

/-- The covariance of the "informed" indicators equals that of the "uninformed" ones. -/
lemma cov_eq (P : RumorProcess n) (S : Finset (Fin n)) (x y : Fin n) :
    P.cov S x y = (P.K S).prob (fun T => x ∉ T ∧ y ∉ T) -
      (P.K S).prob (fun T => x ∉ T) * (P.K S).prob (fun T => y ∉ T) := by
  unfold RumorProcess.cov RumorProcess.informProb
  rw [prob_and_eq, Epidemics.prob_not, Epidemics.prob_not]
  ring

lemma informProb_eq (P : RumorProcess n) (S : Finset (Fin n)) (x : Fin n) :
    P.informProb S x = 1 - (P.K S).prob (fun T => x ∉ T) := by
  unfold RumorProcess.informProb
  rw [Epidemics.prob_not]
  ring


lemma prod_ite_mem_const (S : Finset (Fin n)) (f : ℝ) :
    ∏ v, (if v ∈ S then f else 1) = f ^ S.card := by
  classical
  rw [prod_ite_mem, univ_inter, prod_const]

lemma prod_ite_eq_const (x : Fin n) (f : ℝ) :
    ∏ v, (if v = x then f else 1) = f := by
  classical
  rw [prod_ite_eq']
  simp

lemma n_pos_of_mem (x : Fin n) : (0 : ℝ) < n := by
  have := x.pos
  exact_mod_cast this

lemma card_erase_cast (x : Fin n) : (((univ : Finset (Fin n)).erase x).card : ℝ) = n - 1 := by
  rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
  have := x.pos
  rw [Nat.cast_sub (by omega)]
  simp

lemma card_erase_erase_cast {x y : Fin n} (hxy : x ≠ y) :
    ((((univ : Finset (Fin n)).erase x).erase y).card : ℝ) = n - 2 := by
  have hy : y ∈ (univ : Finset (Fin n)).erase x := mem_erase.mpr ⟨hxy.symm, mem_univ y⟩
  rw [card_erase_of_mem hy, card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
  have h2 : 2 ≤ n := by
    have := Fintype.card_le_of_injective (fun b : Bool => if b then x else y) (by
      intro a b hab
      cases a <;> cases b <;> simp_all [eq_comm])
    simpa using this
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

/-! ### Push -/

lemma not_mem_pushRound {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) (c : Fin n → Fin n) :
    x ∉ pushRound S c ↔ ∀ v, c v ∈ (if v ∈ S then (univ : Finset (Fin n)).erase x else univ) := by
  classical
  unfold pushRound
  constructor
  · intro h v
    split_ifs with hv
    · refine mem_erase.mpr ⟨fun hcv => h ?_, mem_univ _⟩
      exact mem_union_right _ (mem_image.mpr ⟨v, hv, hcv⟩)
    · exact mem_univ _
  · intro h hmem
    rcases mem_union.mp hmem with h1 | h1
    · exact hx h1
    · obtain ⟨v, hv, hcv⟩ := mem_image.mp h1
      have := h v
      rw [if_pos hv] at this
      exact (mem_erase.mp this).1 hcv

lemma not_mem_pushRound₂ {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (c : Fin n → Fin n) :
    (x ∉ pushRound S c ∧ y ∉ pushRound S c) ↔
      ∀ v, c v ∈ (if v ∈ S then ((univ : Finset (Fin n)).erase x).erase y else univ) := by
  classical
  rw [not_mem_pushRound hx, not_mem_pushRound hy]
  constructor
  · rintro ⟨h1, h2⟩ v
    have a := h1 v
    have b := h2 v
    split_ifs at a b ⊢ with hv
    · exact mem_erase.mpr ⟨(mem_erase.mp b).1, a⟩
    · exact mem_univ _
  · intro h
    refine ⟨fun v => ?_, fun v => ?_⟩ <;> have a := h v <;> split_ifs at a ⊢ with hv
    · exact mem_of_mem_erase a
    · exact mem_univ _
    · exact mem_erase.mpr ⟨(mem_erase.mp a).1, mem_univ _⟩
    · exact mem_univ _

lemma push_prob_not_mem {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    ((push n).K S).prob (fun T => x ∉ T) = (1 - 1 / (n : ℝ)) ^ S.card := by
  classical
  have hn := n_pos_of_mem x
  show ((calls n).map (pushRound S)).prob _ = _
  rw [prob_map, prob_congr _ (fun c => not_mem_pushRound hx c), prob_calls_forall]
  rw [← prod_ite_mem_const]
  refine prod_congr rfl fun v _ => ?_
  split_ifs
  · rw [card_erase_cast x]
    field_simp
  · rw [card_univ, Fintype.card_fin]
    field_simp

lemma push_prob_not_mem₂ {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) :
    ((push n).K S).prob (fun T => x ∉ T ∧ y ∉ T) = (1 - 2 / (n : ℝ)) ^ S.card := by
  classical
  have hn := n_pos_of_mem x
  show ((calls n).map (pushRound S)).prob _ = _
  rw [prob_map, prob_congr _ (fun c => not_mem_pushRound₂ hx hy c), prob_calls_forall]
  rw [← prod_ite_mem_const]
  refine prod_congr rfl fun v _ => ?_
  split_ifs
  · rw [card_erase_erase_cast hxy]
    field_simp
  · rw [card_univ, Fintype.card_fin]
    field_simp

/-! ### Pull -/

lemma not_mem_pullRound {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) (c : Fin n → Fin n) :
    x ∉ pullRound S c ↔
      ∀ v, c v ∈ (if v = x then (univ : Finset (Fin n)) \ S else univ) := by
  classical
  unfold pullRound
  constructor
  · intro h v
    split_ifs with hv
    · subst hv
      refine mem_sdiff.mpr ⟨mem_univ _, fun hc => h ?_⟩
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hc⟩)
    · exact mem_univ _
  · intro h hmem
    rcases mem_union.mp hmem with h1 | h1
    · exact hx h1
    · have := h x
      rw [if_pos rfl] at this
      exact (mem_sdiff.mp this).2 (mem_filter.mp h1).2

lemma forall_and_mem (A B : Fin n → Finset (Fin n)) (c : Fin n → Fin n) :
    ((∀ v, c v ∈ A v) ∧ ∀ v, c v ∈ B v) ↔ ∀ v, c v ∈ A v ∩ B v := by
  simp only [mem_inter]
  exact forall_and.symm

lemma card_univ_div (hn : (0 : ℝ) < n) : (((univ : Finset (Fin n)).card : ℝ)) / n = 1 := by
  rw [card_univ, Fintype.card_fin]
  exact div_self hn.ne'

lemma pull_prob_not_mem {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    ((pull n).K S).prob (fun T => x ∉ T) = 1 - S.card / (n : ℝ) := by
  classical
  have hn := n_pos_of_mem x
  show ((calls n).map (pullRound S)).prob _ = _
  rw [prob_map, prob_congr _ (fun c => not_mem_pullRound hx c), prob_calls_forall]
  rw [← prod_ite_eq_const x (1 - S.card / (n : ℝ))]
  refine prod_congr rfl fun v _ => ?_
  split_ifs
  · rw [card_compl_cast]
    field_simp
  · exact card_univ_div hn

lemma pull_prob_not_mem₂ {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) :
    ((pull n).K S).prob (fun T => x ∉ T ∧ y ∉ T) = (1 - S.card / (n : ℝ)) ^ 2 := by
  classical
  have hn := n_pos_of_mem x
  show ((calls n).map (pullRound S)).prob _ = _
  rw [prob_map, prob_congr _ (fun c => (and_congr (not_mem_pullRound hx c)
    (not_mem_pullRound hy c)).trans (forall_and_mem _ _ c)), prob_calls_forall]
  have hrhs : (1 - S.card / (n : ℝ)) ^ 2 =
      ∏ v, ((if v = x then 1 - S.card / (n : ℝ) else 1) *
        (if v = y then 1 - S.card / (n : ℝ) else 1)) := by
    rw [prod_mul_distrib, prod_ite_eq_const, prod_ite_eq_const]
    ring
  rw [hrhs]
  refine prod_congr rfl fun v _ => ?_
  by_cases hvx : v = x
  · subst hvx
    simp only [if_neg hxy, ↓reduceIte, inter_univ, mul_one]
    rw [card_compl_cast]
    field_simp
  · by_cases hvy : v = y
    · subst hvy
      simp only [if_neg hvx, ↓reduceIte, univ_inter, one_mul]
      rw [card_compl_cast]
      field_simp
    · simp only [if_neg hvx, if_neg hvy, inter_univ, mul_one]
      exact card_univ_div hn

/-! ### Push–pull -/

lemma not_mem_pushPullRound (S : Finset (Fin n)) (x : Fin n) (c : Fin n → Fin n) :
    x ∉ pushPullRound S c ↔ x ∉ pushRound S c ∧ x ∉ pullRound S c := by
  unfold pushPullRound
  rw [mem_union]
  tauto

lemma pushPull_prob_not_mem {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    ((pushPull n).K S).prob (fun T => x ∉ T) =
      (1 - 1 / (n : ℝ)) ^ S.card * (1 - S.card / (n : ℝ)) := by
  classical
  have hn := n_pos_of_mem x
  show ((calls n).map (pushPullRound S)).prob _ = _
  rw [prob_map, prob_congr _ (fun c => (not_mem_pushPullRound S x c).trans
    ((and_congr (not_mem_pushRound hx c) (not_mem_pullRound hx c)).trans
      (forall_and_mem _ _ c))), prob_calls_forall]
  rw [← prod_ite_mem_const, ← prod_ite_eq_const x (1 - S.card / (n : ℝ)), ← prod_mul_distrib]
  refine prod_congr rfl fun v _ => ?_
  by_cases hvS : v ∈ S
  · have hvx : v ≠ x := fun h => hx (h ▸ hvS)
    simp only [if_pos hvS, if_neg hvx, inter_univ, mul_one]
    rw [card_erase_cast x]
    field_simp
  · by_cases hvx : v = x
    · subst hvx
      simp only [if_neg hvS, ↓reduceIte, univ_inter, one_mul]
      rw [card_compl_cast]
      field_simp
    · simp only [if_neg hvS, if_neg hvx, inter_univ, mul_one]
      exact card_univ_div hn

lemma pushPull_prob_not_mem₂ {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) :
    ((pushPull n).K S).prob (fun T => x ∉ T ∧ y ∉ T) =
      (1 - 2 / (n : ℝ)) ^ S.card * (1 - S.card / (n : ℝ)) ^ 2 := by
  classical
  have hn := n_pos_of_mem x
  show ((calls n).map (pushPullRound S)).prob _ = _
  have hev : ∀ c : Fin n → Fin n, (x ∉ pushPullRound S c ∧ y ∉ pushPullRound S c) ↔
      ((∀ v, c v ∈ (if v ∈ S then ((univ : Finset (Fin n)).erase x).erase y else univ)) ∧
        ∀ v, c v ∈ (if v = x then (univ : Finset (Fin n)) \ S else univ) ∩
          (if v = y then (univ : Finset (Fin n)) \ S else univ)) := by
    intro c
    rw [not_mem_pushPullRound, not_mem_pushPullRound, ← not_mem_pushRound₂ hx hy,
      ← forall_and_mem, ← not_mem_pullRound hx, ← not_mem_pullRound hy]
    tauto
  rw [prob_map, prob_congr _ (fun c => (hev c).trans (forall_and_mem _ _ c)),
    prob_calls_forall]
  have hrhs : (1 - 2 / (n : ℝ)) ^ S.card * (1 - S.card / (n : ℝ)) ^ 2 =
      ∏ v, ((if v ∈ S then 1 - 2 / (n : ℝ) else 1) *
        (if v = x then 1 - S.card / (n : ℝ) else 1) *
        (if v = y then 1 - S.card / (n : ℝ) else 1)) := by
    rw [prod_mul_distrib, prod_mul_distrib, prod_ite_mem_const, prod_ite_eq_const,
      prod_ite_eq_const]
    ring
  rw [hrhs]
  refine prod_congr rfl fun v _ => ?_
  by_cases hvS : v ∈ S
  · have hvx : v ≠ x := fun h => hx (h ▸ hvS)
    have hvy : v ≠ y := fun h => hy (h ▸ hvS)
    simp only [if_pos hvS, if_neg hvx, if_neg hvy, inter_univ, mul_one]
    rw [card_erase_erase_cast hxy]
    field_simp
  · by_cases hvx : v = x
    · subst hvx
      have hvy : v ≠ y := hxy
      simp only [if_neg hvS, if_neg hvy, ↓reduceIte, univ_inter, inter_univ,
        one_mul, mul_one]
      rw [card_compl_cast]
      field_simp
    · by_cases hvy : v = y
      · subst hvy
        simp only [if_neg hvS, if_neg hvx, ↓reduceIte, univ_inter, one_mul,
          mul_one]
        rw [card_compl_cast]
        field_simp
      · simp only [if_neg hvS, if_neg hvx, if_neg hvy, inter_univ, mul_one]
        exact card_univ_div hn

/-! ### Elementary inequalities -/

lemma two_le_of_ne {x y : Fin n} (hxy : x ≠ y) : 2 ≤ n := by
  have := Fintype.card_le_of_injective (fun b : Bool => if b then x else y) (by
    intro a b hab
    cases a <;> cases b <;> simp_all [eq_comm])
  simpa using this

/-- Second-order Bonferroni: `(1 - x)^k ≤ 1 - k x + (k x)² / 2` for `0 ≤ x ≤ 1`. -/
lemma one_sub_pow_le_quad {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ 1 - k * x + (k * x) ^ 2 / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ 1 - x := by linarith
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_right ih h1
    push_cast
    nlinarith [mul_nonneg (mul_nonneg hk hk) (mul_nonneg (mul_nonneg hx0 hx0) hx0),
      mul_nonneg hx0 hx0]

/-- `e^t ≤ 1 + 2t` on `[0, 1]`. -/
lemma exp_le_one_add_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t ≤ 1 + 2 * t := by
  have h := Real.abs_exp_sub_one_le (x := t) (by rw [abs_of_nonneg ht0]; exact ht1)
  rw [abs_of_nonneg ht0] at h
  have := le_abs_self (Real.exp t - 1)
  linarith

/-- Push, shrinking regime: `(1 - 1/n)^k ≤ e^{-1} + (2/e)((n - k)/n)` for `k ≤ n`. -/
lemma push_stay_le {k : ℕ} (hn : (0 : ℝ) < n) (hk : (k : ℝ) ≤ n) :
    (1 - 1 / (n : ℝ)) ^ k ≤ Real.exp (-1) + 2 / Real.exp 1 * (((n : ℝ) - k) / n) := by
  have h1n : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn]
    have : (1 : ℝ) ≤ n := by
      have : (0 : ℕ) < n := by exact_mod_cast hn
      exact_mod_cast this
    exact this
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by linarith
  have hexp : (1 - 1 / (n : ℝ)) ^ k ≤ Real.exp (-(k / n)) := by
    calc (1 - 1 / (n : ℝ)) ^ k ≤ Real.exp (-(1 / n)) ^ k :=
          pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (-(1 / (n : ℝ)))]) k
      _ = Real.exp (-(k / n)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  set t : ℝ := ((n : ℝ) - k) / n with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hn.le
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hn]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsplit : -(k / (n : ℝ)) = -1 + t := by
    rw [ht]
    field_simp
    ring
  rw [hsplit, Real.exp_add] at hexp
  have hb := exp_le_one_add_two_mul ht0 ht1
  have he : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  have hpos : 0 < Real.exp (-1) := Real.exp_pos _
  calc (1 - 1 / (n : ℝ)) ^ k ≤ Real.exp (-1) * Real.exp t := hexp
    _ ≤ Real.exp (-1) * (1 + 2 * t) := mul_le_mul_of_nonneg_left hb hpos.le
    _ = Real.exp (-1) + 2 / Real.exp 1 * t := by rw [he]; ring

/-! ### One-round probabilities and covariances -/

lemma push_informProb_proof {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    (push n).informProb S x = 1 - (1 - 1 / (n : ℝ)) ^ S.card := by
  rw [informProb_eq, push_prob_not_mem hx]

lemma pull_informProb_proof {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    (pull n).informProb S x = S.card / (n : ℝ) := by
  rw [informProb_eq, pull_prob_not_mem hx]
  ring

lemma pushPull_informProb_proof {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    (pushPull n).informProb S x = 1 - (1 - 1 / (n : ℝ)) ^ S.card * (1 - S.card / (n : ℝ)) := by
  rw [informProb_eq, pushPull_prob_not_mem hx]

lemma two_pow_le {S : Finset (Fin n)} {x y : Fin n} (hxy : x ≠ y) :
    (1 - 2 / (n : ℝ)) ^ S.card ≤ ((1 - 1 / (n : ℝ)) ^ S.card) ^ 2 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast two_le_of_ne hxy
  have hn : (0 : ℝ) < n := by linarith
  have h0 : 0 ≤ 1 - 2 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn]
    exact h2
  have hle : 1 - 2 / (n : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ 2 := by
    have : (1 - 1 / (n : ℝ)) ^ 2 = 1 - 2 / n + (1 / n) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (1 / (n : ℝ))]
  rw [← pow_mul, mul_comm, pow_mul]
  exact pow_le_pow_left₀ h0 hle _

lemma push_cov_nonpos_proof {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) : (push n).cov S x y ≤ 0 := by
  rw [cov_eq, push_prob_not_mem₂ hx hy hxy, push_prob_not_mem hx, push_prob_not_mem hy]
  have := two_pow_le (S := S) hxy
  nlinarith

lemma pull_cov_eq_zero_proof {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) : (pull n).cov S x y = 0 := by
  rw [cov_eq, pull_prob_not_mem₂ hx hy hxy, pull_prob_not_mem hx, pull_prob_not_mem hy]
  ring

lemma pushPull_cov_nonpos_proof {S : Finset (Fin n)} {x y : Fin n} (hx : x ∉ S) (hy : y ∉ S)
    (hxy : x ≠ y) : (pushPull n).cov S x y ≤ 0 := by
  rw [cov_eq, pushPull_prob_not_mem₂ hx hy hxy, pushPull_prob_not_mem hx,
    pushPull_prob_not_mem hy]
  have h := two_pow_le (S := S) hxy
  have hsq : 0 ≤ (1 - S.card / (n : ℝ)) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_right h hsq
  nlinarith

/-! ### The conditions -/

lemma card_le_n (S : Finset (Fin n)) : (S.card : ℝ) ≤ n := by
  have := card_le_univ S
  simp only [Fintype.card_fin] at this
  exact_mod_cast this

lemma push_upperGrowth_proof : (push n).UpperGrowth 1 (1 / 2) 0 0 (1 / 2) := by
  intro S hS _
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · have hn := n_pos_of_mem x
    rw [push_informProb_proof hx]
    have h1n : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn]
      have : (1 : ℕ) ≤ n := x.pos
      exact_mod_cast this
    have hq := one_sub_pow_le_quad (by positivity) h1n S.card
    have hk : (S.card : ℝ) * (1 / n) = S.card / n := by ring
    rw [hk] at hq
    simp only [zero_div, sub_zero]
    nlinarith
  · simp only [zero_mul, zero_div]
    exact push_cov_nonpos_proof hx hy hxy

lemma push_upperShrinking_proof : (push n).UpperShrinking 1 (2 / Real.exp 1) 0 (1 / 2) := by
  intro S _
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · rw [push_informProb_proof hx, sub_sub_cancel]
    exact push_stay_le (n_pos_of_mem x) (card_le_n S)
  · simp only [zero_div]
    exact push_cov_nonpos_proof hx hy hxy

lemma pull_upperGrowth_proof : (pull n).UpperGrowth 1 0 0 0 (1 / 2) := by
  intro S _ _
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · rw [pull_informProb_proof hx]
    simp
  · simp only [zero_mul, zero_div]
    exact (pull_cov_eq_zero_proof hx hy hxy).le

lemma pull_upperDoubleShrinking_proof :
    (pull n).UpperDoubleShrinking 2 1 0 (1 / 2) (1 / 2) := by
  intro S _ _
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · have hn := n_pos_of_mem x
    rw [pull_informProb_proof hx, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul,
      sub_div, div_self hn.ne']
  · simp only [zero_mul, zero_div]
    exact (pull_cov_eq_zero_proof hx hy hxy).le

lemma frac_le_rpow {u : ℝ} (hn : (0 : ℝ) < n) (hu : u ≤ (n : ℝ) ^ (1 - 1 / 2 : ℝ)) :
    u / n ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [div_le_iff₀ hn]
  calc u ≤ (n : ℝ) ^ (1 - 1 / 2 : ℝ) := hu
    _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) * n := by
      rw [← Real.rpow_add_one hn.ne']
      norm_num

lemma pull_fastFinishing_proof : (pull n).FastFinishing (1 / 2) (1 / 2) := by
  intro S hS x hx
  have hn := n_pos_of_mem x
  rw [pull_informProb_proof hx]
  have h := frac_le_rpow hn hS
  rw [sub_div, div_self hn.ne'] at h
  exact h

lemma pushPull_upperGrowth_proof : (pushPull n).UpperGrowth 2 (3 / 4) 0 0 (1 / 2) := by
  intro S hS _
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · have hn := n_pos_of_mem x
    rw [pushPull_informProb_proof hx]
    have h1n : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn]
      have : (1 : ℕ) ≤ n := x.pos
      exact_mod_cast this
    have hq := one_sub_pow_le_quad (by positivity) h1n S.card
    have hk : (S.card : ℝ) * (1 / n) = S.card / n := by ring
    rw [hk] at hq
    set y : ℝ := S.card / n with hy
    have hy0 : 0 ≤ y := by positivity
    have hy1 : 1 - y ≥ 0 := by
      rw [hy, ge_iff_le, sub_nonneg, div_le_one hn]
      exact card_le_n S
    have hm := mul_le_mul_of_nonneg_right hq hy1
    simp only [zero_div, sub_zero]
    nlinarith [mul_nonneg (mul_nonneg hy0 hy0) hy0]
  · simp only [zero_mul, zero_div]
    exact pushPull_cov_nonpos_proof hx hy hxy

lemma pushPull_stay_le {S : Finset (Fin n)} {x : Fin n} (hx : x ∉ S) :
    1 - (pushPull n).informProb S x ≤ ((n : ℝ) - S.card) / n := by
  have hn := n_pos_of_mem x
  rw [pushPull_informProb_proof hx, sub_sub_cancel]
  have h1n : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn]
    have : (1 : ℕ) ≤ n := x.pos
    exact_mod_cast this
  have hp0 : 0 ≤ (1 - 1 / (n : ℝ)) ^ S.card := pow_nonneg (by linarith) _
  have hp1 : (1 - 1 / (n : ℝ)) ^ S.card ≤ 1 := pow_le_one₀ (by linarith) (by
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith)
  have hy1 : 0 ≤ 1 - S.card / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn]
    exact card_le_n S
  have heq : ((n : ℝ) - S.card) / n = 1 - S.card / n := by
    rw [sub_div, div_self hn.ne']
  rw [heq]
  nlinarith

lemma pushPull_upperDoubleShrinking_proof :
    (pushPull n).UpperDoubleShrinking 2 1 0 (1 / 2) (1 / 2) := by
  intro S _ _
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul]
    exact pushPull_stay_le hx
  · simp only [zero_mul, zero_div]
    exact pushPull_cov_nonpos_proof hx hy hxy

lemma pushPull_fastFinishing_proof : (pushPull n).FastFinishing (1 / 2) (1 / 2) := by
  intro S hS x hx
  exact le_trans (pushPull_stay_le hx) (frac_le_rpow (n_pos_of_mem x) hS)

end Epidemics.Revisited
