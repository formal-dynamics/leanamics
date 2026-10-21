import ThreeMajority.AnyStartMajorization
import Dynamics.Distribution

/-!
# Proposition 1 of BCEKMN17 (Rinott; Marshall–Olkin–Arnold, Proposition 11.E.11)

If `p ⪰ q`, every Schur-convex observable of the configuration has a larger expectation when
the `n` agents draw their colours i.i.d. from `p` than from `q`.

The proof sorts neither configurations nor colour counts, and uses no multinomial sums.

* `expect_le_of_transfer`: a single Robin Hood transfer of mass between two colours `a` and `b`.
  Along the transfer the expectation is a polynomial in the weight `θ` of `a`, nondecreasing
  past the midpoint: its derivative is a sum over agents `v`, and pairing each configuration with
  its images under swapping `a` and `b` (for all agents, then for agent `v` only) leaves terms
  that are nonnegative by Schur-convexity (`sum_transferSlope_nonneg`).
* `expect_le_of_partial_sums`: a chain of transfers (the Hardy–Littlewood–Pólya construction,
  `exists_transfer_step`) leads from `p` to `q` when `q` is sorted along an enumeration of the
  colours and the partial sums of `p` dominate those of `q`.
* `expect_le_of_majorizes`: sorting `q` and `p` and relabelling the colours of `p`
  (`expect_independent_perm`) reduces the sort-free majorization to that case.
-/

namespace ThreeMajority

open Finset Dynamics

section Transfer

variable {ι : Type*} [Fintype ι]

/-- A Robin Hood transfer between two coordinates `a` and `b` (with `x b ≤ y a ≤ x a` and the
same sum on `{a, b}`) produces a vector majorized by the original one. -/
lemma majorizes_of_transfer {x y : ι → ℝ} {a b : ι} (hab : a ≠ b)
    (hc : ∀ c, c ≠ a → c ≠ b → y c = x c) (hs : y a + y b = x a + x b)
    (hba : x b ≤ y a) (hax : y a ≤ x a) : Majorizes x y := by
  classical
  have key : ∀ S : Finset ι, ∑ i ∈ S, y i = ∑ i ∈ S, x i +
      ((if a ∈ S then y a - x a else 0) + if b ∈ S then y b - x b else 0) := by
    intro S
    have h : ∀ i ∈ S, y i - x i =
        (if a = i then y a - x a else 0) + if b = i then y b - x b else 0 := by
      intro i _
      by_cases ha : a = i
      · subst ha; simp [hab.symm]
      by_cases hb : b = i
      · subst hb; simp [ha]
      simp [ha, hb, hc i (Ne.symm ha) (Ne.symm hb)]
    rw [← sub_eq_iff_eq_add', ← sum_sub_distrib, sum_congr rfl h, sum_add_distrib,
      sum_ite_eq, sum_ite_eq]
  refine ⟨?_, fun S => ?_⟩
  · have := key univ
    simp only [mem_univ, if_true] at this
    linarith
  by_cases ha : a ∈ S
  · refine ⟨S, rfl, ?_⟩
    rw [key S, if_pos ha]
    split_ifs <;> linarith
  by_cases hb : b ∈ S
  · refine ⟨insert a (S.erase b), ?_, ?_⟩
    · rw [card_insert_of_notMem (by simp [ha]), card_erase_of_mem hb,
        Nat.sub_add_cancel (card_pos.mpr ⟨b, hb⟩)]
    · rw [key S, if_neg ha, if_pos hb, sum_insert (by simp [ha]), ← add_sum_erase S x hb]
      linarith
  · exact ⟨S, rfl, by rw [key S, if_neg ha, if_neg hb]; simp⟩

/-- A vector majorizes each of its rearrangements. -/
lemma majorizes_comp_perm (x : ι → ℝ) (π : Equiv.Perm ι) : Majorizes x (x ∘ π) := by
  refine ⟨(Equiv.sum_comp π x).symm, fun S => ⟨S.map π.toEmbedding, card_map _, ?_⟩⟩
  simp [sum_map]

end Transfer

/-- `w ^ K * u ^ L ≤ u ^ K * w ^ L` for `0 ≤ w ≤ u` and `L ≤ K`. -/
lemma pow_mul_pow_le_pow_mul_pow {u w : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) {K L : ℕ} (h : L ≤ K) :
    w ^ K * u ^ L ≤ u ^ K * w ^ L := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have h0 : 0 ≤ w ^ L * u ^ L := mul_nonneg (pow_nonneg hw _) (pow_nonneg (hw.trans hwu) _)
  calc w ^ (L + j) * u ^ L = (w ^ L * u ^ L) * w ^ j := by ring
    _ ≤ (w ^ L * u ^ L) * u ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw hwu j) h0
    _ = u ^ (L + j) * w ^ L := by ring

section Colours

variable {n : ℕ} {σ : Type*} [DecidableEq σ]

/-- Relabelling the colours permutes the configuration vector. -/
lemma countVec_perm_comp (π : Equiv.Perm σ) (c : Fin n → σ) :
    countVec (π ∘ c) = countVec c ∘ π.symm := by
  funext a
  simp only [countVec, colourCount, Function.comp_apply, Equiv.apply_eq_iff_eq_symm_apply]

/-- The number of agents of colour `d` after setting agent `v` to colour `c`. -/
lemma colourCount_update (x : Fin n → σ) (v : Fin n) (c d : σ) :
    colourCount (Function.update x v c) d = #{u ∈ univ.erase v | x u = d} +
      if c = d then 1 else 0 := by
  rw [colourCount, card_filter, card_filter, ← add_sum_erase _ _ (mem_univ v), add_comm]
  congr 1
  · exact sum_congr rfl fun u hu => by rw [Function.update_of_ne (ne_of_mem_erase hu)]
  · simp

/-- Colour weights along a transfer between the colours `a` and `b`: `θ` on `a`, the rest
`w a + w b - θ` of their mass on `b`, and `w` elsewhere. -/
noncomputable def transferWeight (w : σ → ℝ) (a b : σ) (θ : ℝ) (c : σ) : ℝ :=
  if c = a then θ else if c = b then w a + w b - θ else w c

/-- The derivative of `transferWeight w a b θ c` in `θ`. -/
def transferSlope (a b c : σ) : ℝ :=
  if c = a then 1 else if c = b then -1 else 0

section TransferWeight

variable {w : σ → ℝ} {a b : σ}

/-- Swapping the colours `a` and `b` exchanges `θ` and `w a + w b - θ`. -/
lemma transferWeight_swap (hab : a ≠ b) (θ : ℝ) (c : σ) :
    transferWeight w a b θ (Equiv.swap a b c) = transferWeight w a b (w a + w b - θ) c := by
  unfold transferWeight
  by_cases ha : c = a
  · subst ha; simp [hab.symm]
  by_cases hb : c = b
  · subst hb; simp [ha]
  simp [Equiv.swap_apply_of_ne_of_ne ha hb, ha, hb]

/-- Swapping the colours `a` and `b` reverses the slope. -/
lemma transferSlope_swap (hab : a ≠ b) (c : σ) :
    transferSlope a b (Equiv.swap a b c) = -transferSlope a b c := by
  unfold transferSlope
  by_cases ha : c = a
  · subst ha; simp [hab.symm]
  by_cases hb : c = b
  · subst hb; simp [ha]
  simp [Equiv.swap_apply_of_ne_of_ne ha hb, ha, hb]

/-- Each transfer weight is affine in `θ`, with slope `transferSlope`. -/
lemma hasDerivAt_transferWeight (c : σ) (θ : ℝ) :
    HasDerivAt (fun t => transferWeight w a b t c) (transferSlope a b c) θ := by
  unfold transferWeight transferSlope
  by_cases ha : c = a
  · subst ha
    simpa using hasDerivAt_id' θ
  by_cases hb : c = b
  · subst hb
    simpa [ha] using (hasDerivAt_id' θ).const_sub (w a + w c)
  simpa [ha, hb] using hasDerivAt_const θ (w c)

/-- Along a transfer, a product of colour weights is `θ ^ K * (w a + w b - θ) ^ L * R`, with
`K`, `L` the numbers of factors of colour `a`, `b` and `R ≥ 0` not depending on `θ`. -/
lemma prod_transferWeight (hw : ∀ c, 0 ≤ w c) (hab : a ≠ b) (E : Finset (Fin n))
    (x : Fin n → σ) : ∃ R, 0 ≤ R ∧ ∀ θ, ∏ u ∈ E, transferWeight w a b θ (x u) =
      θ ^ #{u ∈ E | x u = a} * (w a + w b - θ) ^ #{u ∈ E | x u = b} * R := by
  refine ⟨∏ u ∈ E with ¬x u = a ∧ ¬x u = b, w (x u),
    prod_nonneg fun u _ => hw _, fun θ => ?_⟩
  rw [← prod_filter_mul_prod_filter_not E (fun u => x u = a),
    ← prod_filter_mul_prod_filter_not (E.filter fun u => ¬x u = a) (fun u => x u = b),
    filter_filter, filter_filter, mul_assoc]
  have hb : (E.filter fun u => ¬x u = a ∧ x u = b) = E.filter fun u => x u = b :=
    filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hab.symm, h⟩⟩
  rw [hb]
  congr 1
  · rw [prod_congr rfl fun u hu => by rw [(mem_filter.1 hu).2, transferWeight, if_pos rfl],
      prod_const]
  congr 1
  · rw [prod_congr rfl fun u hu => by
      rw [(mem_filter.1 hu).2, transferWeight, if_neg hab.symm, if_pos rfl], prod_const]
  · refine prod_congr rfl fun u hu => ?_
    obtain ⟨-, h1, h2⟩ := (mem_filter.1 hu)
    rw [transferWeight, if_neg h1, if_neg h2]

end TransferWeight

end Colours

section Expect

variable {n : ℕ} {σ : Type*} [Fintype σ]

/-- The expectation of an observable under i.i.d. colours, as an explicit sum over the
configurations, with the colour weights given by any function equal to them. -/
lemma expect_independent_eq (r : Distribution σ) (g : σ → ℝ) (hg : ∀ c, r.weight c = g c)
    (φ : (Fin n → σ) → ℝ) :
    (Distribution.independent fun _ : Fin n => r).expect φ = ∑ x, (∏ v, g (x v)) * φ x := by
  simp only [Distribution.expect, Distribution.independent, hg]

/-- Every weight function is antitone along some enumeration of the colours. -/
lemma exists_equiv_antitone (f : σ → ℝ) :
    ∃ e : Fin (Fintype.card σ) ≃ σ, Antitone (f ∘ e) := by
  refine ⟨(Tuple.sort fun i => -f ((Fintype.equivFin σ).symm i)).trans (Fintype.equivFin σ).symm,
    fun i j hij => ?_⟩
  simpa using Tuple.monotone_sort (fun i => -f ((Fintype.equivFin σ).symm i)) hij

end Expect

variable {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A Schur-convex observable is invariant under relabelling the colours. -/
lemma SchurConvex.apply_perm_comp {φ : (Fin n → σ) → ℝ} (hφ : SchurConvex φ)
    (π : Equiv.Perm σ) (c : Fin n → σ) : φ (π ∘ c) = φ c := by
  have h := countVec_perm_comp π c
  refine le_antisymm (hφ _ _ ?_) (hφ _ _ ?_)
  · rw [h]
    exact majorizes_comp_perm _ _
  · have : countVec c = countVec (π ∘ c) ∘ π := by
      rw [h]; funext a; simp
    rw [this]
    exact majorizes_comp_perm _ _

/-- Relabelling the colours of the common law of the agents does not change the expectation of
a Schur-convex observable. -/
lemma expect_independent_perm {φ : (Fin n → σ) → ℝ} (hφ : SchurConvex φ) (π : Equiv.Perm σ)
    (p r : Distribution σ) (hr : ∀ c, r.weight c = p.weight (π c)) :
    (Distribution.independent fun _ : Fin n => r).expect φ =
      (Distribution.independent fun _ : Fin n => p).expect φ := by
  rw [expect_independent_eq r _ hr, expect_independent_eq p _ fun _ => rfl]
  refine Fintype.sum_bijective (fun x => π ∘ x)
    (Equiv.arrowCongr (Equiv.refl _) π).bijective _ _ fun x => ?_
  simp [hφ.apply_perm_comp]

/-- Moving agent `v` from colour `a` to colour `b` is a Robin Hood transfer of the
configuration vector when the other agents have colour `a` at least as often as colour `b`. -/
lemma majorizes_countVec_update {a b : σ} (hab : a ≠ b) (x : Fin n → σ) (v : Fin n)
    (h : #{u ∈ univ.erase v | x u = b} ≤ #{u ∈ univ.erase v | x u = a}) :
    Majorizes (countVec (Function.update x v a)) (countVec (Function.update x v b)) := by
  have hcv : ∀ c d, countVec (Function.update x v c) d =
      (#{u ∈ univ.erase v | x u = d} : ℝ) + if c = d then 1 else 0 := by
    intro c d
    simp only [countVec, colourCount_update]
    push_cast
    rfl
  apply majorizes_of_transfer hab
  · intro c hca hcb
    rw [hcv, hcv, if_neg (Ne.symm hca), if_neg (Ne.symm hcb)]
  · simp only [hcv, if_neg hab, if_neg hab.symm]
    ring
  · simp only [hcv, if_neg hab, if_neg hab.symm]
    exact_mod_cast h
  · simp [hcv, hab.symm]

/-- The paired terms of the derivative along a transfer are nonnegative: the weight difference
and the difference of the observable have the same sign. -/
lemma transfer_term_nonneg {w : σ → ℝ} {a b : σ} (hw : ∀ c, 0 ≤ w c) (hab : a ≠ b)
    {φ : (Fin n → σ) → ℝ} (hφ : SchurConvex φ) {θ : ℝ} (hθ : w a + w b - θ ≤ θ)
    (hθs : θ ≤ w a + w b) (x : Fin n → σ) (v : Fin n) :
    0 ≤ ((∏ u ∈ univ.erase v, transferWeight w a b θ (x u)) -
        ∏ u ∈ univ.erase v, transferWeight w a b (w a + w b - θ) (x u)) *
      (φ (Function.update x v a) - φ (Function.update x v b)) := by
  obtain ⟨R, hR, hP⟩ := prod_transferWeight hw hab (univ.erase v) x
  rw [hP, hP, sub_sub_cancel, ← sub_mul]
  have hs : 0 ≤ w a + w b - θ := sub_nonneg.2 hθs
  rcases le_total #{u ∈ univ.erase v | x u = b} #{u ∈ univ.erase v | x u = a} with h | h
  · refine mul_nonneg (mul_nonneg (sub_nonneg.2 ?_) hR)
      (sub_nonneg.2 (hφ _ _ (majorizes_countVec_update hab x v h)))
    exact pow_mul_pow_le_pow_mul_pow hs hθ h
  · refine mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ?_) hR)
      (sub_nonpos.2 (hφ _ _ (majorizes_countVec_update hab.symm x v h)))
    exact (mul_comm _ _).trans_le ((pow_mul_pow_le_pow_mul_pow hs hθ h).trans_eq (mul_comm _ _))

/-- The contribution of agent `v` to the derivative along a transfer is nonnegative past the
midpoint. Pair each configuration with its image under swapping `a` and `b` (for all agents,
then for agent `v` only), and apply `transfer_term_nonneg`. -/
lemma sum_transferSlope_nonneg {w : σ → ℝ} {a b : σ} (hw : ∀ c, 0 ≤ w c) (hab : a ≠ b)
    {φ : (Fin n → σ) → ℝ} (hφ : SchurConvex φ) {θ : ℝ} (hθ : w a + w b - θ ≤ θ)
    (hθs : θ ≤ w a + w b) (v : Fin n) :
    0 ≤ ∑ x : Fin n → σ, (∏ u ∈ univ.erase v, transferWeight w a b θ (x u)) *
      transferSlope a b (x v) * φ x := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ → (Fin n → σ) → ℝ,
      P = fun t x => ∏ u ∈ univ.erase v, transferWeight w a b t (x u) := ⟨_, rfl⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ', θ' = w a + w b - θ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : σ → ℝ, d = transferSlope a b := ⟨_, rfl⟩
  have hdτ : ∀ c, d (Equiv.swap a b c) = -d c := fun c => by rw [hd, transferSlope_swap hab]
  suffices h : 0 ≤ ∑ x, P θ x * d (x v) * φ x by simpa only [hP, hd] using h
  -- swapping `a` and `b` for all agents exchanges `θ` and `θ'`
  have hτ : Function.Involutive fun x : Fin n → σ => Equiv.swap a b ∘ x :=
    fun x => by funext u; simp
  have h1 : ∑ x, P θ' x * -d (x v) * φ x = ∑ x, P θ x * d (x v) * φ x := by
    refine Fintype.sum_bijective _ hτ.bijective _ _ fun x => ?_
    simp only [hP, hθ', Function.comp_apply, transferWeight_swap hab, hdτ, hφ.apply_perm_comp]
  -- swapping `a` and `b` for agent `v` only
  obtain ⟨e, he⟩ : ∃ e : (Fin n → σ) → Fin n → σ,
      e = fun x => Function.update x v (Equiv.swap a b (x v)) := ⟨_, rfl⟩
  have hev : Function.Involutive e := fun x => by simp [he]
  have hev_v : ∀ x, e x v = Equiv.swap a b (x v) := fun x => by simp [he]
  have hPe : ∀ t x, P t (e x) = P t x := fun t x => by
    simp only [hP, he]
    exact prod_congr rfl fun u hu => by rw [Function.update_of_ne (ne_of_mem_erase hu)]
  have h2 : ∑ x, (P θ x - P θ' x) * -d (x v) * φ (e x) =
      ∑ x, (P θ x - P θ' x) * d (x v) * φ x := by
    refine Fintype.sum_bijective _ hev.bijective _ _ fun x => ?_
    rw [hPe, hPe, hev_v, hdτ]
  -- the paired terms are nonnegative
  have h3 : ∀ x, 0 ≤ (P θ x - P θ' x) * (d (x v) * (φ x - φ (e x))) := by
    intro x
    have key := transfer_term_nonneg hw hab hφ hθ hθs x v
    rw [← hθ'] at key
    simp only [hP, he, hd, transferSlope]
    by_cases ha : x v = a
    · have hxa : Function.update x v a = x := by rw [← ha]; exact Function.update_eq_self v x
      rw [hxa] at key
      simpa [ha] using key
    by_cases hb : x v = b
    · have hxb : Function.update x v b = x := by rw [← hb]; exact Function.update_eq_self v x
      rw [hxb] at key
      have : -(φ x - φ (Function.update x v a)) = φ (Function.update x v a) - φ x := by ring
      simpa [hb, hab.symm, this] using key
    · simp [ha, hb]
  have h4 := sum_nonneg fun x (_ : x ∈ univ) => h3 x
  simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, sum_sub_distrib,
    sum_neg_distrib] at h1 h2 h4 ⊢
  linarith

/-- The derivative of the expectation along a transfer, as a function of the weight `θ` of `a`. -/
lemma hasDerivAt_sum_transferWeight (w : σ → ℝ) (a b : σ) (φ : (Fin n → σ) → ℝ) (θ : ℝ) :
    HasDerivAt (fun t => ∑ x : Fin n → σ, (∏ v, transferWeight w a b t (x v)) * φ x)
      (∑ x : Fin n → σ, (∑ v, (∏ u ∈ univ.erase v, transferWeight w a b θ (x u)) *
        transferSlope a b (x v)) * φ x) θ := by
  refine HasDerivAt.fun_sum fun x _ => ?_
  have h := HasDerivAt.fun_finsetProd (u := univ) (f := fun v t => transferWeight w a b t (x v))
    fun v _ => hasDerivAt_transferWeight (x v) θ
  simpa only [smul_eq_mul] using h.mul_const (φ x)

/-- **Transfer lemma.** Moving mass from a colour `a` to a colour `b`, without making `b`
heavier than `a`, does not increase the expectation of a Schur-convex observable under i.i.d.
colours. The expectation along the transfer is monotone past the midpoint, by
`sum_transferSlope_nonneg`. -/
theorem expect_le_of_transfer (p r : Distribution σ) {a b : σ} (hab : a ≠ b)
    (hc : ∀ c, c ≠ a → c ≠ b → r.weight c = p.weight c)
    (hs : r.weight a + r.weight b = p.weight a + p.weight b)
    (hba : r.weight b ≤ r.weight a) (hap : r.weight a ≤ p.weight a)
    {φ : (Fin n → σ) → ℝ} (hφ : SchurConvex φ) :
    (Distribution.independent fun _ : Fin n => r).expect φ ≤
      (Distribution.independent fun _ : Fin n => p).expect φ := by
  rw [expect_independent_eq r (transferWeight p.weight a b (r.weight a)) fun c => ?_,
    expect_independent_eq p (transferWeight p.weight a b (p.weight a)) fun c => ?_]
  · have hd := hasDerivAt_sum_transferWeight p.weight a b φ
    have hpb := p.nonneg b
    have hmono : MonotoneOn
        (fun t => ∑ x : Fin n → σ, (∏ v, transferWeight p.weight a b t (x v)) * φ x)
        (Set.Icc ((p.weight a + p.weight b) / 2) (p.weight a + p.weight b)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun θ _ => (hd θ).continuousAt.continuousWithinAt)
        (fun θ _ => (hd θ).differentiableAt.differentiableWithinAt) fun θ hθ => ?_
      rw [interior_Icc] at hθ
      rw [(hd θ).deriv]
      simp_rw [sum_mul]
      rw [sum_comm]
      exact sum_nonneg fun v _ => sum_transferSlope_nonneg p.nonneg hab hφ
        (by linarith [hθ.1]) hθ.2.le v
    exact hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hap
  · unfold transferWeight
    split_ifs with h1 h2
    · rw [h1]
    · rw [h2]; ring
    · rfl
  · unfold transferWeight
    split_ifs with h1 h2
    · rw [h1]
    · rw [h2]; linarith
    · exact hc c h1 h2

/-- One step of the Hardy–Littlewood–Pólya construction. If the partial sums of `x` dominate
those of an antitone `y` with the same total and `x ≠ y`, moving some `δ ≥ 0` from an index `j`
to a later index `k` keeps the domination, keeps the entry at `j` above the one at `k`, and makes
`x` agree with `y` at one more index. Here `k` is the first index with `x k < y k`. -/
lemma exists_transfer_step {m : ℕ} (x y : Fin m → ℝ) (hy : Antitone y)
    (hdom : ∀ l : ℕ, ∑ i with i.val < l, y i ≤ ∑ i with i.val < l, x i)
    (hsum : ∑ i, x i = ∑ i, y i) (hne : ∃ i, x i ≠ y i) :
    ∃ j k : Fin m, ∃ δ : ℝ, j ≠ k ∧ 0 ≤ δ ∧ y j ≤ x j - δ ∧ x k + δ ≤ y k ∧ y k ≤ y j ∧
      (∀ l : ℕ, ∑ i with i.val < l, y i ≤
        ∑ i with i.val < l, (x i - (if i = j then δ else 0) + if i = k then δ else 0)) ∧
      #{i | x i - (if i = j then δ else 0) + (if i = k then δ else 0) ≠ y i} <
        #{i | x i ≠ y i} := by
  -- the first index `k` where `x` is below `y`
  have hk : ({i | x i < y i} : Finset (Fin m)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    obtain ⟨i, hi⟩ := hne
    exact hi ((sum_eq_sum_iff_of_le fun i _ => not_lt.1 (h (mem_univ i))).1 hsum.symm i
      (mem_univ i)).symm
  obtain ⟨k, hk, hkmin⟩ := exists_min_image _ id hk
  have hkx : x k < y k := (mem_filter.1 hk).2
  have hbelow : ∀ i, i < k → y i ≤ x i := fun i hi =>
    not_lt.1 fun h => absurd (hkmin i (mem_filter.2 ⟨mem_univ i, h⟩)) (not_le.2 hi)
  -- an earlier index `j` where `x` is above `y`
  obtain ⟨j, hjk, hjx⟩ : ∃ j, j < k ∧ y j < x j := by
    by_contra h
    push Not at h
    have h0 := hdom (k.val + 1)
    rw [← sub_nonneg, ← sum_sub_distrib, sum_eq_single_of_mem k (by simp) fun i hi hik => ?_]
      at h0
    · linarith
    have hik' : i < k := lt_of_le_of_ne (Fin.le_def.2 (Nat.lt_succ_iff.1 (mem_filter.1 hi).2)) hik
    linarith [h i hik', hbelow i hik']
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min (x j - y j) (y k - x k) := ⟨_, rfl⟩
  have hδj : δ ≤ x j - y j := hδ ▸ min_le_left _ _
  have hδk : δ ≤ y k - x k := hδ ▸ min_le_right _ _
  have hjk' : j ≠ k := hjk.ne
  refine ⟨j, k, δ, hjk', hδ ▸ le_min (by linarith) (by linarith), by linarith, by linarith,
    hy hjk.le, fun l => ?_, ?_⟩
  · rw [sum_add_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
    simp only [mem_filter, mem_univ, true_and]
    by_cases hj : j.val < l
    · by_cases hk : k.val < l
      · simpa [hj, hk] using hdom l
      -- `j < l ≤ k`: the partial sum of `x - y` up to `l` is at least `x j - y j ≥ δ`
      have h1 : x j - y j ≤ ∑ i with i.val < l, (x i - y i) :=
        single_le_sum (f := fun i => x i - y i) (fun i hi => sub_nonneg.2 (hbelow i
          (Fin.lt_def.2 (lt_of_lt_of_le (mem_filter.1 hi).2 (not_lt.1 hk)))))
          (mem_filter.2 ⟨mem_univ j, hj⟩)
      rw [sum_sub_distrib] at h1
      simp only [hj, hk, if_true, if_false]
      linarith
    · have hk : ¬k.val < l := fun h => hj (lt_trans (Fin.lt_def.1 hjk) h)
      simpa [hj, hk] using hdom l
  · refine card_lt_card ((ssubset_iff_of_subset fun i hi => ?_).2 ?_)
    · simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_cases hij : i = j
      · subst hij; linarith
      by_cases hik : i = k
      · subst hik; linarith
      simpa [hij, hik] using hi
    rcases min_choice (x j - y j) (y k - x k) with h | h
    · exact ⟨j, by simp; linarith, by simp [hjk']; linarith⟩
    · exact ⟨k, by simp; linarith, by simp [hjk'.symm]; linarith⟩

/-- **Chain of transfers.** If the partial sums of `p` dominate those of `q` along an
enumeration of the colours on which `q` is antitone, then `E_q φ ≤ E_p φ`. By induction on the
number of colours where `p` and `q` differ, with `exists_transfer_step` and
`expect_le_of_transfer`. -/
theorem expect_le_of_partial_sums {m : ℕ} (e : Fin m ≃ σ) (p q : Distribution σ)
    (hq : Antitone (q.weight ∘ e))
    (hdom : ∀ l : ℕ, ∑ i with i.val < l, q.weight (e i) ≤ ∑ i with i.val < l, p.weight (e i))
    {φ : (Fin n → σ) → ℝ} (hφ : SchurConvex φ) :
    (Distribution.independent fun _ : Fin n => q).expect φ ≤
      (Distribution.independent fun _ : Fin n => p).expect φ := by
  obtain ⟨N, hN⟩ : ∃ N, #{i | p.weight (e i) ≠ q.weight (e i)} = N := ⟨_, rfl⟩
  induction N using Nat.strong_induction_on generalizing p with
  | _ N ih =>
  by_cases hne : ∃ i, p.weight (e i) ≠ q.weight (e i)
  swap
  · push Not at hne
    have hpq : p.weight = q.weight := funext fun c => by simpa using hne (e.symm c)
    simp only [Distribution.expect, Distribution.independent, hpq, le_refl]
  have hsum : ∑ i, (p.weight ∘ e) i = ∑ i, (q.weight ∘ e) i := by
    simp only [Function.comp_apply, Equiv.sum_comp, p.sum_one, q.sum_one]
  obtain ⟨j, k, δ, hjk, hδ, hj, hk, hkj, hdom', hcard⟩ :=
    exists_transfer_step _ _ hq hdom hsum hne
  have hejk : e j ≠ e k := e.injective.ne hjk
  -- `p` with `δ` moved from colour `e j` to colour `e k`
  let r : Distribution σ :=
    { weight := fun c => p.weight c - (if c = e j then δ else 0) + if c = e k then δ else 0
      nonneg := fun c => by
        split_ifs with h1 h2
        · exact absurd (h1.symm.trans h2) hejk
        · subst h1; simp only [Function.comp_apply] at hj; linarith [q.nonneg (e j)]
        · linarith [p.nonneg c]
        · linarith [p.nonneg c]
      sum_one := by
        rw [sum_add_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq', p.sum_one]
        simp }
  have hr : ∀ i, r.weight (e i) =
      p.weight (e i) - (if i = j then δ else 0) + if i = k then δ else 0 := fun i => by
    simp [r, e.injective.eq_iff]
  calc (Distribution.independent fun _ : Fin n => q).expect φ
      ≤ (Distribution.independent fun _ : Fin n => r).expect φ := by
        have hlt : #{i | r.weight (e i) ≠ q.weight (e i)} < N := by
          rw [← hN]
          simp only [hr]
          exact hcard
        refine ih _ hlt r (fun l => ?_) rfl
        simp only [hr]
        exact hdom' l
    _ ≤ (Distribution.independent fun _ : Fin n => p).expect φ := by
        refine expect_le_of_transfer p r hejk (fun c h1 h2 => by simp [r, h1, h2]) ?_ ?_ ?_ hφ
        · simp [r, hejk, hejk.symm]
        · simp only [Function.comp_apply] at hj hk hkj
          simp only [r, if_neg hejk, if_neg hejk.symm, if_pos]
          linarith
        · simp [r, hejk, hδ]

/-- If `#A = #B` and every term over `A` is at most every term over `B`, the sum over `A` is at
most the sum over `B`. -/
lemma sum_le_sum_of_card_eq {ι : Type*} {A B : Finset ι} (f : ι → ℝ) (hAB : #A = #B)
    (h : ∀ a ∈ A, ∀ b ∈ B, f a ≤ f b) : ∑ i ∈ A, f i ≤ ∑ i ∈ B, f i := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · rw [card_empty, card_eq_zero] at hAB
    simp [hAB]
  obtain ⟨b₀, hb₀, hmin⟩ := B.exists_min_image f hB
  calc ∑ i ∈ A, f i ≤ #A • f b₀ := sum_le_card_nsmul _ _ _ fun a ha => h a ha b₀ hb₀
    _ = #B • f b₀ := by rw [hAB]
    _ ≤ ∑ i ∈ B, f i := card_nsmul_le_sum _ _ _ hmin

/-- For an antitone `g`, the first `l` terms have the largest sum among sets of as many
terms. -/
lemma sum_le_sum_lt_of_antitone {m : ℕ} {g : Fin m → ℝ} (hg : Antitone g) (l : ℕ)
    (T : Finset (Fin m)) (hT : #T = #{i : Fin m | i.val < l}) :
    ∑ i ∈ T, g i ≤ ∑ i with i.val < l, g i := by
  obtain ⟨I, hI⟩ : ∃ I, I = ({i : Fin m | i.val < l} : Finset (Fin m)) := ⟨_, rfl⟩
  rw [← hI] at hT ⊢
  rw [← sum_inter_add_sum_sdiff T I, ← sum_inter_add_sum_sdiff I T, inter_comm I T]
  refine add_le_add le_rfl (sum_le_sum_of_card_eq g ?_ fun a ha b hb => ?_)
  · have h1 := card_sdiff_add_card_inter T I
    have h2 := card_sdiff_add_card_inter I T
    rw [inter_comm I T] at h2
    omega
  · rw [hI] at ha hb
    simp only [mem_sdiff, mem_filter, mem_univ, true_and] at ha hb
    exact hg (Fin.le_def.2 (by omega))

/-- Proposition 1 of BCEKMN17, proved in this file; `multinomial_schurConvex` restates it. -/
theorem expect_le_of_majorizes (p q : Distribution σ) (hpq : Majorizes p.weight q.weight)
    (φ : (Fin n → σ) → ℝ) (hφ : SchurConvex φ) :
    (Distribution.independent fun _ : Fin n => q).expect φ ≤
      (Distribution.independent fun _ : Fin n => p).expect φ := by
  -- enumerate the colours in decreasing order of `q`, and of `p`
  obtain ⟨eq, hq⟩ := exists_equiv_antitone q.weight
  obtain ⟨ep, hp⟩ := exists_equiv_antitone p.weight
  -- relabel `p` so that it is decreasing along the enumeration of `q`
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm σ, π = eq.symm.trans ep := ⟨_, rfl⟩
  let p' : Distribution σ :=
    ⟨fun c => p.weight (π c), fun _ => p.nonneg _, by rw [Equiv.sum_comp π p.weight, p.sum_one]⟩
  rw [← expect_independent_perm hφ π p p' fun _ => rfl]
  refine expect_le_of_partial_sums eq p' q hq (fun l => ?_) hφ
  have h1 : ∑ i with i.val < l, p'.weight (eq i) = ∑ i with i.val < l, p.weight (ep i) := by
    simp [p', hπ]
  -- the top `l` entries of `q` are bounded by `l` entries of `p`, hence by its top `l` ones
  obtain ⟨S', hcard, hsum⟩ := hpq.2 (({i | i.val < l} : Finset _).map eq.toEmbedding)
  rw [sum_map] at hsum
  have h2 : ∑ c ∈ S', p.weight c = ∑ i ∈ S'.map ep.symm.toEmbedding, p.weight (ep i) := by
    simp [sum_map]
  rw [h1]
  refine hsum.trans (h2 ▸ sum_le_sum_lt_of_antitone hp l _ ?_)
  rw [card_map, hcard, card_map]

end ThreeMajority
