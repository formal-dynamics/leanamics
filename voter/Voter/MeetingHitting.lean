import Voter.Graph
import Voter.Uniform

/-! # Hitting times of the lazy random walk through the graph Laplacian (VOT-6 helpers)

Hassin–Peleg §2.4 (Fact 2.3) for the lazy uniform walk on a connected graph `G`, in finite
linear algebra with Mathlib's Laplacian `L = G.lapMatrix ℝ`.

The expected hitting time `Z_{x,y}` of `y` from `x` for the lazy walk (stay with probability
`1/2`, otherwise move to a uniform neighbour) solves `h y = 0` and `(L h) x = 2 d_x` for
`x ≠ y`. We only use this linear system, never the probabilistic interpretation:

* `exists_hitting`: the system has a solution (injectivity by the maximum principle
  `le_zero_of_lapMatrix_le`, which reuses `boundary_edge`), named `hitting G hc y`;
* `hitting_nonneg` (minimum principle) and `hitting_lapMatrix_apply`: `(L h) y = 2 d_y − 2 vol`;
* `hitting_symm`: `Σ_z d_z h_y z − vol h_y x = Σ_z d_z h_x z − vol h_x y`, the reversibility
  identity `E_x T_y − E_y T_x = E_π T_y − E_π T_x`, from the symmetry of `L`;
* `hitting_add_hitting_le`: the commute bound `h_y x + h_x y ≤ 4 vol (n − 1)`, from the energy
  identity `ψᵀ L ψ = Σ_{i ∼ j} (ψ i − ψ j)² / 2` and Cauchy–Schwarz along a path.
-/

namespace Voter
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The Laplacian -/

/-- The entries of `L u` sum to zero. -/
lemma sum_lapMatrix_mulVec (u : V → ℝ) : ∑ x, (G.lapMatrix ℝ *ᵥ u) x = 0 := by
  have h1 : ∑ x, (G.lapMatrix ℝ *ᵥ u) x = (fun _ => (1 : ℝ)) ⬝ᵥ (G.lapMatrix ℝ *ᵥ u) := by
    simp [dotProduct]
  rw [h1, dotProduct_mulVec, ← mulVec_transpose, (G.isSymm_lapMatrix ℝ).eq,
    G.lapMatrix_mulVec_const_eq_zero, zero_dotProduct]

/-- The Laplacian is symmetric. -/
lemma dotProduct_lapMatrix_comm (u w : V → ℝ) :
    u ⬝ᵥ (G.lapMatrix ℝ *ᵥ w) = w ⬝ᵥ (G.lapMatrix ℝ *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, (G.isSymm_lapMatrix ℝ).eq, dotProduct_comm]

/-- **Maximum principle.** A function that is subharmonic off `y` and nonpositive at `y` is
nonpositive on a connected graph. -/
lemma le_zero_of_lapMatrix_le (hc : G.Connected) {u : V → ℝ} {y : V} (hy : u y ≤ 0)
    (hsub : ∀ x, x ≠ y → (G.lapMatrix ℝ *ᵥ u) x ≤ 0) (x : V) : u x ≤ 0 := by
  by_contra hpos
  push Not at hpos
  obtain ⟨z, -, hz⟩ := Finset.exists_max_image univ u ⟨x, mem_univ x⟩
  set S := univ.filter fun w => u w = u z with hS
  have hzS : z ∈ S := by simp [hS]
  have hyS : y ∉ S := by
    simp only [hS, mem_filter, mem_univ, true_and]
    intro h
    have := hz x (mem_univ x)
    linarith
  have hproper : S ≠ univ := fun h => hyS (h ▸ mem_univ y)
  obtain ⟨i, hiS, j, hjS, hij⟩ := boundary_edge G hc S ⟨z, hzS⟩ hproper
  have hiz : u i = u z := (mem_filter.mp hiS).2
  have hjz : u j < u z := lt_of_le_of_ne (hz j (mem_univ j))
    (fun h => hjS (mem_filter.mpr ⟨mem_univ j, h⟩))
  have hiy : i ≠ y := fun h => hyS (h ▸ hiS)
  have hlap := hsub i hiy
  rw [SimpleGraph.lapMatrix_mulVec_apply, hiz] at hlap
  have hlt : ∑ w ∈ G.neighborFinset i, u w < ∑ w ∈ G.neighborFinset i, u z :=
    Finset.sum_lt_sum (fun w _ => hz w (mem_univ w))
      ⟨j, (G.mem_neighborFinset i j).mpr hij, hjz⟩
  rw [sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul] at hlt
  linarith

/-! ### Hitting times -/

/-- The hitting-time system `h y = 0`, `(L h) x = 2 d_x` for `x ≠ y` has a solution. -/
lemma exists_hitting (hc : G.Connected) (y : V) :
    ∃ h : V → ℝ, h y = 0 ∧ ∀ x, x ≠ y → (G.lapMatrix ℝ *ᵥ h) x = 2 * G.degree x := by
  let Φ : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun u x => if x = y then u y else (G.lapMatrix ℝ *ᵥ u) x
      map_add' := fun u w => by
        funext x
        by_cases hx : x = y <;> simp [hx, mulVec_add]
      map_smul' := fun c u => by
        funext x
        by_cases hx : x = y <;> simp [hx, mulVec_smul] }
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).mpr fun u hu => ?_
    have hval (x : V) : (if x = y then u y else (G.lapMatrix ℝ *ᵥ u) x) = 0 := congrFun hu x
    have hy : u y = 0 := by simpa using hval y
    have hlap (x : V) (hx : x ≠ y) : (G.lapMatrix ℝ *ᵥ u) x = 0 := by simpa [hx] using hval x
    funext x
    show u x = 0
    apply le_antisymm
    · exact le_zero_of_lapMatrix_le G hc hy.le (fun x hx => (hlap x hx).le) x
    · have := le_zero_of_lapMatrix_le G hc (u := -u) (y := y) (by simp [hy])
        (fun x hx => by rw [mulVec_neg, Pi.neg_apply, hlap x hx, neg_zero]) x
      simpa using this
  obtain ⟨h, hh⟩ := LinearMap.surjective_of_injective hinj
    (fun x => if x = y then 0 else 2 * (G.degree x : ℝ))
  have hval (x : V) : (if x = y then h y else (G.lapMatrix ℝ *ᵥ h) x) =
      if x = y then 0 else 2 * (G.degree x : ℝ) := congrFun hh x
  exact ⟨h, by simpa using hval y, fun x hx => by simpa [hx] using hval x⟩

/-- Expected hitting time of `y` for the lazy walk (Hassin–Peleg's `Z_{x,y}`), defined as the
solution of its linear system. -/
noncomputable def hitting (hc : G.Connected) (y : V) : V → ℝ :=
  Classical.choose (exists_hitting G hc y)

variable {G} (hc : G.Connected)

@[simp] lemma hitting_self (y : V) : hitting G hc y y = 0 :=
  (Classical.choose_spec (exists_hitting G hc y)).1

lemma hitting_lapMatrix_of_ne {x y : V} (hxy : x ≠ y) :
    (G.lapMatrix ℝ *ᵥ hitting G hc y) x = 2 * G.degree x :=
  (Classical.choose_spec (exists_hitting G hc y)).2 x hxy

/-- The Laplacian of a hitting time everywhere, with `vol = Σ_z d_z`. -/
lemma hitting_lapMatrix_apply (y x : V) :
    (G.lapMatrix ℝ *ᵥ hitting G hc y) x =
      2 * G.degree x - if x = y then 2 * volume G else 0 := by
  by_cases hxy : x = y
  · subst hxy
    have hsum := sum_lapMatrix_mulVec G (hitting G hc x)
    rw [← Finset.add_sum_erase _ _ (mem_univ x),
      Finset.sum_congr rfl fun z hz => hitting_lapMatrix_of_ne hc (mem_erase.mp hz).1,
      ← Finset.mul_sum, Finset.sum_erase_eq_sub (mem_univ x)] at hsum
    rw [if_pos rfl, volume]
    linarith
  · rw [hitting_lapMatrix_of_ne hc hxy, if_neg hxy, sub_zero]

/-- **Minimum principle.** Hitting times are nonnegative. -/
lemma hitting_nonneg (hd : ∀ i, 0 < G.degree i) (y x : V) : 0 ≤ hitting G hc y x := by
  obtain ⟨z, -, hz⟩ := Finset.exists_min_image univ (hitting G hc y) ⟨x, mem_univ x⟩
  by_cases hzy : z = y
  · subst hzy
    simpa using hz x (mem_univ x)
  · exfalso
    have hlap := hitting_lapMatrix_of_ne hc hzy
    rw [SimpleGraph.lapMatrix_mulVec_apply] at hlap
    have hge : ∑ w ∈ G.neighborFinset z, hitting G hc y z ≤
        ∑ w ∈ G.neighborFinset z, hitting G hc y w :=
      Finset.sum_le_sum fun w _ => hz w (mem_univ w)
    rw [sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul] at hge
    have hdz : (0 : ℝ) < G.degree z := by exact_mod_cast hd z
    linarith

/-- `h_y ⬝ L h_x = 2 Σ_z d_z h_y z − 2 vol h_y x`. -/
lemma hitting_dotProduct_lapMatrix (x y : V) :
    hitting G hc y ⬝ᵥ (G.lapMatrix ℝ *ᵥ hitting G hc x) =
      2 * ∑ z, (G.degree z : ℝ) * hitting G hc y z - 2 * volume G * hitting G hc y x := by
  simp only [dotProduct, hitting_lapMatrix_apply, mul_sub, Finset.sum_sub_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', mem_univ, if_true, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun z _ => by ring
  · ring

/-- **Reversibility identity** `E_x T_y − E_y T_x = E_π T_y − E_π T_x`, in the form
`Σ_z d_z h_y z − vol h_y x = Σ_z d_z h_x z − vol h_x y`. -/
lemma hitting_symm (x y : V) :
    ∑ z, (G.degree z : ℝ) * hitting G hc y z - volume G * hitting G hc y x =
      ∑ z, (G.degree z : ℝ) * hitting G hc x z - volume G * hitting G hc x y := by
  have key := dotProduct_lapMatrix_comm G (hitting G hc y) (hitting G hc x)
  rw [hitting_dotProduct_lapMatrix, hitting_dotProduct_lapMatrix] at key
  linarith

/-! ### The commute bound -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Differences along a walk telescope. -/
lemma walk_sum_darts (ψ : V → ℝ) {u v : V} (p : G.Walk u v) :
    (p.darts.map fun d => ψ d.fst - ψ d.snd).sum = ψ u - ψ v := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- Squared differences over distinct darts are bounded by the Dirichlet energy. -/
lemma sum_darts_sq_le (ψ : V → ℝ) (S : Finset G.Dart) :
    ∑ d ∈ S, (ψ d.fst - ψ d.snd) ^ 2 ≤
      ∑ i, ∑ j, if G.Adj i j then (ψ i - ψ j) ^ 2 else 0 := by
  have hinj : Set.InjOn (fun d : G.Dart => d.toProd) S :=
    fun d₁ _ d₂ _ h => SimpleGraph.Dart.ext d₁ d₂ h
  calc ∑ d ∈ S, (ψ d.fst - ψ d.snd) ^ 2
      = ∑ q ∈ S.image (fun d : G.Dart => d.toProd), (ψ q.1 - ψ q.2) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ q ∈ univ.filter (fun q : V × V => G.Adj q.1 q.2), (ψ q.1 - ψ q.2) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨d, -, rfl⟩ := mem_image.mp hq
          simp [d.adj]
        · intros
          positivity
    _ = _ := by rw [Finset.sum_filter, Fintype.sum_prod_type]

/-- **Commute bound** (Hassin–Peleg Fact 2.3, lazy uniform case):
`h_y x + h_x y ≤ 4 vol (n − 1)`. -/
lemma hitting_add_hitting_le (hd : ∀ i, 0 < G.degree i) (x y : V) :
    hitting G hc y x + hitting G hc x y ≤ 4 * volume G * (Fintype.card V - 1) := by
  set ψ : V → ℝ := hitting G hc y - hitting G hc x with hψ
  set c := hitting G hc y x + hitting G hc x y with hc_def
  have hc0 : 0 ≤ c := add_nonneg (hitting_nonneg hc hd y x) (hitting_nonneg hc hd x y)
  have hvol : 0 ≤ volume G := Finset.sum_nonneg fun i _ => by positivity
  -- energy identity
  have henergy : (∑ i, ∑ j, if G.Adj i j then (ψ i - ψ j) ^ 2 else 0) = 4 * volume G * c := by
    have h1 := G.lapMatrix_toLinearMap₂' ℝ ψ
    rw [toLinearMap₂'_apply'] at h1
    have h2 : ψ ⬝ᵥ (G.lapMatrix ℝ *ᵥ ψ) = 2 * volume G * c := by
      rw [hψ, mulVec_sub]
      simp only [dotProduct, Pi.sub_apply, hitting_lapMatrix_apply]
      simp only [sub_sub_sub_cancel_left, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', mem_univ, if_true, hitting_self, hc_def]
      ring
    linarith
  -- a path from `x` to `y`
  obtain ⟨w⟩ := hc.preconnected x y
  set p := w.bypass
  have hp : p.IsPath := w.bypass_isPath
  have hnodup : p.darts.Nodup := SimpleGraph.Walk.darts_nodup_of_support_nodup hp.support_nodup
  have hlen : (p.length : ℝ) ≤ Fintype.card V - 1 := by
    have := hp.length_lt
    have : (p.length : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast this
    linarith
  have htel : ∑ d ∈ p.darts.toFinset, (ψ d.fst - ψ d.snd) = c := by
    rw [List.sum_toFinset _ hnodup, walk_sum_darts]
    simp [hψ, hc_def]
  have hcard : (p.darts.toFinset.card : ℝ) = p.length := by
    rw [List.toFinset_card_of_nodup hnodup, SimpleGraph.Walk.length_darts]
  have hcs := sq_sum_le_card_mul_sum_sq (s := p.darts.toFinset)
    (f := fun d : G.Dart => ψ d.fst - ψ d.snd)
  rw [htel, hcard] at hcs
  have hsq := sum_darts_sq_le ψ p.darts.toFinset
  have hcc : c * c ≤ c * (4 * volume G * p.length) := by
    have hlen0 : (0 : ℝ) ≤ p.length := by positivity
    calc c * c = c ^ 2 := by ring
      _ ≤ p.length * ∑ d ∈ p.darts.toFinset, (ψ d.fst - ψ d.snd) ^ 2 := hcs
      _ ≤ p.length * (4 * volume G * c) :=
          mul_le_mul_of_nonneg_left (hsq.trans henergy.le) hlen0
      _ = c * (4 * volume G * p.length) := by ring
  rcases hc0.lt_or_eq with hpos | hzero
  · have := le_of_mul_le_mul_left hcc hpos
    calc c ≤ 4 * volume G * p.length := this
      _ ≤ 4 * volume G * (Fintype.card V - 1) :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
  · rw [← hzero]
    have : (0 : ℝ) ≤ Fintype.card V - 1 := by
      have : (1 : ℝ) ≤ Fintype.card V := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
      linarith
    positivity

end Voter
