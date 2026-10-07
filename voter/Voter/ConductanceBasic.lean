import Voter.Conductance

/-! # Basic facts on volume, minority side, potential, cut and conductance (VOT-5)

Helpers for the proofs of Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the
voter model in dynamic networks*, ICALP 2016 (BGKM16):

* volumes: `vol_univ` (`= 2m`), `vol_pos`, `vol_eq_zero_iff`;
* the minority side is a colour class of volume `min(vol F, vol T) ≤ m` (`exists_minority_eq`,
  `vol_minority_le`, `vol_minority_le_edges`), empty exactly at consensus
  (`minority_eq_empty_iff`), and so is the potential (`potential_eq_zero_iff`);
* the cut between a colour class and its complement counts the discordant neighbours from either
  side (`card_interedges_class`, `card_interedges_class_compl`);
* the conductance is a lower bound for the cut ratios (`conductance_mul_vol_le`), nonnegative,
  at most one;
* one lazy step (from `lazyNeighbor_expect` in `Lazy.lean`): the probability `1/2` of moving
  and the probability `λ_u / (2 d_u)` of adopting another opinion;
* two real inequalities: the third-order Taylor bound of `√` and a chord bound.
-/

namespace Voter
open Dynamics Finset

variable {V C : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Volumes -/

omit [DecidableEq V] in
/-- The total volume is twice the number of edges. -/
lemma vol_univ : vol G univ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- A set and its complement share the total volume. -/
lemma vol_add_vol_compl (S : Finset V) : vol G S + vol G Sᶜ = vol G univ :=
  sum_add_sum_compl S _

/-- The two colour classes of a two-opinion configuration share the total volume. -/
lemma vol_false_add_vol_true (s : Config V Bool) :
    vol G (univ.filter fun u => s u = false) + vol G (univ.filter fun u => s u = true) =
      vol G univ := by
  unfold vol
  rw [← sum_union]
  · congr 1
    ext u
    cases s u <;> simp
  · rw [disjoint_filter]
    intro u _ h
    simp [h]

omit [DecidableEq V] in
/-- Without isolated vertices, a nonempty set has positive volume. -/
lemma vol_pos {G} [DecidableRel G.Adj] (hd : ∀ v, 0 < G.degree v) {S : Finset V}
    (hS : S.Nonempty) : 0 < vol G S :=
  sum_pos (fun v _ => hd v) hS

/-- Without isolated vertices, a set has zero volume exactly when it is empty. -/
lemma vol_eq_zero_iff {G} [DecidableRel G.Adj] (hd : ∀ v, 0 < G.degree v) (S : Finset V) :
    vol G S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact (vol_pos hd (nonempty_iff_ne_empty.mpr hne)).ne' h
  · rintro rfl
    simp [vol]

omit [DecidableEq V] in
/-- Volume is monotone. -/
lemma vol_mono {S T : Finset V} (h : S ⊆ T) : vol G S ≤ vol G T :=
  sum_le_sum_of_subset h

/-! ### The minority side and the potential -/

omit [DecidableEq V] in
/-- The minority side is the colour class of some opinion `b`. -/
lemma exists_minority_eq (s : Config V Bool) :
    ∃ b, minority G s = univ.filter fun u => s u = b := by
  unfold minority
  split_ifs
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

omit [DecidableEq V] in
/-- The minority side has at most the volume of either colour class. -/
lemma vol_minority_le (s : Config V Bool) (b : Bool) :
    vol G (minority G s) ≤ vol G (univ.filter fun u => s u = b) := by
  unfold minority
  split_ifs with h <;> cases b <;> omega

/-- The minority side has volume at most the number of edges `m`. -/
lemma vol_minority_le_edges (s : Config V Bool) :
    vol G (minority G s) ≤ G.edgeFinset.card := by
  have h1 := vol_minority_le G s false
  have h2 := vol_minority_le G s true
  have h3 := vol_false_add_vol_true G s
  rw [vol_univ] at h3
  omega

/-- Without isolated vertices, the minority side is empty exactly at consensus. -/
lemma minority_eq_empty_iff (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) :
    minority G s = ∅ ↔ ∃ c, s = fun _ => c := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_minority_eq G s
    refine ⟨!b, funext fun u => ?_⟩
    have hu : u ∉ minority G s := by simp [h]
    rw [hb] at hu
    have hu' : s u ≠ b := by simpa using hu
    revert hu'
    cases s u <;> cases b <;> simp
  · rintro ⟨c, rfl⟩
    have h := vol_minority_le G (fun _ => c) (!c)
    have h0 : (univ.filter fun _ : V => c = !c) = ∅ := by
      ext u
      cases c <;> simp
    rw [h0] at h
    have : vol G (minority G fun _ => c) = 0 := by simpa [vol] using h
    exact (vol_eq_zero_iff hd _).mp this

omit [DecidableEq V] in
/-- The potential is nonnegative. -/
lemma potential_nonneg (s : Config V Bool) : 0 ≤ potential G s := Real.sqrt_nonneg _

omit [DecidableEq V] in
/-- The square of the potential is the minority volume. -/
lemma potential_sq (s : Config V Bool) : potential G s ^ 2 = vol G (minority G s) :=
  Real.sq_sqrt (Nat.cast_nonneg _)

omit [DecidableEq V] in
/-- Without isolated vertices, the potential is positive exactly when the minority side is
nonempty. -/
lemma potential_pos_iff (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) :
    0 < potential G s ↔ (minority G s).Nonempty := by
  unfold potential
  rw [Real.sqrt_pos, Nat.cast_pos]
  constructor
  · intro h
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp [hne, vol] at h
  · exact vol_pos hd

/-- Without isolated vertices, the potential vanishes exactly at consensus. -/
lemma potential_eq_zero_iff (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) :
    potential G s = 0 ↔ ∃ c, s = fun _ => c := by
  rw [← minority_eq_empty_iff G hd, ← not_nonempty_iff_eq_empty, ← potential_pos_iff G hd]
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm (not_lt.mp h) (potential_nonneg G s)

/-- Without isolated vertices, the disagreement indicator is the indicator of a positive
potential. -/
lemma disagreement_eq_potential (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) :
    disagreement s = 1 - if potential G s = 0 then 1 else 0 := by
  classical
  unfold disagreement
  by_cases h : ∃ c, s = fun _ => c
  · rw [if_pos h, if_pos ((potential_eq_zero_iff G hd s).mpr h)]
    norm_num
  · rw [if_neg h, if_neg (fun h' => h ((potential_eq_zero_iff G hd s).mp h'))]
    norm_num

omit [DecidableEq V] in
/-- The potential depends on the graph only through the degrees. -/
lemma potential_congr {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ v, G'.degree v = G.degree v) : potential G' = potential G := by
  have hvol : ∀ S, vol G' S = vol G S := fun S => sum_congr rfl fun v _ => h v
  funext s
  simp only [potential, minority, hvol]

omit [DecidableEq V] in
/-- The minimum degree depends on the graph only through the degrees. -/
lemma minDegree_congr {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ v, G'.degree v = G.degree v) : G'.minDegree = G.minDegree := by
  unfold SimpleGraph.minDegree
  simp_rw [h]

/-! ### Cuts -/

/-- The edges from `U` to `T` counted from `U`. -/
lemma card_interedges_eq_sum (U T : Finset V) :
    (G.interedges U T).card = ∑ u ∈ U, ((G.neighborFinset u).filter (· ∈ T)).card := by
  rw [SimpleGraph.interedges_def, card_filter, sum_product]
  refine sum_congr rfl fun u _ => ?_
  have h : (G.neighborFinset u).filter (· ∈ T) = T.filter (G.Adj u) := by
    ext w
    simp [and_comm]
  rw [h, card_filter]

omit [Fintype V] [DecidableEq V] in
/-- The number of edges between two sets does not depend on the order. -/
lemma card_interedges_comm (U T : Finset V) :
    (G.interedges U T).card = (G.interedges T U).card := by
  refine card_bij (fun x _ => x.swap) (fun x hx => ?_) (fun _ _ _ _ h => Prod.swap_injective h)
    (fun x hx => ⟨x.swap, ?_, x.swap_swap⟩)
  · rw [SimpleGraph.mem_interedges_iff] at hx ⊢
    exact ⟨hx.2.1, hx.1, hx.2.2.symm⟩
  · rw [SimpleGraph.mem_interedges_iff] at hx ⊢
    exact ⟨hx.2.1, hx.1, hx.2.2.symm⟩

/-- The cut of a colour class counts the discordant neighbours of its vertices. -/
lemma card_interedges_class (s : Config V Bool) (b : Bool) :
    (G.interedges (univ.filter fun u => s u = b) (univ.filter fun u => s u = b)ᶜ).card =
      ∑ u ∈ univ.filter (fun u => s u = b), discordant G s u := by
  rw [card_interedges_eq_sum]
  refine sum_congr rfl fun u hu => ?_
  rw [mem_filter] at hu
  unfold discordant
  congr 1
  ext w
  simp [hu.2]

/-- The cut of a colour class counts the discordant neighbours of the other vertices. -/
lemma card_interedges_class_compl (s : Config V Bool) (b : Bool) :
    (G.interedges (univ.filter fun u => s u = b) (univ.filter fun u => s u = b)ᶜ).card =
      ∑ u ∈ (univ.filter fun u => s u = b)ᶜ, discordant G s u := by
  rw [card_interedges_comm, card_interedges_eq_sum]
  refine sum_congr rfl fun u hu => ?_
  have hu' : s u ≠ b := by simpa using hu
  unfold discordant
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
  · rw [h2]
    exact Ne.symm hu'
  · revert h2 hu'
    cases s w <;> cases s u <;> cases b <;> simp

omit [DecidableEq V] in
/-- Discordant neighbours are neighbours. -/
lemma discordant_le_degree [DecidableEq C] (s : Config V C) (u : V) :
    discordant G s u ≤ G.degree u := by
  unfold discordant
  exact (card_filter_le _ _).trans (G.card_neighborFinset_eq_degree u).le

/-- A cut is at most the volume of either side. -/
lemma card_interedges_compl_le_vol (U : Finset V) :
    (G.interedges U Uᶜ).card ≤ vol G U := by
  rw [card_interedges_eq_sum]
  exact sum_le_sum fun u _ => (card_filter_le _ _).trans (G.card_neighborFinset_eq_degree u).le

/-! ### Conductance -/

/-- The conductance is nonnegative. -/
lemma conductance_nonneg : 0 ≤ conductance G :=
  Real.iInf_nonneg fun _ => by positivity

/-- **Definition of the conductance**: every cut ratio is at least `φ`, i.e.
`φ vol(U) ≤ |cut(U, V ∖ U)|` whenever `0 < vol(U) ≤ m`. -/
lemma conductance_mul_vol_le (U : Finset V) (h0 : 0 < vol G U)
    (hm : vol G U ≤ G.edgeFinset.card) :
    conductance G * vol G U ≤ (G.interedges U Uᶜ).card := by
  have hle : conductance G ≤ ((G.interedges U Uᶜ).card : ℝ) / vol G U :=
    ciInf_le (Set.finite_range _).bddBelow
      (⟨U, h0, hm⟩ : {U : Finset V // 0 < vol G U ∧ vol G U ≤ G.edgeFinset.card})
  rwa [le_div_iff₀ (by exact_mod_cast h0)] at hle

/-- The conductance is at most one. -/
lemma conductance_le_one : conductance G ≤ 1 := by
  by_cases hne : Nonempty {U : Finset V // 0 < vol G U ∧ vol G U ≤ G.edgeFinset.card}
  · obtain ⟨U, h0, hm⟩ := hne
    have h := conductance_mul_vol_le G U h0 hm
    have hc : ((G.interedges U Uᶜ).card : ℝ) ≤ vol G U := by
      exact_mod_cast card_interedges_compl_le_vol G U
    have hv : (0 : ℝ) < vol G U := by exact_mod_cast h0
    nlinarith
  · rw [not_nonempty_iff] at hne
    simp [conductance]

/-! ### One lazy step -/

/-- The lazy voter moves with probability exactly `1/2` (a simple graph has no loops). -/
lemma lazyNeighbor_expect_ne_self (hd : ∀ v, 0 < G.degree v) (u : V) :
    (lazyNeighbor G hd u).expect (fun a => if a ≠ u then 1 else 0) = 1 / 2 := by
  rw [lazyNeighbor_expect]
  have h : ∑ a ∈ G.neighborFinset u, (if a ≠ u then (1 : ℝ) else 0) = G.degree u := by
    rw [sum_congr rfl fun a ha => if_pos (G.ne_of_adj ((G.mem_neighborFinset u a).mp ha)).symm]
    simp
  have hdu : (G.degree u : ℝ) ≠ 0 := by exact_mod_cast (hd u).ne'
  rw [h, if_neg (not_not.mpr rfl)]
  field_simp
  ring

/-- The lazy voter adopts another opinion with probability `λ_u / (2 d_u)`. -/
lemma lazyNeighbor_expect_discordant [DecidableEq C] (hd : ∀ v, 0 < G.degree v)
    (s : Config V C) (u : V) :
    (lazyNeighbor G hd u).expect (fun a => if s a ≠ s u then 1 else 0) =
      discordant G s u / (2 * G.degree u) := by
  rw [lazyNeighbor_expect, if_neg (not_not.mpr rfl), ← sum_filter, sum_const, nsmul_one]
  unfold discordant
  ring

/-! ### Two real inequalities -/

/-- **Third-order Taylor bound for `√`** (proof of Lemma 2.1 of BGKM16): for `P > 0` and
`P + x ≥ 0`, `√(P + x) ≤ √P (1 + x/(2P) - x²/(8P²) + x³/(16P³))`. With `t = √(P + x)` and
`r = √P`, the difference times `16 r⁵` is `(t - r)⁴ (t² + 4tr + 5r²) ≥ 0`. -/
lemma sqrt_add_le_taylor {P x : ℝ} (hP : 0 < P) (hx : 0 ≤ P + x) :
    Real.sqrt (P + x) ≤
      Real.sqrt P * (1 + x / (2 * P) - x ^ 2 / (8 * P ^ 2) + x ^ 3 / (16 * P ^ 3)) := by
  set t := Real.sqrt (P + x) with ht
  set r := Real.sqrt P with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hP
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hP' : P = r ^ 2 := (Real.sq_sqrt hP.le).symm
  have ht2 : t ^ 2 = P + x := Real.sq_sqrt hx
  have hx' : x = t ^ 2 - r ^ 2 := by rw [ht2, ← hP']; ring
  have key : 0 ≤ (t - r) ^ 4 * (t ^ 2 + 4 * t * r + 5 * r ^ 2) := by positivity
  rw [hx', hP']
  have hr5 : 0 < 16 * r ^ 5 := by positivity
  rw [← sub_nonneg]
  have hid : r * (1 + (t ^ 2 - r ^ 2) / (2 * (r ^ 2)) - (t ^ 2 - r ^ 2) ^ 2 / (8 * (r ^ 2) ^ 2) +
      (t ^ 2 - r ^ 2) ^ 3 / (16 * (r ^ 2) ^ 3)) - t =
      (t - r) ^ 4 * (t ^ 2 + 4 * t * r + 5 * r ^ 2) / (16 * r ^ 5) := by
    field_simp
    ring
  rw [hid]
  positivity

/-- **Chord bound for `√`**: for `z ≥ 0` and `0 ≤ l ≤ d`,
`l √(z + d) + (d - l) √z ≤ d √(z + l)` (concavity of `√`). -/
lemma sqrt_chord {z l d : ℝ} (hz : 0 ≤ z) (hl : 0 ≤ l) (hld : l ≤ d) :
    l * Real.sqrt (z + d) + (d - l) * Real.sqrt z ≤ d * Real.sqrt (z + l) := by
  set α := Real.sqrt z
  set β := Real.sqrt (z + d)
  set γ := Real.sqrt (z + l)
  have hα : α ^ 2 = z := Real.sq_sqrt hz
  have hβ : β ^ 2 = z + d := Real.sq_sqrt (by linarith)
  have hγ : γ ^ 2 = z + l := Real.sq_sqrt (by linarith)
  have hαγ : α ≤ γ := Real.sqrt_le_sqrt (by linarith)
  have hγβ : γ ≤ β := Real.sqrt_le_sqrt (by linarith)
  have hl' : l = γ ^ 2 - α ^ 2 := by rw [hγ, hα]; ring
  have hd' : d = β ^ 2 - α ^ 2 := by rw [hβ, hα]; ring
  rw [hl', hd']
  have key : 0 ≤ (β - α) * (γ - α) * (β - γ) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith [key]

end Voter
