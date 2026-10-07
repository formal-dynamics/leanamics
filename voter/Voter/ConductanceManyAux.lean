import Voter.ConductanceTime

/-! # The phase step for many opinions (BGKM16, Lemma 2.3)

Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic
networks*, ICALP 2016 (BGKM16). With `ℓ ≥ 2` opinions present and a threshold `θ ≥ ℓ`, after
`B ≥ 384 vol(V) / (θ d_min φ)` rounds of the lazy voter the number of opinions is at most
`5θ/6` with probability at least `1/3` (`phase_step`). The argument:

* the voter only copies opinions, so the set of opinions present can only shrink
  (`opinions_step_subset`); expectations can be compared on the states reachable from the start
  (`iterate_le_of_closed`);
* fewer than `θ/3` opinions have volume above `3 vol(V)/θ` (`card_big_le`); every other
  opinion `i` is resolved (vanished or prevailed) after `B` rounds with probability at least
  `1/2`, by Lemma 2.2 applied to the two-opinion process "`i` against the rest", which is the
  projection of the voter by `colorIndicator i` (`half_le_iterate_resolved`);
* if at least a quarter of these opinions are resolved and none prevailed, at most
  `ℓ - (ℓ - θ/3)/4 ≤ 5θ/6` opinions remain; reverse Markov gives probability `1/3`
  (BGKM16 says `1/2` "by Markov's inequality"; the constant does not matter).
-/

namespace Voter
open Dynamics Finset

/-! ### Comparing expectations on a closed set of states -/

section Support
variable {α : Type*} [Fintype α]

/-- If `Q` is closed under the transitions of `K` and `F ≤ F'` on `Q`, then
`𝔼_x F(X_n) ≤ 𝔼_x F'(X_n)` from every state `x` of `Q`. -/
lemma iterate_le_of_closed (K : Kernel α) (Q : α → Prop)
    (hQ : ∀ y z, Q y → (K y).weight z ≠ 0 → Q z) {F F' : α → ℝ}
    (hF : ∀ y, Q y → F y ≤ F' y) (n : ℕ) : ∀ x, Q x → K.iterate n F x ≤ K.iterate n F' x := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    intro x hx
    rw [Kernel.iterate_succ, Kernel.iterate_succ]
    unfold Kernel.apply Distribution.expect
    refine sum_le_sum fun z _ => ?_
    by_cases hz : (K x).weight z = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (ih z (hQ x z hx hz)) ((K x).nonneg z)

/-- `𝔼[c - F] = c - 𝔼[F]` at every finite time. -/
lemma iterate_const_sub (K : Kernel α) (n : ℕ) (c : ℝ) (F : α → ℝ) (x : α) :
    K.iterate n (fun y => c - F y) x = c - K.iterate n F x := by
  have h : (fun y => c - F y) = fun y => (fun _ => c) y + (fun y => (-1) * F y) y := by
    funext y
    ring
  rw [h, K.iterate_add, K.iterate_mul, K.iterate_const]
  ring

end Support

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

/-! ### The opinions present -/

/-- A transition of the voter goes to a configuration obtained by copying. -/
lemma transition_weight_ne_zero (H : Kernel V) {x y : Config V C}
    (h : (transition H x).weight y ≠ 0) : ∃ r, step x r = y := by
  classical
  by_contra hne
  push Not at hne
  apply h
  simp only [transition, Distribution.map]
  exact sum_eq_zero fun r _ => by rw [if_neg (hne r)]

variable [DecidableEq C]

/-- The set of opinions present in a configuration. -/
def opinions (x : Config V C) : Finset C := univ.image x

omit [Fintype C] [DecidableEq V] in
lemma mem_opinions {x : Config V C} {c : C} : c ∈ opinions x ↔ ∃ u, x u = c := by
  simp [opinions]

omit [Fintype C] [DecidableEq V] in
/-- Copying cannot create opinions. -/
lemma opinions_step_subset (x : Config V C) (r : V → V) : opinions (step x r) ⊆ opinions x := by
  intro c hc
  obtain ⟨u, rfl⟩ := mem_opinions.mp hc
  exact mem_opinions.mpr ⟨r u, rfl⟩

/-- The configurations whose opinions lie in a fixed set are closed under the voter. -/
lemma opinions_closed (H : Kernel V) (O : Finset C) :
    ∀ y z : Config V C, opinions y ⊆ O → (transition H y).weight z ≠ 0 → opinions z ⊆ O := by
  intro y z hy hz
  obtain ⟨r, rfl⟩ := transition_weight_ne_zero H hz
  exact (opinions_step_subset y r).trans hy

omit [Fintype C] [DecidableEq V] in
/-- With at least one vertex, disagreement means at least two opinions. -/
lemma disagreement_eq_opinions [Nonempty V] (x : Config V C) :
    disagreement x = if 2 ≤ (opinions x).card then 1 else 0 := by
  classical
  unfold disagreement
  obtain ⟨v⟩ := ‹Nonempty V›
  have hiff : (∃ c, x = fun _ => c) ↔ ¬ 2 ≤ (opinions x).card := by
    rw [not_le, Nat.lt_succ_iff, card_le_one]
    constructor
    · rintro ⟨c, rfl⟩ a ha b hb
      obtain ⟨u, rfl⟩ := mem_opinions.mp ha
      obtain ⟨w, rfl⟩ := mem_opinions.mp hb
      rfl
    · intro h
      exact ⟨x v, funext fun u =>
        h _ (mem_opinions.mpr ⟨u, rfl⟩) _ (mem_opinions.mpr ⟨v, rfl⟩)⟩
  by_cases h : ∃ c, x = fun _ => c
  · rw [if_pos h, if_neg (hiff.mp h)]
  · rw [if_neg h, if_pos (not_not.mp (fun h' => h (hiff.mpr h')))]

/-! ### Volumes of the opinions -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype C] [DecidableEq V] in
/-- The volumes of the opinions present add up to the total volume. -/
lemma sum_vol_opinions (x : Config V C) :
    ∑ i ∈ opinions x, (vol G (univ.filter fun u => x u = i) : ℝ) = vol G univ := by
  unfold vol
  push_cast
  exact sum_fiberwise_of_maps_to (fun u _ => mem_opinions.mpr ⟨u, rfl⟩) _

omit [Fintype C] [DecidableEq V] in
/-- **Few big opinions**: at most `θ/3` of the opinions present have volume above
`3 vol(V)/θ`. -/
lemma card_big_le (x : Config V C) {θ : ℝ} (hθ : 0 < θ) (hW : (0 : ℝ) < vol G univ) :
    (((opinions x).filter fun i =>
      3 * (vol G univ : ℝ) / θ < vol G (univ.filter fun u => x u = i)).card : ℝ) ≤ θ / 3 := by
  set Bg := (opinions x).filter fun i =>
    3 * (vol G univ : ℝ) / θ < vol G (univ.filter fun u => x u = i)
  have h1 : (Bg.card : ℝ) * (3 * (vol G univ : ℝ) / θ) ≤
      ∑ i ∈ Bg, (vol G (univ.filter fun u => x u = i) : ℝ) := by
    rw [← nsmul_eq_mul]
    exact card_nsmul_le_sum _ _ _ fun i hi => (mem_filter.mp hi).2.le
  have h2 : ∑ i ∈ Bg, (vol G (univ.filter fun u => x u = i) : ℝ) ≤ vol G univ := by
    rw [← sum_vol_opinions G x]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
  have h3 : (Bg.card : ℝ) * (3 * (vol G univ : ℝ) / θ) ≤ vol G univ := h1.trans h2
  rw [mul_div_assoc', div_le_iff₀ hθ] at h3
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  nlinarith

/-! ### Resolving one opinion: projection to two opinions -/

omit [DecidableEq V] [Fintype C] in
/-- Opinion `i` is resolved (vanished or prevailed) exactly when the two-opinion projection
"`i` against the rest" is at consensus. -/
lemma one_sub_disagreement_project (i : C) (y : Config V C) :
    1 - disagreement (colorIndicator i ∘ y) =
      if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then 1 else 0 := by
  classical
  unfold disagreement
  have hiff : (∃ c, colorIndicator i ∘ y = fun _ => c) ↔
      (∀ u, y u = i) ∨ (∀ u, y u ≠ i) := by
    constructor
    · rintro ⟨c, hc⟩
      cases c
      · right
        intro u
        have := congrFun hc u
        simpa [colorIndicator] using this
      · left
        intro u
        have := congrFun hc u
        simpa [colorIndicator] using this
    · rintro (h | h)
      · exact ⟨true, funext fun u => by simp [colorIndicator, h u]⟩
      · exact ⟨false, funext fun u => by simp [colorIndicator, h u]⟩
  by_cases h : (∀ u, y u = i) ∨ (∀ u, y u ≠ i)
  · rw [if_pos (hiff.mpr h), if_pos h]
    norm_num
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    norm_num

/-- **One opinion is resolved with probability `1/2`** (BGKM16, Lemma 2.2 applied to the
process "`i` against the rest"): if `128 vol(i) ≤ d_min φ B`, then opinion `i` has vanished or
prevailed after `B` rounds with probability at least `1/2`. -/
lemma half_le_iterate_resolved (hd : ∀ v, 0 < G.degree v) (x : Config V C) (i : C) (B : ℕ)
    (hB : 128 * (vol G (univ.filter fun u => x u = i) : ℝ) ≤
      G.minDegree * conductance G * B) :
    1 / 2 ≤ (transition (lazyNeighbor G hd)).iterate B
      (fun y : Config V C => if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then 1 else 0) x := by
  have hfun : (fun y : Config V C => if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then (1 : ℝ) else 0) =
      fun y => 1 - disagreement (colorIndicator i ∘ y) :=
    funext fun y => (one_sub_disagreement_project i y).symm
  rw [hfun, iterate_const_sub, ← iterate_project]
  -- the projection has minority volume at most `vol(i)`
  have hvol : (vol G (minority G (colorIndicator i ∘ x)) : ℝ) ≤
      vol G (univ.filter fun u => x u = i) := by
    have h := vol_minority_le G (colorIndicator i ∘ x) true
    have he : (univ.filter fun u => (colorIndicator i ∘ x) u = true) =
        univ.filter fun u => x u = i := by
      ext u
      simp [colorIndicator]
    rw [he] at h
    exact_mod_cast h
  have h := lazy_consensus_of_minority G hd (colorIndicator i ∘ x) B (by linarith)
  linarith

/-! ### The phase step -/

omit [Fintype C] [DecidableEq V] in
/-- **Counting after a phase** (pointwise part of Lemma 2.3 of BGKM16). Let `S` be a set of
opinions present in `x`, with `|S| ≥ ℓ - θ/3`, where `2 ≤ ℓ ≤ θ` is the number of opinions of
`x`, and let `R(y)` count the opinions of `S` resolved in `y`. For every `y` whose opinions are
opinions of `x`: if more than `5θ/6` opinions remain in `y`, then fewer than `|S|/4` opinions of
`S` are resolved, so `(3|S|/4) · 1[more than 5θ/6 opinions] ≤ |S| - R(y)`. -/
lemma phase_count [Nonempty V] (x y : Config V C) (S : Finset C) (hS : S ⊆ opinions x)
    {θ : ℝ} (h2 : 2 ≤ (opinions x).card) (hθ : ((opinions x).card : ℝ) ≤ θ)
    (hSθ : ((opinions x).card : ℝ) - θ / 3 ≤ S.card) (hy : opinions y ⊆ opinions x) :
    3 * S.card / 4 * (if θ * (5 / 6) < (opinions y).card then (1 : ℝ) else 0) ≤
      S.card - ∑ i ∈ S, (if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then (1 : ℝ) else 0) := by
  classical
  set Res := S.filter fun i => (∀ u, y u = i) ∨ (∀ u, y u ≠ i)
  have hR : ∑ i ∈ S, (if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then (1 : ℝ) else 0) = Res.card := by
    rw [← sum_filter, sum_const, nsmul_one]
  rw [hR]
  have hResS : (Res.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card (filter_subset _ _)
  split_ifs with hbad
  · -- more than `5θ/6` opinions remain: few opinions of `S` are resolved
    rw [mul_one]
    by_contra hcon
    push Not at hcon
    have hθ2 : (2 : ℝ) ≤ θ := le_trans (by exact_mod_cast h2) hθ
    by_cases hprev : ∃ i ∈ S, ∀ u, y u = i
    · -- an opinion prevailed: one opinion remains
      obtain ⟨i, -, hi⟩ := hprev
      have h1 : opinions y ⊆ {i} := fun c hc => by
        obtain ⟨u, rfl⟩ := mem_opinions.mp hc
        simp [hi u]
      have := card_le_card h1
      rw [card_singleton] at this
      have : ((opinions y).card : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
    · -- the resolved opinions of `S` vanished
      push Not at hprev
      have hsub : opinions y ⊆ opinions x \ Res := by
        intro c hc
        rw [mem_sdiff]
        refine ⟨hy hc, fun hcR => ?_⟩
        obtain ⟨hcS, hres⟩ := mem_filter.mp hcR
        obtain ⟨u, hu⟩ := mem_opinions.mp hc
        rcases hres with h | h
        · obtain ⟨w, hw⟩ := hprev c hcS
          exact hw (h w)
        · exact h u hu
      have hcard := card_le_card hsub
      rw [card_sdiff_of_subset ((filter_subset _ _).trans hS)] at hcard
      have hcard' : ((opinions y).card : ℝ) ≤ (opinions x).card - Res.card := by
        have hle : Res.card ≤ (opinions x).card :=
          card_le_card ((filter_subset _ _).trans hS)
        rw [← Nat.cast_sub hle]
        exact_mod_cast hcard
      nlinarith
  · rw [mul_zero]
    linarith

/-- **The phase step** (Lemma 2.3 of BGKM16). Without isolated vertices, from a configuration
with `2 ≤ ℓ ≤ θ` opinions, after `B` rounds with `384 vol(V) ≤ θ d_min φ B` the lazy voter has
more than `5θ/6` opinions with probability at most `2/3`. -/
theorem phase_step [Nonempty V] (hd : ∀ v, 0 < G.degree v) (x : Config V C) {θ : ℝ} (B : ℕ)
    (h2 : 2 ≤ (opinions x).card) (hθ : ((opinions x).card : ℝ) ≤ θ)
    (hB : 384 * (vol G univ : ℝ) ≤ θ * (G.minDegree * conductance G * B)) :
    (transition (lazyNeighbor G hd)).iterate B
      (fun y : Config V C => if θ * (5 / 6) < (opinions y).card then 1 else 0) x ≤ 2 / 3 := by
  classical
  set K : Kernel (Config V C) := transition (lazyNeighbor G hd)
  have hW : (0 : ℝ) < vol G univ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact_mod_cast vol_pos hd (univ_nonempty_iff.mpr ⟨v⟩)
  set W : ℝ := (vol G univ : ℝ)
  have hθ2 : (2 : ℝ) ≤ θ := le_trans (by exact_mod_cast h2) hθ
  have hθ0 : 0 < θ := by linarith
  -- the small opinions
  set S := (opinions x).filter fun i => (vol G (univ.filter fun u => x u = i) : ℝ) ≤ 3 * W / θ
  have hSθ : ((opinions x).card : ℝ) - θ / 3 ≤ S.card := by
    have hbig := card_big_le G x hθ0 hW
    have hsplit := card_filter_add_card_filter_not (s := opinions x)
      (fun i => (vol G (univ.filter fun u => x u = i) : ℝ) ≤ 3 * W / θ)
    have hneg : ((opinions x).filter fun i =>
        ¬ (vol G (univ.filter fun u => x u = i) : ℝ) ≤ 3 * W / θ) =
        (opinions x).filter fun i => 3 * W / θ < vol G (univ.filter fun u => x u = i) := by
      simp_rw [not_le]
    rw [hneg] at hsplit
    have : ((opinions x).card : ℝ) = S.card + ((opinions x).filter fun i =>
        3 * W / θ < vol G (univ.filter fun u => x u = i)).card := by
      exact_mod_cast hsplit.symm
    linarith
  -- each small opinion is resolved with probability at least `1/2`
  have hres : ∀ i ∈ S, 1 / 2 ≤ K.iterate B
      (fun y : Config V C => if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then 1 else 0) x := by
    intro i hi
    refine half_le_iterate_resolved G hd x i B ?_
    have hvi := (mem_filter.mp hi).2
    have h128 : 128 * (3 * W / θ) ≤ G.minDegree * conductance G * B := by
      rw [mul_div_assoc', div_le_iff₀ hθ0]
      linarith
    linarith
  have hER : (S.card : ℝ) / 2 ≤ K.iterate B (fun y : Config V C => ∑ i ∈ S,
      (if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then (1 : ℝ) else 0)) x := by
    rw [iterate_finset_sum]
    calc (S.card : ℝ) / 2 = ∑ i ∈ S, (1 / 2 : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := sum_le_sum hres
  -- compare on the configurations whose opinions are opinions of `x`
  have hcmp := iterate_le_of_closed K (fun y => opinions y ⊆ opinions x)
    (opinions_closed (lazyNeighbor G hd) (opinions x))
    (F := fun y : Config V C =>
      3 * S.card / 4 * (if θ * (5 / 6) < (opinions y).card then (1 : ℝ) else 0))
    (F' := fun y : Config V C => S.card - ∑ i ∈ S,
      (if (∀ u, y u = i) ∨ (∀ u, y u ≠ i) then (1 : ℝ) else 0))
    (fun y hy => phase_count x y S (filter_subset _ _) h2 hθ hSθ hy) B x subset_rfl
  rw [K.iterate_mul, iterate_const_sub] at hcmp
  set E := K.iterate B
    (fun y : Config V C => if θ * (5 / 6) < (opinions y).card then (1 : ℝ) else 0) x
  rcases Nat.eq_zero_or_pos S.card with hS0 | hS0
  · -- no small opinion: then at most `θ/3 < 5θ/6` opinions, and none can appear
    have hle : ((opinions x).card : ℝ) ≤ θ / 3 := by
      rw [hS0, Nat.cast_zero] at hSθ
      linarith
    have h0 := iterate_le_of_closed K (fun y => opinions y ⊆ opinions x)
      (opinions_closed (lazyNeighbor G hd) (opinions x))
      (F := fun y : Config V C => if θ * (5 / 6) < (opinions y).card then (1 : ℝ) else 0)
      (F' := fun _ => 0)
      (fun y hy => by
        have : ((opinions y).card : ℝ) ≤ (opinions x).card := by
          exact_mod_cast card_le_card hy
        rw [if_neg (by linarith)]) B x subset_rfl
    rw [K.iterate_const] at h0
    change E ≤ 0 at h0
    linarith
  · have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS0
    have : 3 * S.card / 4 * E ≤ S.card / 2 := by linarith
    nlinarith

end Voter
