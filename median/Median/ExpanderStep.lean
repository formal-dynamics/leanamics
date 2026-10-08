import Median.ExpanderMixing
import Dynamics.Chernoff

/-! # One round of two-sample voting with a sparse minority

The analysis of one round in the proof of Lemma 12 of Cooper, Elsässer and Radzik (ICALP 2014),
with `α = 3/10`. Write `B` for the minority (vertices whose opinion differs from `a`), `A` for
the rest, `b = |B|`, and `pᵥ = d_v^B / d` for the fraction of neighbours of `v` in `B`.

* `avg_minority_step`: after one round, `𝔼|B'| = ∑_{v ∈ A} pᵥ² + ∑_{v ∈ B} (1 − (1 − pᵥ)²)`.
* `sum_minorityProb_le`: if every superset `S ⊇ B` with `|S| ≤ (13/3) b` satisfies
  `E(S, S) ≤ (3/5) d |S|`, then `𝔼|B'| ≤ (24/25) b`. With `y = ∑_{v ∈ B} (1 − pᵥ)` (which is
  also `∑_{v ∈ A} pᵥ`, by double counting the edges between `A` and `B`), Cauchy-Schwarz gives
  `∑_{v ∈ B} (1 − pᵥ)² ≥ y² / b`; with `C = {v ∈ A : pᵥ > 3/10}`, the chord bound
  `p² ≤ (3/10) p + (p − 3/10)⁺` and the sparsity of `B ∪ C` (`|C| ≤ (10/3) b`) give
  `∑_{v ∈ A} pᵥ² ≤ (3/10) y + (y − (2/5) b) / 2`. Altogether
  `𝔼|B'| ≤ (4/5) b + (4/5) y − y² / b = (24/25) b − (y − (2/5) b)² / b`.
* `tail_minority_step`: Chernoff's bound turns this into `P(|B'| ≥ (49/50) m) ≤ e^{−m/4850}`
  for every `m ≥ b`.
-/

namespace Median
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Indicator of an opinion different from `a`. -/
def neInd (a b : Bool) : ℝ := if b ≠ a then 1 else 0

lemma neInd_med3 (a xv u w : Bool) :
    neInd a (med3 xv u w) =
      if xv = a then neInd a u * neInd a w else 1 - (1 - neInd a u) * (1 - neInd a w) := by
  cases a <;> cases xv <;> cases u <;> cases w <;> norm_num [neInd, med3]

omit [DecidableEq V] in
lemma minority_eq_sum (a : Bool) (y : V → Bool) :
    (minority a y : ℝ) = ∑ v, neInd a (y v) := by
  simp only [minority, neInd, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

/-- The two samples of a vertex are independent with the same law. -/
lemma avg_pair {β : Type*} [Fintype β] [Nonempty β] (a xv : Bool) (g : β → Bool) {p : ℝ}
    (hp : avg (fun i => neInd a (g i)) = p) :
    avg (fun q : β × β => neInd a (med3 xv (g q.1) (g q.2)))
      = if xv = a then p * p else 1 - (1 - p) * (1 - p) := by
  simp_rw [neInd_med3]
  by_cases h : xv = a
  · simp only [h, if_true]
    rw [avg_mul_prod (fun i => neInd a (g i)) (fun i => neInd a (g i)), hp]
  · simp only [h, if_false]
    rw [avg_sub, avg_const,
      avg_mul_prod (fun i => 1 - neInd a (g i)) (fun i => 1 - neInd a (g i)), avg_sub, avg_const,
      hp]

variable {G}

/-- The number of neighbours of `v` whose opinion differs from `a`. -/
def nbCount (G : SimpleGraph V) [DecidableRel G.Adj] (a : Bool) (x : V → Bool) (v : V) : ℕ :=
  ((G.neighborFinset v).filter fun u => x u ≠ a).card

/-- The probability that `v` holds an opinion different from `a` after one round. -/
noncomputable def minorityProb (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (a : Bool)
    (x : V → Bool) (v : V) : ℝ :=
  let p := (nbCount G a x v : ℝ) / d
  if x v = a then p * p else 1 - (1 - p) * (1 - p)

omit [DecidableEq V] in
lemma avg_neighbor_neInd {d : ℕ} (hreg : G.IsRegularOfDegree d) (a : Bool) (x : V → Bool)
    (v : V) : avg (fun u : G.neighborSet v => neInd a (x u)) = (nbCount G a x v : ℝ) / d := by
  rw [avg_neighborSet G v (fun u => neInd a (x u)), hreg v, nbCount]
  congr 1
  simp only [neInd, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

/-- **Expected minority after one round**: `𝔼|B'| = ∑ᵥ P(v holds an opinion ≠ a)`. -/
theorem avg_minority_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool) :
    avg (fun r : GraphRound G => (minority a (graphStep G x r) : ℝ))
      = ∑ v, minorityProb G d a x v := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  simp_rw [minority_eq_sum, avg_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hp : avg (fun r : NeighborRound G => neInd a (x (r v))) = (nbCount G a x v : ℝ) / d := by
    rw [avg_neighborRound_eval G hdeg v (fun u => neInd a (x u)), avg_neighbor_neInd hreg]
  exact avg_pair a (x v) (fun r : NeighborRound G => x (r v)) hp

/-! ### The worst case of one round -/

lemma edgeCount_union_left {S₁ S₂ : Finset V} (h : Disjoint S₁ S₂) (T : Finset V) :
    edgeCount G (S₁ ∪ S₂) T = edgeCount G S₁ T + edgeCount G S₂ T := by
  unfold edgeCount
  exact Finset.sum_union h

lemma edgeCount_union_right (S : Finset V) {T₁ T₂ : Finset V} (h : Disjoint T₁ T₂) :
    edgeCount G S (T₁ ∪ T₂) = edgeCount G S T₁ + edgeCount G S T₂ := by
  unfold edgeCount
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (h.mono Finset.inter_subset_right Finset.inter_subset_right)]

lemma card_inter_minority (a : Bool) (x : V → Bool) (v : V) :
    (G.neighborFinset v ∩ univ.filter (fun u => x u ≠ a)).card = nbCount G a x v := by
  rw [Finset.inter_filter, Finset.inter_univ, nbCount]

lemma card_inter_majority {d : ℕ} (hreg : G.IsRegularOfDegree d) (a : Bool) (x : V → Bool)
    (v : V) :
    ((G.neighborFinset v ∩ univ.filter (fun u => x u = a)).card : ℝ) = d - nbCount G a x v := by
  rw [Finset.inter_filter, Finset.inter_univ, nbCount, eq_sub_iff_add_eq]
  have h := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v)
    (fun u => x u = a)
  rw [G.card_neighborFinset_eq_degree, hreg v] at h
  simp only [ne_eq]
  exact_mod_cast h

/-- **The expected minority contracts** (the bound `𝔼Δ ≥ (1 − 2α)(1 − 3α) B` of the proof of
Lemma 12, at `α = 3/10`): if every superset `S ⊇ B` of the minority with `|S| ≤ (13/3) |B|`
satisfies `E(S, S) ≤ (3/5) d |S|`, then `∑ᵥ P(v holds an opinion ≠ a) ≤ (24/25) |B|`. -/
theorem sum_minorityProb_le {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool)
    (hsp : ∀ S : Finset V, univ.filter (fun v => x v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ 13 / 3 * minority a x → (edgeCount G S S : ℝ) ≤ 3 / 5 * d * S.card) :
    ∑ v, minorityProb G d a x v ≤ 24 / 25 * minority a x := by
  set B := univ.filter (fun v => x v ≠ a) with hB
  set A := univ.filter (fun v => x v = a) with hA
  have hbB : minority a x = B.card := rfl
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set p : V → ℝ := fun v => (nbCount G a x v : ℝ) / d with hp
  have hnb_le : ∀ v, nbCount G a x v ≤ d := fun v => by
    rw [← hreg v, ← G.card_neighborFinset_eq_degree]
    exact Finset.card_filter_le _ _
  have hp0 : ∀ v, 0 ≤ p v := fun v => by positivity
  have hp1 : ∀ v, p v ≤ 1 := fun v => by
    rw [hp]
    dsimp only
    rw [div_le_one hd']
    exact_mod_cast hnb_le v
  have hdp : ∀ v, (nbCount G a x v : ℝ) = d * p v := fun v => by
    rw [hp]
    field_simp
  -- split the sum over `A` and `B`
  have hsplit : ∑ v, minorityProb G d a x v
      = ∑ v ∈ A, p v * p v + ∑ v ∈ B, (1 - (1 - p v) * (1 - p v)) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => x v = a)]
    congr 1
    · exact Finset.sum_congr rfl fun v hv => by
        have hv' : x v = a := by simpa [hA] using hv
        simp [minorityProb, hv', hp]
    · rw [hB]
      exact Finset.sum_congr rfl fun v hv => by
        have hv' : ¬ x v = a := by simpa using hv
        simp [minorityProb, hv', hp]
  set y := ∑ v ∈ B, (1 - p v) with hy
  set Q := ∑ v ∈ B, (1 - p v) ^ 2 with hQdef
  have hQ : y ^ 2 ≤ B.card * Q := sq_sum_le_card_mul_sum_sq
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun v _ => sq_nonneg _
  have hy0 : 0 ≤ y := Finset.sum_nonneg fun v _ => by linarith [hp1 v]
  have hyb : y ≤ B.card := by
    calc y ≤ ∑ _v ∈ B, (1 : ℝ) := Finset.sum_le_sum fun v _ => by linarith [hp0 v]
      _ = B.card := by simp
  have hBp : ∑ v ∈ B, p v = B.card - y := by
    rw [hy, Finset.sum_sub_distrib]
    simp
  -- double counting the edges between `A` and `B`: `∑_{v ∈ A} pᵥ = y`
  have hAB : ∑ v ∈ A, p v = y := by
    have h1 : (edgeCount G A B : ℝ) = ∑ v ∈ A, (nbCount G a x v : ℝ) := by
      unfold edgeCount
      push_cast
      exact Finset.sum_congr rfl fun v _ => by rw [hB, card_inter_minority]
    have h2 : (edgeCount G B A : ℝ) = ∑ u ∈ B, ((d : ℝ) - nbCount G a x u) := by
      unfold edgeCount
      push_cast
      exact Finset.sum_congr rfl fun u _ => by rw [hA, card_inter_majority hreg]
    rw [edgeCount_comm] at h1
    rw [h1] at h2
    have : ∑ v ∈ A, (d : ℝ) * p v = ∑ u ∈ B, (d : ℝ) * (1 - p u) := by
      simp_rw [← hdp]
      rw [h2]
      exact Finset.sum_congr rfl fun u _ => by rw [hdp]; ring
    rw [← Finset.mul_sum, ← Finset.mul_sum] at this
    exact mul_left_cancel₀ hd'.ne' this
  -- the heavy vertices of `A`
  set C := A.filter (fun v => 3 / 10 < p v) with hC
  have hA2 : ∑ v ∈ A, p v * p v ≤ 3 / 10 * y + ∑ v ∈ C, (p v - 3 / 10) := by
    calc ∑ v ∈ A, p v * p v
        ≤ ∑ v ∈ A, (3 / 10 * p v + if 3 / 10 < p v then p v - 3 / 10 else 0) :=
          Finset.sum_le_sum fun v _ => by
            have := hp0 v
            have := hp1 v
            split_ifs with h
            · nlinarith
            · nlinarith
      _ = 3 / 10 * y + ∑ v ∈ C, (p v - 3 / 10) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hAB]
          congr 1
          exact (Finset.sum_filter _ _).symm
  have hCA : C ⊆ A := Finset.filter_subset _ _
  have hCp : 3 / 10 * (C.card : ℝ) ≤ ∑ v ∈ C, p v := by
    calc 3 / 10 * (C.card : ℝ) = ∑ _v ∈ C, (3 / 10 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ v ∈ C, p v := Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2.le
  have hCy : ∑ v ∈ C, p v ≤ y := by
    rw [← hAB]
    exact Finset.sum_le_sum_of_subset_of_nonneg hCA fun v _ _ => hp0 v
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro v hvB hvC
    have h1 := (Finset.mem_filter.mp hvB).2
    have h2 := (Finset.mem_filter.mp (hCA hvC)).2
    exact h1 h2
  set S := B ∪ C with hS
  have hScard : (S.card : ℝ) = B.card + C.card := by
    rw [hS, Finset.card_union_of_disjoint hdisj]
    push_cast
    ring
  have hsize : (S.card : ℝ) ≤ 13 / 3 * minority a x := by
    rw [hScard, hbB]
    linarith
  have hspS := hsp S Finset.subset_union_left hsize
  -- `E(S, S) ≥ E(B, B) + 2 E(C, B)`
  have hES : (edgeCount G B B : ℝ) + 2 * edgeCount G C B ≤ edgeCount G S S := by
    have h : edgeCount G S S = edgeCount G B S + edgeCount G C S := edgeCount_union_left hdisj S
    rw [hS, edgeCount_union_right B hdisj, edgeCount_union_right C hdisj,
      edgeCount_comm G B C] at h
    rw [h]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (edgeCount G C C)]
  have hEBB : (edgeCount G B B : ℝ) = d * (B.card - y) := by
    unfold edgeCount
    push_cast
    rw [← hBp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [hB, card_inter_minority, hdp]
  have hECB : (edgeCount G C B : ℝ) = d * ∑ v ∈ C, p v := by
    unfold edgeCount
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [hB, card_inter_minority, hdp]
  rw [hEBB, hECB] at hES
  have hkey : (B.card : ℝ) - y + 2 * ∑ v ∈ C, p v ≤ 3 / 5 * (B.card + C.card) := by
    have h := hES.trans hspS
    rw [hScard] at h
    have : (d : ℝ) * ((B.card : ℝ) - y + 2 * ∑ v ∈ C, p v)
        ≤ d * (3 / 5 * (B.card + C.card)) := by linarith
    exact le_of_mul_le_mul_left this hd'
  have hCsum : ∑ v ∈ C, (p v - 3 / 10) = ∑ v ∈ C, p v - 3 / 10 * C.card := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  have hBsum : ∑ v ∈ B, (1 - (1 - p v) * (1 - p v)) = B.card - Q := by
    rw [hQdef, Finset.sum_sub_distrib]
    simp [sq]
  rw [hsplit, hBsum, hbB]
  have hmain : ∑ v ∈ A, p v * p v + (B.card - Q) ≤ 4 / 5 * y + 4 / 5 * B.card - Q := by
    linarith
  rcases (Nat.cast_nonneg (α := ℝ) B.card).eq_or_lt with hb | hb
  · have : y = 0 := le_antisymm (hb ▸ hyb) hy0
    rw [← hb] at hmain ⊢
    linarith
  · nlinarith [sq_nonneg (y - 2 / 5 * B.card)]

/-- The expected minority after one round is at most `(24/25) |B|`. -/
theorem avg_minority_step_le {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool)
    (hsp : ∀ S : Finset V, univ.filter (fun v => x v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ 13 / 3 * minority a x → (edgeCount G S S : ℝ) ≤ 3 / 5 * d * S.card) :
    avg (fun r : GraphRound G => (minority a (graphStep G x r) : ℝ)) ≤ 24 / 25 * minority a x := by
  rw [avg_minority_step hd hreg]
  exact sum_minorityProb_le hd hreg a x hsp

/-! ### Concentration: one round as independent trials on a common sample space -/

/-- An enumeration of the neighbours of `v` in a `d`-regular graph. -/
noncomputable def nbrEquiv {d : ℕ} (hreg : G.IsRegularOfDegree d) (v : V) :
    Fin d ≃ G.neighborSet v :=
  (Fintype.equivFinOfCardEq (by rw [G.card_neighborSet_eq_degree, hreg v])).symm

/-- On a `d`-regular graph a round is the same as `2|V|` labels in `Fin d`, so uniform rounds
are independent uniform draws from the common space `Fin d × Fin d`, one per vertex. -/
noncomputable def roundEquiv {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    (V → Fin d × Fin d) ≃ GraphRound G where
  toFun ω := (fun v => nbrEquiv hreg v (ω v).1, fun v => nbrEquiv hreg v (ω v).2)
  invFun r := fun v => ((nbrEquiv hreg v).symm (r.1 v), (nbrEquiv hreg v).symm (r.2 v))
  left_inv ω := by
    funext v
    simp
  right_inv r := Prod.ext (funext fun v => by simp) (funext fun v => by simp)

/-- **Tail of the minority after one round**: under the sparsity hypothesis, for every
`m ≥ |B|`, `P(|B'| ≥ (49/50) m) ≤ e^{−m/4850}` (Chernoff's bound with mean bound `(24/25) m` and
`δ = 1/48`). -/
theorem tail_minority_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool)
    (hsp : ∀ S : Finset V, univ.filter (fun v => x v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ 13 / 3 * minority a x → (edgeCount G S S : ℝ) ≤ 3 / 5 * d * S.card)
    {m : ℝ} (hm : (minority a x : ℝ) ≤ m) :
    avg (fun r : GraphRound G =>
        if 49 / 50 * m ≤ (minority a (graphStep G x r) : ℝ) then (1 : ℝ) else 0)
      ≤ exp (-(m / 4850)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [← avg_equiv (roundEquiv hreg)]
  set Y : V → Fin d × Fin d → ℝ := fun v q =>
    neInd a (med3 (x v) (x (nbrEquiv hreg v q.1)) (x (nbrEquiv hreg v q.2))) with hYdef
  have hY : ∀ v q, Y v q = 0 ∨ Y v q = 1 := fun v q => by
    simp only [hYdef, neInd]
    split_ifs <;> simp
  have hsum (ω : V → Fin d × Fin d) :
      (minority a (graphStep G x (roundEquiv hreg ω)) : ℝ) = ∑ v, Y v (ω v) := by
    rw [minority_eq_sum]
    rfl
  have hμ : ∑ v, avg (Y v) ≤ 24 / 25 * m := by
    have hv (v : V) : avg (Y v) = minorityProb G d a x v := by
      have hp : avg (fun i : Fin d => neInd a (x (nbrEquiv hreg v i)))
          = (nbCount G a x v : ℝ) / d := by
        rw [avg_equiv (nbrEquiv hreg v) (fun u : G.neighborSet v => neInd a (x u)),
          avg_neighbor_neInd hreg]
      exact avg_pair a (x v) (fun i : Fin d => x (nbrEquiv hreg v i)) hp
    simp_rw [hv]
    have := sum_minorityProb_le hd hreg a x hsp
    linarith
  have key := avg_chernoff_upper Y hY (δ := 1 / 48) (by norm_num) hμ
  have hc : (1 + 1 / 48 : ℝ) * (24 / 25 * m) = 49 / 50 * m := by ring
  have he : -((1 / 48 : ℝ) ^ 2 * (24 / 25 * m) / (2 + 1 / 48)) = -(m / 4850) := by ring
  rw [hc, he] at key
  simp_rw [hsum]
  exact key

end Median
