import Epidemics.Giant

/-! # Supercritical Reed–Frost epidemics on the complete graph (EPI-3, epidemic reading)

By the pathwise coupling of EPI-1 (`final_recovered_iff`), the nodes eventually infected by the
Reed–Frost epidemic started from a single node `v` form the connected component of `v` in the
percolated graph `perc G ω`. On the complete graph `K_n` with transmission probability `p` and
`R₀ = p n > 1`, the supercritical giant component (Krivelevich–Sudakov, Theorem 2, and its
extension to every `ε > 0`) thus gives an outbreak of `Ω(n)` nodes with probability `Ω(1)`: by
symmetry, `v` lies in a component of size `≥ k` with probability at least `k / n` times the
probability that such a component exists (`prob_component_ge`).

`R₀ = p n` follows the roadmap; the mean number of secondary infections caused by the first
infected node is `p (n - 1)`.
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Final size (EPI-1): the number of nodes eventually infected from `{v}` is the size of the
connected component of `v` in the percolated graph. -/
lemma card_final_recovered (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (v : V) :
    (run G ω {v} (Fintype.card V)).recovered.card =
      ((perc G ω).connectedComponentMk v).supp.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.mem_coe, final_recovered_iff, Finset.mem_singleton, exists_eq_left,
    SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Relabelling the vertices by `σ` is an isomorphism `perc ⊤ (ω ∘ σ) ≃g perc ⊤ ω`. -/
def percPermIso (ω : Sym2 V → Bool) (σ : Equiv.Perm V) :
    perc ⊤ (fun e => ω (e.map σ)) ≃g perc ⊤ ω where
  toEquiv := σ
  map_rel_iff' := by
    intro a b
    show (⊤ : SimpleGraph V).Adj (σ a) (σ b) ∧ ω s(σ a, σ b) = true ↔
      (⊤ : SimpleGraph V).Adj a b ∧ ω (s(a, b).map σ) = true
    simp [σ.injective.eq_iff]

omit [Fintype V] [DecidableEq V] in
/-- The components of `w` after relabelling and of `σ w` before have the same size. -/
lemma ncard_supp_perm (ω : Sym2 V → Bool) (σ : Equiv.Perm V) (w : V) :
    ((perc ⊤ (fun e => ω (e.map σ))).connectedComponentMk w).supp.ncard =
      ((perc ⊤ ω).connectedComponentMk (σ w)).supp.ncard := by
  set φ := percPermIso ω σ
  have hφ (x : V) : φ x = σ x := rfl
  have himage : σ '' ((perc ⊤ (fun e => ω (e.map σ))).connectedComponentMk w).supp =
      ((perc ⊤ ω).connectedComponentMk (σ w)).supp := by
    ext x
    simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [← hφ, ← hφ]
      exact SimpleGraph.Iso.reachable_iff.mpr hu
    · intro hx
      refine ⟨σ.symm x, ?_, by simp⟩
      have : (perc ⊤ ω).Reachable (φ (σ.symm x)) (φ w) := by
        rw [hφ, hφ, Equiv.apply_symm_apply]; exact hx
      exact SimpleGraph.Iso.reachable_iff.mp this
  rw [← himage, Set.ncard_image_of_injective _ σ.injective]

/-- **Symmetry of `K_n`**: the size of the component of a vertex has the same law for all
vertices. -/
lemma prob_component_ge_eq (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (v w : V) (k : ℝ) :
    (coins (V := V) p h0 h1).prob
        (fun ω => k ≤ ((perc ⊤ ω).connectedComponentMk w).supp.ncard) =
      (coins (V := V) p h0 h1).prob
        (fun ω => k ≤ ((perc ⊤ ω).connectedComponentMk v).supp.ncard) := by
  rw [← coins_prob_perm p h0 h1 (Equiv.swap w v)]
  refine prob_congr _ fun ω => ?_
  rw [ncard_supp_perm, Equiv.swap_apply_left]

/-- **Symmetry of `K_n`**: the vertex `v` lies in a component with at least `k` vertices with
probability at least `k / n` times the probability that such a component exists (the expected
number of vertices in such components is `n` times the former, and at least `k` times the
latter). -/
lemma prob_component_ge (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (v : V) (k : ℝ) :
    k / Fintype.card V * (coins (V := V) p h0 h1).prob
        (fun ω => ∃ K : (perc ⊤ ω).ConnectedComponent, k ≤ K.supp.ncard) ≤
      (coins p h0 h1).prob fun ω => k ≤ ((perc ⊤ ω).connectedComponentMk v).supp.ncard := by
  classical
  set P := coins (V := V) p h0 h1
  rcases le_or_gt k 0 with hk | hk
  · have : k / Fintype.card V ≤ 0 := div_nonpos_of_nonpos_of_nonneg hk (Nat.cast_nonneg _)
    exact (mul_nonpos_of_nonpos_of_nonneg this (Distribution.prob_nonneg _ _)).trans
      (Distribution.prob_nonneg _ _)
  -- pointwise: a component with `≥ k` vertices gives `≥ k` vertices in such components
  have hpt (ω : Sym2 V → Bool) :
      k * (if ∃ K : (perc ⊤ ω).ConnectedComponent, k ≤ K.supp.ncard then (1 : ℝ) else 0) ≤
        ∑ w, if k ≤ ((perc ⊤ ω).connectedComponentMk w).supp.ncard then (1 : ℝ) else 0 := by
    split_ifs with h
    · obtain ⟨K, hK⟩ := h
      have hsub : ∑ w ∈ K.supp.toFinset,
          (if k ≤ ((perc ⊤ ω).connectedComponentMk w).supp.ncard then (1 : ℝ) else 0) ≤
          ∑ w, if k ≤ ((perc ⊤ ω).connectedComponentMk w).supp.ncard then (1 : ℝ) else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => by split_ifs <;> norm_num
      have hone : ∑ w ∈ K.supp.toFinset,
          (if k ≤ ((perc ⊤ ω).connectedComponentMk w).supp.ncard then (1 : ℝ) else 0) =
          K.supp.toFinset.card := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
        refine Finset.sum_congr rfl fun w hw => ?_
        have hw' : (perc ⊤ ω).connectedComponentMk w = K :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff K w).mp (Set.mem_toFinset.mp hw)
        rw [hw', if_pos hK]
      rw [Set.ncard_eq_toFinset_card'] at hK
      rw [mul_one]
      linarith
    · rw [mul_zero]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hint : k * P.prob (fun ω => ∃ K : (perc ⊤ ω).ConnectedComponent, k ≤ K.supp.ncard) ≤
      ∑ w, P.prob (fun ω => k ≤ ((perc ⊤ ω).connectedComponentMk w).supp.ncard) := by
    rw [prob_eq_expect, ← Distribution.expect_mul]
    simp_rw [prob_eq_expect]
    rw [← Distribution.expect_sum]
    exact P.expect_mono hpt
  rw [Finset.sum_congr rfl fun w _ => prob_component_ge_eq p h0 h1 v w k, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hint
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · rw [hn, Nat.cast_zero, div_zero, zero_mul]
    exact Distribution.prob_nonneg _ _
  · have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    rw [div_mul_eq_mul_div, div_le_iff₀ hn']
    linarith

/-- **Large outbreak near the threshold, explicit constants** (EPI-3, Krivelevich–Sudakov,
Theorem 2, via EPI-1): for every small enough `ε > 0` there is `C` such that the Reed–Frost
epidemic on the complete graph on `n` nodes with transmission probability `p = (1 + ε) / n`
(`R₀ = p n = 1 + ε`), started from any single infected node `v`, eventually infects at least
`ε n / 2` nodes with probability at least `ε / 2 - C / n`. -/
theorem reedFrost_large_outbreak_explicit :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
        p * Fintype.card V = 1 + ε → ∀ v : V,
        ε / 2 - C / Fintype.card V ≤ (coins p h0 h1).prob fun ω =>
          ε * Fintype.card V / 2 ≤ ((run ⊤ ω {v} (Fintype.card V)).recovered.card : ℝ) := by
  obtain ⟨ε₀, hε₀, hgiant⟩ := exists_giant_component
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨C, hC⟩ := hgiant ε hε hεε₀
  refine ⟨ε / 2 * C, fun V _ _ p h0 h1 hp v => ?_⟩
  have hn : (0 : ℝ) < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hp; linarith
    · exact_mod_cast h
  have key := prob_component_ge p h0 h1 v (ε * Fintype.card V / 2)
  have hk : ε * (Fintype.card V : ℝ) / 2 / Fintype.card V = ε / 2 := by field_simp
  rw [hk] at key
  have hcomp := hC V p h0 h1 hp
  calc ε / 2 - ε / 2 * C / Fintype.card V = ε / 2 * (1 - C / Fintype.card V) := by ring
    _ ≤ ε / 2 * (coins (V := V) p h0 h1).prob (fun ω =>
          ∃ K : (perc ⊤ ω).ConnectedComponent, ε * Fintype.card V / 2 ≤ K.supp.ncard) :=
        mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ ≤ _ := key
    _ = _ := prob_congr _ fun ω => by rw [card_final_recovered]

/-- **Large outbreak** (EPI-3, epidemic reading of the supercritical giant component, via EPI-1):
for every `R₀ > 1` there are `c > 0`, `q > 0` and `n₀` such that the Reed–Frost epidemic on the
complete graph on `n ≥ n₀` nodes with transmission probability `p = R₀ / n`, started from any
single infected node `v`, eventually infects at least `c n` nodes with probability at least `q`:
`Ω(n)` nodes with probability `Ω(1)`. -/
theorem reedFrost_large_outbreak (R₀ : ℝ) (hR₀ : 1 < R₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ q : ℝ, 0 < q ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V], n₀ ≤ Fintype.card V →
        ∀ (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1), p * Fintype.card V = R₀ → ∀ v : V,
        q ≤ (coins p h0 h1).prob fun ω =>
          c * Fintype.card V ≤ ((run ⊤ ω {v} (Fintype.card V)).recovered.card : ℝ) := by
  obtain ⟨c, hc, C, hC⟩ := exists_linear_component (R₀ - 1) (by linarith)
  refine ⟨c, hc, c / 2, by positivity, ⌈2 * C⌉₊ + 1, fun V _ _ hn₀ p h0 h1 hp v => ?_⟩
  have hnC : 2 * C < Fintype.card V := by
    have h1' := Nat.le_ceil (2 * C)
    have h2' : ((⌈2 * C⌉₊ + 1 : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hn₀
    push_cast at h2'
    linarith
  have hn : (0 : ℝ) < Fintype.card V := by
    have : (0 : ℝ) < ((⌈2 * C⌉₊ + 1 : ℕ) : ℝ) := by positivity
    have h2' : ((⌈2 * C⌉₊ + 1 : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hn₀
    linarith
  have hp' : p * Fintype.card V = 1 + (R₀ - 1) := by rw [hp]; ring
  have hcomp := hC V p h0 h1 hp'
  have key := prob_component_ge p h0 h1 v (c * Fintype.card V)
  have hk : c * (Fintype.card V : ℝ) / Fintype.card V = c := by field_simp
  rw [hk] at key
  have hCn : C / Fintype.card V ≤ 1 / 2 := by
    rw [div_le_iff₀ hn]; linarith
  calc c / 2 ≤ c * (1 - C / Fintype.card V) := by nlinarith
    _ ≤ c * (coins (V := V) p h0 h1).prob (fun ω =>
          ∃ K : (perc ⊤ ω).ConnectedComponent, c * Fintype.card V ≤ K.supp.ncard) :=
        mul_le_mul_of_nonneg_left hcomp hc.le
    _ ≤ _ := key
    _ = _ := prob_congr _ fun ω => by rw [card_final_recovered]

end Epidemics
