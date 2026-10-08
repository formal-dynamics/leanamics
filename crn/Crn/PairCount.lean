import Mathlib

/-!
# Counting ordered pairs of distinct agents by species

For a configuration `c : Fin n → S`, the ordered pairs `(u, v)` of distinct agents whose
species form the unordered pair `{A, B}` are `2·#A·#B` if `A ≠ B` and `#A·(#A - 1)` if
`A = B`, where `#A` is the number of agents of species `A`; there are `n·(n - 1)` ordered pairs
of distinct agents. This is the counting behind the key identity of CRN-1.
-/

namespace Crn
open Finset

variable {S : Type*} [DecidableEq S] {n : ℕ}

/-- Filtering ordered pairs of distinct agents is filtering the off-diagonal of `Fin n × Fin n`. -/
lemma card_filter_pairs (c : Fin n → S) (z : Sym2 S) :
    (univ.filter fun p : {p : Fin n × Fin n // p.1 ≠ p.2} => s(c p.1.1, c p.1.2) = z).card =
      ((univ : Finset (Fin n)).offDiag.filter fun p => s(c p.1, c p.2) = z).card := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext ⟨u, v⟩
  simp [mem_offDiag, and_comm]

/-- There are `n·(n - 1)` ordered pairs of distinct agents. -/
lemma card_pairs : Fintype.card {p : Fin n × Fin n // p.1 ≠ p.2} = n * (n - 1) := by
  rw [Fintype.card_subtype]
  have : (univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2) = (univ : Finset (Fin n)).offDiag := by
    ext ⟨u, v⟩
    simp [mem_offDiag]
  rw [this, offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub_one]

/-- Ordered pairs of distinct agents with species `{A, B}`, `A ≠ B`: `2·#A·#B`. -/
lemma card_pairs_of_ne (c : Fin n → S) {A B : S} (hAB : A ≠ B) :
    ((univ : Finset (Fin n)).offDiag.filter fun p => s(c p.1, c p.2) = s(A, B)).card =
      2 * (univ.filter fun v => c v = A).card * (univ.filter fun v => c v = B).card := by
  set FA := univ.filter fun v => c v = A
  set FB := univ.filter fun v => c v = B
  have hset : ((univ : Finset (Fin n)).offDiag.filter fun p => s(c p.1, c p.2) = s(A, B)) =
      FA ×ˢ FB ∪ FB ×ˢ FA := by
    ext ⟨u, v⟩
    simp only [mem_filter, mem_offDiag, mem_univ, true_and, mem_union, mem_product, FA, FB,
      Sym2.eq_iff]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
      · refine ⟨fun huv => hAB ?_, Or.inl ⟨hu, hv⟩⟩
        rw [← hu, ← hv, huv]
      · refine ⟨fun huv => hAB ?_, Or.inr ⟨hu, hv⟩⟩
        rw [← hu, ← hv, huv]
  have hdisj : Disjoint (FA ×ˢ FB) (FB ×ˢ FA) := by
    rw [disjoint_left]
    rintro ⟨u, v⟩ h1 h2
    simp only [mem_product, FA, FB, mem_filter, mem_univ, true_and] at h1 h2
    exact hAB (h1.1.symm.trans h2.1)
  rw [hset, card_union_of_disjoint hdisj, card_product, card_product]
  ring

/-- Ordered pairs of distinct agents with species `{A, A}`: `#A·(#A - 1)`. -/
lemma card_pairs_of_eq (c : Fin n → S) (A : S) :
    ((univ : Finset (Fin n)).offDiag.filter fun p => s(c p.1, c p.2) = s(A, A)).card =
      (univ.filter fun v => c v = A).card * ((univ.filter fun v => c v = A).card - 1) := by
  have hset : ((univ : Finset (Fin n)).offDiag.filter fun p => s(c p.1, c p.2) = s(A, A)) =
      (univ.filter fun v => c v = A).offDiag := by
    ext ⟨u, v⟩
    simp only [mem_filter, mem_offDiag, mem_univ, true_and, Sym2.eq_iff]
    tauto
  rw [hset, offDiag_card, Nat.mul_sub_one]

end Crn
