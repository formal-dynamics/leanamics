import Dynamics.Rounds

/-!
# Time reversal of i.i.d. rounds (roadmap FND-6)

The `T` rounds averaged by `expList` are i.i.d. uniform, so their joint law is invariant under
reversing their order: `expList α T (F ∘ List.reverse) = expList α T F`. The proof goes through
the product form `expList_eq_avg_ofFn` of `Dynamics.Equivalence` and the reindexing of
`Fin T → α` by `Fin.rev`.

For a process driven by rounds, `iterate_ofStep` reads the rounds first to last (a left fold);
by time reversal the same expectation is obtained by applying them last to first (a right
fold), which is the form of backward (dual) processes such as coalescing random walks.
-/

namespace Dynamics
variable {α : Type*}

/-- Reversing a list of draws is precomposing the draws with `Fin.rev`. -/
lemma reverse_ofFn {n : ℕ} (ω : Fin n → α) :
    (List.ofFn ω).reverse = List.ofFn (ω ∘ Fin.rev) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_reverse, List.finRange_reverse,
    List.map_map]

variable [Fintype α]

/-- **Time reversal of i.i.d. rounds** (roadmap FND-6). Reversing the order of `T` i.i.d.
uniform rounds does not change the expectation of any functional of them. -/
theorem expList_comp_reverse (T : ℕ) (F : List α → ℝ) :
    expList α T (F ∘ List.reverse) = expList α T F := by
  rw [expList_eq_avg_ofFn, expList_eq_avg_ofFn]
  simp only [Function.comp_apply, reverse_ofFn]
  have h := avg_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl α))
    (fun ω : Fin T → α => F (List.ofFn ω))
  convert h using 4 with ω
  congr 1

end Dynamics

namespace Dynamics.Kernel
variable {S R : Type*} [Fintype S] [Fintype R] [Nonempty R]

/-- **Time reversal for round-based kernels** (roadmap FND-6). Iterating `ofStep step` is
averaging over `T` i.i.d. rounds applied in reverse order, i.e. along the right fold. -/
theorem iterate_ofStep_foldr (step : S → R → S) (T : ℕ) (f : S → ℝ) (s : S) :
    (ofStep step).iterate T f s = expList R T (fun l => f (l.foldr (fun r t => step t r) s)) := by
  rw [iterate_ofStep, ← expList_comp_reverse]
  congr 1
  funext l
  simp

end Dynamics.Kernel
