import Mathlib

/-!
# Iterating a monotone, inflationary step

PULL and PUSH–PULL (`PullModel.lean`) iterate a one-round step `f I a` (informed set `I`,
round `a`) along a list of rounds with `List.foldl`. This file collects the deterministic facts
used for any such step that is *inflationary* (`I ⊆ f I a`: informed nodes stay informed) and
*monotone* in the informed set:

* `subset_foldl` — the informed set only grows;
* `foldl_mono` — more informed nodes at the start give more at the end;
* `foldl_subset_foldl` — pathwise domination of a step by a larger monotone step;
* `foldl_append_eq_univ` — once everybody is informed, everybody stays informed.
-/

namespace RumorPush

open Finset

variable {n : ℕ} {α : Type*}

/-- An inflationary step only adds informed nodes along a trajectory. -/
lemma subset_foldl {f : Finset (Fin n) → α → Finset (Fin n)} (hf : ∀ I a, I ⊆ f I a)
    (I : Finset (Fin n)) (l : List α) : I ⊆ l.foldl f I := by
  induction l generalizing I with
  | nil => exact subset_rfl
  | cons a l ih => exact (hf I a).trans (ih (f I a))

/-- Iterating a monotone step is monotone in the initial informed set. -/
lemma foldl_mono {f : Finset (Fin n) → α → Finset (Fin n)}
    (hf : ∀ a, Monotone fun I => f I a) {I J : Finset (Fin n)} (h : I ⊆ J) (l : List α) :
    l.foldl f I ⊆ l.foldl f J := by
  induction l generalizing I J with
  | nil => exact h
  | cons a l ih => exact ih (hf a h)

/-- **Pathwise domination**: if `f ≤ g` round by round and `g` is monotone, then the
trajectory of `f` stays inside the trajectory of `g` driven by the same rounds. -/
lemma foldl_subset_foldl {f g : Finset (Fin n) → α → Finset (Fin n)}
    (hfg : ∀ I a, f I a ⊆ g I a) (hg : ∀ a, Monotone fun I => g I a)
    (I : Finset (Fin n)) (l : List α) : l.foldl f I ⊆ l.foldl g I := by
  induction l generalizing I with
  | nil => exact subset_rfl
  | cons a l ih => exact (ih (f I a)).trans (foldl_mono hg (hfg I a) l)

/-- Once all nodes are informed they stay informed (for an inflationary step). -/
lemma foldl_append_eq_univ {f : Finset (Fin n) → α → Finset (Fin n)}
    (hf : ∀ I a, I ⊆ f I a) {I : Finset (Fin n)} {l₁ : List α} (h : l₁.foldl f I = univ)
    (l₂ : List α) : (l₁ ++ l₂).foldl f I = univ := by
  rw [List.foldl_append, h]
  exact univ_subset_iff.1 (subset_foldl hf univ l₂)

end RumorPush
