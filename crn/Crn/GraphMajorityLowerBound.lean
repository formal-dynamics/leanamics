import Crn.GraphMajorityAmbassador

/-!
# At least 4 states are needed for majority (CRN-4)

**[MNRS14, Theorem 1]**: no population protocol with at most 3 states stably computes the
majority of a 2-type population on every interaction graph, so the 4-state ambassador protocol
(`ambassador_graphStablyComputes`) has the minimal number of states.

The paper's proof only uses complete interaction graphs (a population `V` and the population
`V ∪ {u, v}` with two extra agents, interacting in a supergraph), so we pin the stronger form
`not_stablyComputesOnGraph_top_majority`: no protocol with at most 3 states stably computes
majority on the complete graphs of all nonempty populations (the standard populations of
`Protocol.StablyComputes`), even with ties excluded from the domain. The statement on all
connected graphs follows (`not_graphStablyComputes_majority`).

Proof route [MNRS14, Theorem 1]: both outputs occur, so with at most 3 states one output value
`b` has a single state `q₁`. Say `b` is the output of a red majority (otherwise exchange the
colors). On `V = Fin 3`, the inputs `C₁ = (r, r, g)` and `C₂ = (r, r, r)` both reach the
configuration "all `q₁`". Adding two green agents gives `C₁' = (r, r, g, g, g)` (green
majority) and `C₂' = (r, r, r, g, g)` (red majority); running the same encounters inside `V`
(`Protocol.GraphReaches.extend`) both reach the configuration "`q₁` on `V`, green input state on
the two extra agents", from which output-stable configurations with both outputs would be
reachable: a contradiction. The paper takes `|V| = 2k + 1` with `k ≥ 2`; `k = 1` already works.

## References

* [MNRS14] G. B. Mertzios, S. E. Nikoletseas, C. L. Raptopoulos, P. G. Spirakis, *Determining
  majority in networks with local interactions and very small local memory*, ICALP 2014;
  arXiv:1404.7671.
-/

namespace Crn

/-- A single agent has no partner on the complete graph: from `c`, only `c` is reachable. -/
theorem Protocol.GraphReaches.eq_of_fin_one {Q : Type*} {P : Protocol Bool Q}
    {c d : Fin 1 → Q} (h : P.GraphReaches (⊤ : SimpleGraph (Fin 1)) c d) : d = c := by
  induction h with
  | refl => rfl
  | tail _ hs _ =>
    obtain ⟨e, -⟩ := hs
    exact absurd (Subsingleton.elim e.fst e.snd) e.adj.ne

/-- **Both outputs occur** [MNRS14, proof of Theorem 1]: a protocol computing majority on the
complete graph of a single agent outputs `b` on the input state of `b`. -/
theorem output_input_of_stablyComputesOnGraph_top_majority {Q : Type*} {P : Protocol Bool Q}
    (h : P.StablyComputesOnGraph (⊤ : SimpleGraph (Fin 1)) HasMajority majority) (b : Bool) :
    P.output (P.input b) = b := by
  obtain ⟨d, hd, hst⟩ := h (fun _ => b) (by unfold HasMajority; cases b <;> decide) _
    Relation.ReflTransGen.refl
  have hm : majority (counts fun _ : Fin 1 => b).1 = b := by cases b <;> decide
  have h0 := hst d Relation.ReflTransGen.refl 0
  rwa [hd.eq_of_fin_one, hm] at h0

/-- **The core of [MNRS14, Theorem 1].** If a single state `q₁` has output `b`, then the
protocol does not compute majority on all complete graphs: on `Fin 3`, the inputs `(b, b, !b)`
and `(b, b, b)` both reach "all `q₁`"; adding two agents of input `!b` (inputs `(b, b, !b, !b, !b)`
and `(b, b, b, !b, !b)`, with majorities `!b` and `b`) gives a common reachable configuration
from which output-stable configurations with both outputs are reachable. -/
theorem not_stablyComputesOnGraph_top_majority_of_unique {Q : Type*} (P : Protocol Bool Q)
    (b : Bool) (q₁ : Q) (hq : ∀ q, P.output q = b → q = q₁) :
    ¬ ∀ n, 0 < n → P.StablyComputesOnGraph (⊤ : SimpleGraph (Fin n)) HasMajority majority := by
  intro h
  -- on `Fin 3`, every input with majority `b` reaches "all `q₁`"
  have key : ∀ ι : Fin 3 → Bool, HasMajority (counts ι).1 → majority (counts ι).1 = b →
      P.GraphReaches ⊤ (P.input ∘ ι) (fun _ => q₁) := by
    intro ι hD hm
    obtain ⟨d, hd, hst⟩ := h 3 (by norm_num) ι hD _ Relation.ReflTransGen.refl
    have hdq : d = fun _ => q₁ :=
      funext fun v => hq _ (hm ▸ hst d Relation.ReflTransGen.refl v)
    exact hdq ▸ hd
  -- embed `Fin 3` into `Fin 5`
  set f : Fin 3 → Fin 5 := Fin.castLE (by norm_num)
  have hf : Function.Injective f := Fin.castLE_injective _
  have hG : ∀ u v, (⊤ : SimpleGraph (Fin 3)).Adj u v → (⊤ : SimpleGraph (Fin 5)).Adj (f u) (f v) :=
    fun u v huv => (SimpleGraph.top_adj _ _).2 (hf.ne ((SimpleGraph.top_adj _ _).1 huv))
  have hext : ∀ (ι : Fin 3 → Bool) (ι' : Fin 5 → Bool), ι' ∘ f = ι →
      Function.extend f (P.input ∘ ι) (P.input ∘ ι') = P.input ∘ ι' := by
    intro ι ι' hι
    funext w
    by_cases hw : ∃ v, f v = w
    · obtain ⟨v, rfl⟩ := hw
      rw [hf.extend_apply, ← hι]
      rfl
    · rw [Function.extend_apply' _ _ _ hw]
  set ι₁' : Fin 5 → Bool := ![b, b, !b, !b, !b]
  set ι₂' : Fin 5 → Bool := ![b, b, b, !b, !b]
  set cs : Fin 5 → Q := Function.extend f (fun _ => q₁) (P.input ∘ ι₁') with hcs
  have r₁ : P.GraphReaches ⊤ (P.input ∘ ι₁') cs := by
    have := Protocol.GraphReaches.extend P hf hG
      (key ![b, b, !b] (by unfold HasMajority; cases b <;> decide) (by cases b <;> decide))
      (P.input ∘ ι₁')
    rwa [hext _ _ (by funext v; fin_cases v <;> rfl)] at this
  have r₂ : P.GraphReaches ⊤ (P.input ∘ ι₂') cs := by
    have := Protocol.GraphReaches.extend P hf hG
      (key ![b, b, b] (by unfold HasMajority; cases b <;> decide) (by cases b <;> decide))
      (P.input ∘ ι₂')
    rw [hext _ _ (by funext v; fin_cases v <;> rfl)] at this
    convert this using 1
    funext w
    rw [hcs]
    by_cases hw : ∃ v, f v = w
    · obtain ⟨v, rfl⟩ := hw
      rw [hf.extend_apply, hf.extend_apply]
    · rw [Function.extend_apply' _ _ _ hw, Function.extend_apply' _ _ _ hw]
      fin_cases w
      · exact (hw ⟨0, rfl⟩).elim
      · exact (hw ⟨1, rfl⟩).elim
      · exact (hw ⟨2, rfl⟩).elim
      · rfl
      · rfl
  obtain ⟨d, hd, hst₁⟩ := h 5 (by norm_num) ι₁'
    (by unfold HasMajority; cases b <;> decide) cs r₁
  obtain ⟨e, he, hst₂⟩ := h 5 (by norm_num) ι₂'
    (by unfold HasMajority; cases b <;> decide) d (r₂.trans hd)
  have h₁ := hst₁ e he 0
  have h₂ := hst₂ e Relation.ReflTransGen.refl 0
  rw [h₁] at h₂
  revert h₂
  cases b <;> decide

/-- **[MNRS14, Theorem 1], strong form.** No population protocol with at most 3 states stably
computes the majority of two input types on the complete graphs of all nonempty populations,
with the tie inputs excluded from the domain. -/
theorem not_stablyComputesOnGraph_top_majority {Q : Type*} [Fintype Q]
    (hQ : Fintype.card Q ≤ 3) (P : Protocol Bool Q) :
    ¬ ∀ n, 0 < n → P.StablyComputesOnGraph (⊤ : SimpleGraph (Fin n)) HasMajority majority := by
  classical
  intro h
  have hout := output_input_of_stablyComputesOnGraph_top_majority (h 1 (by norm_num))
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Q))
    (fun q => P.output q = true)
  rw [Finset.card_univ] at hcard
  have hT : 0 < (Finset.univ.filter fun q => P.output q = true).card :=
    Finset.card_pos.2 ⟨P.input true, by simp [hout]⟩
  have hF : 0 < (Finset.univ.filter fun q => ¬ P.output q = true).card :=
    Finset.card_pos.2 ⟨P.input false, by simp [hout]⟩
  rcases (by omega : (Finset.univ.filter fun q => P.output q = true).card = 1 ∨
      (Finset.univ.filter fun q => ¬ P.output q = true).card = 1) with h1 | h1
  · obtain ⟨q₁, hq₁⟩ := Finset.card_eq_one.1 h1
    refine not_stablyComputesOnGraph_top_majority_of_unique P true q₁ (fun q hq => ?_) h
    exact Finset.mem_singleton.1 (hq₁ ▸ Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩)
  · obtain ⟨q₁, hq₁⟩ := Finset.card_eq_one.1 h1
    refine not_stablyComputesOnGraph_top_majority_of_unique P false q₁ (fun q hq => ?_) h
    exact Finset.mem_singleton.1 (hq₁ ▸ Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [hq]⟩)

/-- **[MNRS14, Theorem 1].** No population protocol with at most 3 states stably computes the
majority of two input types on every connected interaction graph: `R(𝒫_majority) > 3`. -/
theorem not_graphStablyComputes_majority {Q : Type*} [Fintype Q] (hQ : Fintype.card Q ≤ 3)
    (P : Protocol Bool Q) : ¬ P.GraphStablyComputes HasMajority majority :=
  fun h => not_stablyComputesOnGraph_top_majority hQ P h.top

/-- **The rank of majority is 4** [MNRS14, Theorems 1 and 2]: the 4-state ambassador protocol
stably computes majority on every connected graph, and no protocol with fewer states does. -/
theorem rank_majority_eq_four :
    (∃ (Q : Type) (_ : Fintype Q) (P : Protocol Bool Q),
      Fintype.card Q = 4 ∧ P.GraphStablyComputes HasMajority majority) ∧
    ∀ (Q : Type) [Fintype Q] (P : Protocol Bool Q),
      P.GraphStablyComputes HasMajority majority → 4 ≤ Fintype.card Q :=
  ⟨⟨AmbState, inferInstance, ambassador, card_ambState, ambassador_graphStablyComputes⟩,
    fun _ _ P h => by
      by_contra hlt
      exact not_graphStablyComputes_majority (by omega) P h⟩

end Crn
