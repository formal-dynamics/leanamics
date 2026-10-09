import Crn.StableInteract

/-!
# Stable computation with general outputs (CRN-5)

`Protocol.StablyComputes` (CRN-3) computes predicates: every agent outputs a `Bool` through the
`output` field of the protocol, and all agents agree. The exact majority and plurality protocols of
[GHMSS16] need two generalizations, which only change the output convention (the transitions,
`Protocol.Reaches` and the fair-execution semantics in reachability form are those of
`StableBasic.lean`):

* outputs in an arbitrary type `Y`, read through a separate map `O : Q → Y` (the sign of a majority
  vote in [GHMSS16, Theorem 3], the absolute majority colour or none in [GHMSS16, Theorem 6]);
  this is the function-computation convention of Chen, Doty and Soloveichik (2014);
* outputs that depend on the agent's own input symbol (`StablyMarks`): in the relative majority
  protocol [GHMSS16, Theorem 7] the agents end up *marked*, each one knowing whether its own colour
  is the winner, not the winner's label.

`StablyComputesWith P O f` is the uniform case, and `StablyComputesWith P P.output φ` is exactly
`P.StablyComputes φ` (`stablyComputesWith_output_iff`).

## References

* [GHMSS16] L. Gąsieniec, D. Hamilton, R. Martin, P. G. Spirakis, G. Stachowiak, *Deterministic
  population protocols for exact majority and plurality*, OPODIS 2016, LIPIcs 70, Article 14.
-/

namespace Crn

variable {X Q Y Z : Type*} {n : ℕ}

namespace Protocol

/-- `c` is output-stable for the output map `O` with the target outputs `y` (one per agent): in
every configuration reachable from `c`, every agent `v` outputs `y v`. -/
def OutputStableAt (P : Protocol X Q) (O : Q → Y) (y : Fin n → Y) (c : Fin n → Q) : Prop :=
  ∀ c', P.Reaches c c' → ∀ v, O (c' v) = y v

variable [Fintype X] [DecidableEq X]

/-- `P` stably *marks* the agents with `g` through the output map `O`: for every nonempty
population and input assignment `ι`, every configuration reachable from `I ∘ ι` reaches a
configuration that is output-stable with the output `g x (ι v)` at each agent `v`, where `x` is
the input count vector. This is `StablyComputes` with outputs in `Y` that may depend on the
agent's own input symbol. -/
def StablyMarks (P : Protocol X Q) (O : Q → Y) (g : (X → ℕ) → X → Y) : Prop :=
  ∀ n, 0 < n → ∀ ι : Fin n → X, ∀ c, P.Reaches (P.input ∘ ι) c →
    ∃ d, P.Reaches c d ∧ P.OutputStableAt O (fun v => g (counts ι).1 (ι v)) d

/-- `P` stably computes `f : (X → ℕ) → Y` through the output map `O`: all agents eventually and
forever output `f` of the input counts (`StablyMarks` with a target independent of the agent). -/
def StablyComputesWith (P : Protocol X Q) (O : Q → Y) (f : (X → ℕ) → Y) : Prop :=
  P.StablyMarks O fun x _ => f x

/-- With the protocol's own `Bool` output, `StablyComputesWith` is `StablyComputes` (CRN-3). -/
theorem stablyComputesWith_output_iff (P : Protocol X Q) (φ : (X → ℕ) → Bool) :
    P.StablyComputesWith P.output φ ↔ P.StablyComputes φ :=
  Iff.rfl

/-- Post-composing the outputs: if `P` stably marks with `g` through `O`, it stably marks with
`F ∘ g` through `F ∘ O`. -/
theorem StablyMarks.map {P : Protocol X Q} {O : Q → Y} {g : (X → ℕ) → X → Y}
    (h : P.StablyMarks O g) (F : Y → Z) :
    P.StablyMarks (fun q => F (O q)) fun x i => F (g x i) := by
  intro n hn ι c hc
  obtain ⟨d, hd, hs⟩ := h n hn ι c hc
  exact ⟨d, hd, fun e he v => congrArg F (hs e he v)⟩

/-- Post-composing the outputs of a uniform computation. -/
theorem StablyComputesWith.map {P : Protocol X Q} {O : Q → Y} {f : (X → ℕ) → Y}
    (h : P.StablyComputesWith O f) (F : Y → Z) :
    P.StablyComputesWith (fun q => F (O q)) fun x => F (f x) :=
  StablyMarks.map h F

end Protocol

end Crn
