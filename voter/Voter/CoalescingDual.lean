import Dynamics.Relations
import Voter.Model

/-! # The voter model and coalescing random walks: a duality of kernels

The dictionary relation `duality` is `Dynamics.Kernel.Dual H K L`,
`𝔼_x[H(X₁, y)] = 𝔼_y[H(x, Y₁)]`, which then holds at every time
(`Dynamics.Kernel.Dual.iterate`). For every sampling kernel `H`, the synchronous voter model
`transition H` (every vertex `v` copies the colour of `r v`, the vertices sampling independently
with `H`) is dual to coalescing random walks driven by the same kind of rounds, as a process on
sets of vertices: from the set `A` of occupied vertices, a round `r` leads to its image `r(A)`, so
walkers that land on the same vertex merge (`coalescingKernel H`). The duality function is the
additive one of interacting particle systems, `someTrue s A = 1{s v = true for some v ∈ A}`: in
one round both sides agree for every `r`, since `s ∘ r` takes the value `true` on `A` iff `s`
takes it on `r(A)` (`transition_dual`). Hence, at every time `t`, the probability that some vertex
of `A` has colour `true` after `t` rounds from `s` equals the probability that the coalescing walks
started from `A` occupy, after `t` steps, some vertex where `s` is `true`
(`transition_event_someTrue`). This is the discrete-time form, for every sampling kernel, of the
duality between the voter model and coalescing random walks with respect to the additive duality
function of interacting particle systems (Swart, Proposition 6.25; row `coalescing` of the
cross-field dictionary). With Wright–Fisher sampling (`wfKernel V`) the walkers are the ancestral
lineages of a Wright–Fisher sample.
-/

namespace Voter
open Dynamics Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Coalescing random walks on sets of vertices**, driven by the rounds of the voter model with
sampling kernel `H`: from the set `A` of occupied vertices, a round `r` drawn from
`Distribution.independent H` (the walker at `v` moves to `r v`) leads to the image `r(A)`;
walkers that land on the same vertex merge. -/
noncomputable def coalescingKernel (H : Kernel V) : Kernel (Finset V) :=
  fun A => (Distribution.independent H).map fun r => A.image r

/-- The additive duality function: `1` if some vertex of `A` has colour `true` in `s`. -/
noncomputable def someTrue (s : Config V Bool) (A : Finset V) : ℝ :=
  if ∃ v ∈ A, s v = true then 1 else 0

omit [Fintype V] in
/-- **One round of the duality, pathwise.** After the round `r`, some vertex of `A` has colour
`true` iff some vertex of `r(A)` had it before. -/
lemma someTrue_step (s : Config V Bool) (A : Finset V) (r : V → V) :
    someTrue (step s r) A = someTrue s (A.image r) :=
  if_congr (by simp [step]) rfl rfl

/-- **The voter model and coalescing random walks are dual kernels.** For every sampling kernel
`H`, the voter model `transition H` and the coalescing walks `coalescingKernel H` are dual with
respect to the additive duality function: `𝔼_s[someTrue(X₁, A)] = 𝔼_A[someTrue(s, A₁)]` for every
configuration `s` and every set `A`. -/
theorem transition_dual (H : Kernel V) :
    Kernel.Dual someTrue (transition H) (coalescingKernel H) := fun s A => by
  simp only [Kernel.apply, transition, coalescingKernel, Distribution.map_expect, someTrue_step]

/-- **The duality at every time.** The probability that some vertex of `A` has colour `true`
after `t` rounds of the voter model from `s` equals the probability that the coalescing walks
started from `A` occupy, after `t` steps, some vertex where `s` has colour `true`. -/
theorem transition_event_someTrue (H : Kernel V) (t : ℕ) (s : Config V Bool) (A : Finset V) :
    (transition H).event (fun x => ∃ v ∈ A, x v = true) t s =
      (coalescingKernel H).event (fun B => ∃ v ∈ B, s v = true) t A := by
  rw [Kernel.event_eq_iterate, Kernel.event_eq_iterate]
  exact (transition_dual H).iterate t s A

end Voter
