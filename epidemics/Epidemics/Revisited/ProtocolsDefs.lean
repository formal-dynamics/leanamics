import Epidemics.Revisited.Defs

/-! # The push, pull and push–pull protocols on the complete graph (EPI-8, definitions)

In one round every node calls a node chosen uniformly at random among all `n` nodes,
independently; following the convention of Doerr and Kostrygin for complete graphs, a node may
call itself. The calls of a round are a uniform function `c : Fin n → Fin n` (`calls n`), and
each protocol is the image of `calls n` under a deterministic round map.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-- The calls of one round: a uniform function `Fin n → Fin n` (node `v` calls `c v`). The
function type is nonempty for every `n` (it contains the identity). -/
noncomputable def calls (n : ℕ) : Distribution (Fin n → Fin n) :=
  @Distribution.uniform (Fin n → Fin n) _ ⟨id⟩

/-- Push: the informed nodes `S` send the rumor to the nodes they call. -/
def pushRound (S : Finset (Fin n)) (c : Fin n → Fin n) : Finset (Fin n) :=
  S ∪ S.image c

/-- Pull: the nodes that call an informed node become informed. -/
def pullRound (S : Finset (Fin n)) (c : Fin n → Fin n) : Finset (Fin n) :=
  S ∪ univ.filter (fun v => c v ∈ S)

/-- Push–pull: a node becomes informed if it calls an informed node or is called by one. -/
def pushPullRound (S : Finset (Fin n)) (c : Fin n → Fin n) : Finset (Fin n) :=
  pushRound S c ∪ pullRound S c

/-- The push protocol on the complete graph `K_n` (with self-calls). -/
noncomputable def push (n : ℕ) : RumorProcess n where
  K S := (calls n).map (pushRound S)
  mono S := by
    classical
    rw [Distribution.prob_eq_expect, Distribution.map_expect]
    simp [pushRound]

/-- The pull protocol on the complete graph `K_n` (with self-calls). -/
noncomputable def pull (n : ℕ) : RumorProcess n where
  K S := (calls n).map (pullRound S)
  mono S := by
    classical
    rw [Distribution.prob_eq_expect, Distribution.map_expect]
    simp [pullRound]

/-- The push–pull protocol on the complete graph `K_n` (with self-calls). -/
noncomputable def pushPull (n : ℕ) : RumorProcess n where
  K S := (calls n).map (pushPullRound S)
  mono S := by
    classical
    rw [Distribution.prob_eq_expect, Distribution.map_expect]
    simp only [pushPullRound, pushRound, pullRound]
    simp [union_assoc]

end Epidemics.Revisited
