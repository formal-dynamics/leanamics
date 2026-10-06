import RumorSpread.OneRound

/-!
# Independence of the calls in a uniform round

A uniform round `r : Tgt n` is a uniform element of the product `∀ v, {u // u ≠ v}`, so the calls
`r v` of different nodes are independent. `avg_pi_prod` states this for any finite product
(Fubini for products of functions of the coordinates, via `Fintype.prod_sum`), and
`avg_tgt_mul_prod` specializes it to a function of one call `r v` times a product over calls
`r w`, `w ∈ S`, with `v ∉ S`. This covers all the probabilities needed for PULL and PUSH–PULL:

* `avg_tgt_coord` — a single call is uniform among the other `n - 1` nodes;
* `avg_call_mem`, `avg_call_not_mem` — a caller `v ∉ I` calls into `I` with probability
  `|I|/(n-1)`;
* `avg_call_ne` — a caller `w` misses a fixed node `v ≠ w` with probability `1 - 1/(n-1)`.
-/

namespace RumorPush

open Finset

variable {n : ℕ}

/-- **Independent coordinates**: under the uniform distribution on a finite product, the
expectation of a product of functions of the coordinates is the product of the expectations. -/
lemma avg_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (g : ∀ i, β i → ℝ) :
    avg (fun x : (∀ i, β i) => ∏ i, g i (x i)) = ∏ i, avg (g i) := by
  unfold avg
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, ← prod_div_distrib]

/-- The calls of a uniform round are independent (`avg_pi_prod` for `Tgt n`). -/
lemma avg_tgt_prod (g : Fin n → Fin n → ℝ) :
    avg (fun r : Tgt n => ∏ v, g v (r v))
      = ∏ v, avg (fun y : {u : Fin n // u ≠ v} => g v y) :=
  avg_pi_prod fun v (y : {u : Fin n // u ≠ v}) => g v y

lemma nonempty_ne (hn : 2 ≤ n) (w : Fin n) : Nonempty {u : Fin n // u ≠ w} := by
  have h2 : 1 < Fintype.card (Fin n) := by simp only [Fintype.card_fin]; omega
  exact (Fintype.exists_ne_of_one_lt_card h2 w).elim fun u hu => ⟨⟨u, hu⟩⟩

lemma card_ne (w : Fin n) : Fintype.card {u : Fin n // u ≠ w} = n - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]

lemma cast_card_ne (hn : 2 ≤ n) (w : Fin n) :
    (Fintype.card {u : Fin n // u ≠ w} : ℝ) = (n : ℝ) - 1 := by
  rw [card_ne, Nat.cast_sub (by omega), Nat.cast_one]

/-- **One call times independent other calls**: for `v ∉ S`, the expectation of a function of the
call `r v` times a product of functions of the calls `r w`, `w ∈ S`, factorizes. -/
lemma avg_tgt_mul_prod (hn : 2 ≤ n) {v : Fin n} {S : Finset (Fin n)} (hv : v ∉ S)
    (a : Fin n → ℝ) (b : Fin n → Fin n → ℝ) :
    avg (fun r : Tgt n => a (r v) * ∏ w ∈ S, b w (r w))
      = avg (fun y : {u : Fin n // u ≠ v} => a y)
          * ∏ w ∈ S, avg (fun y : {u : Fin n // u ≠ w} => b w y) := by
  let g : Fin n → Fin n → ℝ := fun w y => (if w = v then a y else 1) * (if w ∈ S then b w y else 1)
  have hpt : ∀ r : Tgt n, a (r v) * ∏ w ∈ S, b w (r w) = ∏ w, g w (r w) := by
    intro r
    simp only [g, prod_mul_distrib, prod_ite_eq', mem_univ, if_true, Fintype.prod_ite_mem]
  have hw : ∀ w : Fin n, avg (fun y : {u : Fin n // u ≠ w} => g w y)
      = (if w = v then avg (fun y : {u : Fin n // u ≠ v} => a y) else 1)
          * (if w ∈ S then avg (fun y : {u : Fin n // u ≠ w} => b w y) else 1) := by
    intro w
    haveI := nonempty_ne hn w
    by_cases hwv : w = v
    · subst hwv
      simp [g, hv]
    · by_cases hwS : w ∈ S
      · simp [g, hwv, hwS]
      · simp [g, hwv, hwS, avg_const]
  rw [show (fun r : Tgt n => a (r v) * ∏ w ∈ S, b w (r w)) = fun r => ∏ w, g w (r w)
    from funext hpt, avg_tgt_prod, prod_congr rfl fun w _ => hw w, prod_mul_distrib,
    prod_ite_eq', Fintype.prod_ite_mem, if_pos (mem_univ v)]

/-- A single call `r v` of a uniform round is uniform among the other `n - 1` nodes. -/
lemma avg_tgt_coord (hn : 2 ≤ n) (v : Fin n) (a : Fin n → ℝ) :
    avg (fun r : Tgt n => a (r v)) = avg (fun y : {u : Fin n // u ≠ v} => a y) := by
  simpa using avg_tgt_mul_prod hn (S := ∅) (v := v) (by simp) a fun _ _ => 1

/-- A caller `v ∉ I` calls into `I` with probability `|I|/(n-1)`. -/
lemma avg_call_mem (hn : 2 ≤ n) {v : Fin n} {I : Finset (Fin n)} (hv : v ∉ I) :
    avg (fun y : {u : Fin n // u ≠ v} => if (y : Fin n) ∈ I then (1 : ℝ) else 0)
      = I.card / ((n : ℝ) - 1) := by
  rw [avg_indicator, cast_card_ne hn]
  have h : (univ.filter fun y : {u : Fin n // u ≠ v} => (y : Fin n) ∈ I) = I.subtype (· ≠ v) := by
    ext y
    simp [mem_subtype]
  rw [h, card_subtype, filter_true_of_mem fun x hx => by rintro rfl; exact hv hx]

/-- A caller `v ∉ I` calls outside `I` with probability `(n - 1 - |I|)/(n-1)`. -/
lemma avg_call_not_mem (hn : 2 ≤ n) {v : Fin n} {I : Finset (Fin n)} (hv : v ∉ I) :
    avg (fun y : {u : Fin n // u ≠ v} => if (y : Fin n) ∈ I then (0 : ℝ) else 1)
      = ((n : ℝ) - 1 - I.card) / ((n : ℝ) - 1) := by
  haveI := nonempty_ne hn v
  have hpt : (fun y : {u : Fin n // u ≠ v} => if (y : Fin n) ∈ I then (0 : ℝ) else 1)
      = fun y => (fun _ => (1 : ℝ)) y
          - (fun y : {u : Fin n // u ≠ v} => if (y : Fin n) ∈ I then (1 : ℝ) else 0) y := by
    funext y
    by_cases h : (y : Fin n) ∈ I <;> simp [h]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [hpt, avg_sub, avg_const, avg_call_mem hn hv]
  field_simp

/-- A caller `w` misses a fixed node `v ≠ w` with probability `1 - 1/(n-1)`. -/
lemma avg_call_ne (hn : 2 ≤ n) {v w : Fin n} (hvw : v ≠ w) :
    avg (fun y : {u : Fin n // u ≠ w} => if (y : Fin n) = v then (0 : ℝ) else 1)
      = 1 - 1 / ((n : ℝ) - 1) := by
  have h := avg_call_not_mem hn (I := {v}) (v := w) (by simpa using hvw.symm)
  simp only [mem_singleton, card_singleton, Nat.cast_one] at h
  rw [h]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp

end RumorPush
