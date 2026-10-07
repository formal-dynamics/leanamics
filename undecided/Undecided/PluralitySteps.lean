import Undecided.PluralityAlg
import Undecided.PluralityArith

/-! # One good round of the `k`-colour dynamics (UND-3)

The deterministic heart of the analysis: what a good round (`Good`) does to the sets of the
proof. Fix the plurality colour `m`, the ratio bound `θ = 1/(1 + α) < 1` (with `κ = 1 - θ`), the
bound `B ≥ 1` on the non-plurality mass relative to the plurality (`B = 2 md(x₀)`) and the
deviation parameter `ℓ = 3 log n`.

* `Inv ℓ θ B m`: every other community has at most `θ c - 12√(ℓc)` nodes and all other
  communities together at most `B c - 12B√(ℓc)`, where `c = c_m` (the slack shrinks relative to
  `c` as `c` grows; this replaces the accumulated errors of the paper's Lemma 2);
* `Fpsi m`: the final set `4S + q ≤ n/10`, `S` the nodes of other colours, `q` the undecided.

Under the numerical conditions `Hyp` (all consequences of `n ≥ C³ k³ log n` with `C = C(α)`):

* `inv_step`: a good round from `Inv` with `Φ = µ_m ≥ φ` stays in `Inv`;
* `phi_step`: if moreover the configuration is not in `Fpsi`, `Φ` grows by `1 + κ/(8000B)`;
* `fpsi_step`: a good round from `Fpsi` stays in `Fpsi`;
* `first_step`: a good first round from a configuration without undecided nodes in which
  `cᵢ ≤ θ c_m` for all `i ≠ m` enters `Inv ∩ {Φ ≥ φ}`, when `µ_m ≥ 2φ`.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

/-- The invariant of the analysis: colour `m` beats every other colour by the factor `1/θ`, and
the other colours together have at most `B` times as many nodes, with slack `12√(ℓ c_m)`. -/
def Inv (ℓ θ B : ℝ) (m : Fin k) : Set (Config n k) :=
  {y | (∀ i, i ≠ m → cnt y i + 12 * √(ℓ * cnt y m) ≤ θ * cnt y m) ∧
    oth y m + 12 * B * √(ℓ * cnt y m) ≤ B * cnt y m}

/-- The final set: `4S + q ≤ n/10`. -/
def Fpsi (m : Fin k) : Set (Config n k) := {y | 4 * oth y m + und y ≤ (n : ℝ) / 10}

/-- The numerical conditions of the analysis. -/
structure Hyp (n : ℕ) (ℓ θ B φ : ℝ) : Prop where
  hn : (0 : ℝ) < n
  hℓ : 0 < ℓ
  hθ0 : 0 < θ
  hθ1 : θ < 1
  hB : 1 ≤ B
  h1 : 1024 * ℓ ≤ θ ^ 2 * (1 - θ) ^ 2 * φ
  h2 : 2048 * (n : ℝ) ^ 2 * ℓ ≤ θ ^ 2 * (1 - θ) ^ 2 * ((n : ℝ) / (20 * (1 + B))) ^ 3
  h3 : (16 * (4000 * B) / (1 - θ)) ^ 2 * ℓ ≤ (n : ℝ) / (8 * (1 + B))
  h4 : (48 * (4000 * B) / (1 - θ)) ^ 2 * ℓ ≤ n
  h5 : 160000 * ℓ ≤ n

/-! ### The threshold step in its three regimes -/

/-- The invariant `X + σ√(ℓc) ≤ tc` is kept by a good round, in each regime: zone A
(`X ≤ tc/2`), growth (`n - q < n/20`, so `µ ≥ 16c/9`) and drift (`n - q ≥ n/20`). -/
lemma thr_cases {ℓ t σ E κ c μ nn q X μX X' C' : ℝ} (hℓ : 0 ≤ ℓ) (ht : 0 < t) (hσ : 0 ≤ σ)
    (hc : 0 < c) (hμ16 : 16 * ℓ ≤ μ) (hmono : σ ^ 2 * ℓ ≤ 2 * t ^ 2 * μ)
    (hC' : μ - 2 * √(ℓ * μ) ≤ C') (hinv : X + σ * √(ℓ * c) ≤ t * c)
    (hX' : X' ≤ μX + E * √(ℓ * μ)) (hμXc : μX * c ≤ X * μ)
    (hμXd : t * c / 2 < X → μX * c ≤ X * μ - t / 2 * κ * c ^ 3 / nn)
    (hA : (2 * t + σ + E) * √(ℓ * μ) ≤ t / 2 * μ)
    (hG : nn - q < nn / 20 → 16 / 9 * c ≤ μ) (hσE : 3 * (2 * t + E) ≤ σ)
    (hD : nn / 20 ≤ nn - q → (2 * t + σ + E) * √(ℓ * μ) ≤ t / 2 * κ * c ^ 2 / nn) :
    X' + σ * √(ℓ * C') ≤ t * C' := by
  have hμ0 : 0 ≤ μ := le_trans (by positivity) hμ16
  refine thr_step hℓ ht hσ hμ16 hmono hC' ?_
  by_cases hzA : X ≤ t * c / 2
  · have hr : μX ≤ t / 2 * μ := by
      have h1 : μX * c ≤ t / 2 * μ * c := by
        calc μX * c ≤ X * μ := hμXc
          _ ≤ t * c / 2 * μ := mul_le_mul_of_nonneg_right hzA hμ0
          _ = t / 2 * μ * c := by ring
      exact le_of_mul_le_mul_right h1 hc
    exact key_ratio hX' hr (by linarith)
  · replace hzA := not_le.mp hzA
    by_cases hreg : nn - q < nn / 20
    · exact key_growth hℓ hc hX' hμXc hinv (hG hreg) hσE hσ
    · have hsc := sqrt_nonneg (ℓ * c)
      have hX : X ≤ t * c := by nlinarith
      exact key_drift hc hμ0 hX' (hμXd hzA) hX (hD (not_lt.mp hreg))

/-- The drift beats the deviations once `2048 n² ℓ ≤ θ²κ²c³`: `16√(ℓµ) ≤ θκc²/(2n)`. -/
lemma drift_big {ℓ θ κ c μ nn : ℝ} (hℓ : 0 ≤ ℓ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (hc : 0 < c)
    (hnn : 0 < nn) (hμ : μ ≤ 2 * c) (h : 2048 * nn ^ 2 * ℓ ≤ θ ^ 2 * κ ^ 2 * c ^ 3) :
    16 * √(ℓ * μ) ≤ θ * κ * c ^ 2 / (2 * nn) := by
  have h1 : √(ℓ * μ) ≤ √(ℓ * (2 * c)) := sqrt_mul_le_of_le hℓ hμ
  have h2 : 16 * √(ℓ * (2 * c)) ≤ θ * κ * c ^ 2 / (2 * nn) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, sq_sqrt (by positivity), div_pow, le_div_iff₀ (by positivity)]
    have : 0 < c * nn ^ 2 := by positivity
    nlinarith
  linarith

lemma sqrt_mul_le_mul_sqrt {B y : ℝ} (hB : 1 ≤ B) : √(B * y) ≤ B * √y := by
  rw [sqrt_mul (by linarith)]
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg y)
  calc √B ≤ √(B ^ 2) := sqrt_le_sqrt (by nlinarith)
    _ = B := sqrt_sq (by linarith)

/-! ### The invariant -/

section
variable {ℓ θ B φ : ℝ} {m : Fin k} {x y : Config n k}

lemma cnt_pos_of_mu_pos (h : 0 < mu x m) : 0 < cnt x m := by
  rcases (cnt_nonneg x m).lt_or_eq with h' | h'
  · exact h'
  · unfold mu at h
    rw [← h'] at h
    simp at h

lemma Hyp.kappa_pos (H : Hyp n ℓ θ B φ) : 0 < 1 - θ := by linarith [H.hθ1]

/-- From `Φ ≥ φ`: `1024ℓ ≤ θ²κ²µ`. -/
lemma Hyp.mu_big (H : Hyp n ℓ θ B φ) (hφ : φ ≤ mu x m) :
    1024 * ℓ ≤ θ ^ 2 * (1 - θ) ^ 2 * mu x m :=
  H.h1.trans (mul_le_mul_of_nonneg_left hφ (by positivity))

lemma Hyp.mu_big_θ (H : Hyp n ℓ θ B φ) (hφ : φ ≤ mu x m) : 1024 * ℓ ≤ θ ^ 2 * mu x m := by
  have h := H.mu_big hφ
  have hκ := H.kappa_pos
  have h1 : (1 - θ) ^ 2 ≤ 1 := by nlinarith [H.hθ0]
  have h2 : 0 ≤ θ ^ 2 * mu x m := mul_nonneg (sq_nonneg θ) (mu_nonneg x m)
  calc 1024 * ℓ ≤ θ ^ 2 * (1 - θ) ^ 2 * mu x m := h
    _ = θ ^ 2 * mu x m * (1 - θ) ^ 2 := by ring
    _ ≤ θ ^ 2 * mu x m * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = θ ^ 2 * mu x m := by ring

lemma Hyp.mu_big_one (H : Hyp n ℓ θ B φ) (hφ : φ ≤ mu x m) : 1024 * ℓ ≤ mu x m := by
  have h := H.mu_big_θ hφ
  have h1 : θ ^ 2 ≤ 1 := by nlinarith [H.hθ0, H.hθ1]
  have h2 : θ ^ 2 * mu x m ≤ 1 * mu x m := mul_le_mul_of_nonneg_right h1 (mu_nonneg x m)
  linarith

lemma Hyp.cnt_pos (H : Hyp n ℓ θ B φ) (hφ : φ ≤ mu x m) : 0 < cnt x m :=
  cnt_pos_of_mu_pos (by linarith [H.mu_big_one hφ, H.hℓ])

/-- After a good round the plurality has at least `µ - 2√(ℓµ)` nodes. -/
lemma Hyp.cnt_next (H : Hyp n ℓ θ B φ) (hφ : φ ≤ mu x m) (hG : Good ℓ m x y) :
    mu x m - 2 * √(ℓ * mu x m) ≤ cnt y m := by
  have := dev_le H.hℓ.le (le_refl (mu x m)) (by linarith [H.mu_big_one hφ, H.hℓ])
  linarith [hG.2.1]

lemma inv_col_le (hx : x ∈ Inv ℓ θ B m) {j : Fin k} (hj : j ≠ m) :
    cnt x j ≤ θ * cnt x m := by
  have := hx.1 j hj
  have := sqrt_nonneg (ℓ * cnt x m)
  linarith

lemma inv_oth_le (hx : x ∈ Inv ℓ θ B m) (hB : 1 ≤ B) : oth x m ≤ B * cnt x m := by
  have h := hx.2
  have h1 := sqrt_nonneg (ℓ * cnt x m)
  have h2 : 0 ≤ 12 * B * √(ℓ * cnt x m) := by positivity
  linarith

/-- In the growth regime (`n - q < n/20`), `µ_m ≥ 16 c_m / 9`. -/
lemma Hyp.grow (H : Hyp n ℓ θ B φ) :
    (n : ℝ) - und x < n / 20 → 16 / 9 * cnt x m ≤ mu x m := by
  intro hd
  unfold mu
  rw [le_div_iff₀ H.hn]
  have := cnt_nonneg x m
  nlinarith

/-- In the drift regime (`n - q ≥ n/20`), the plurality has at least `n/(20(1 + B))` nodes and
the drift beats the deviations. -/
lemma Hyp.drift (H : Hyp n ℓ θ B φ) (hx : x ∈ Inv ℓ θ B m) (hφ : φ ≤ mu x m) :
    (n : ℝ) / 20 ≤ n - und x →
      16 * √(ℓ * mu x m) ≤ θ * (1 - θ) * cnt x m ^ 2 / (2 * n) := by
  intro hd
  have hc := H.cnt_pos hφ
  have hSB := inv_oth_le hx H.hB
  have hbigc : (n : ℝ) / (20 * (1 + B)) ≤ cnt x m := by
    rw [div_le_iff₀ (by linarith [H.hB])]
    have e : (n : ℝ) - und x = cnt x m + oth x m := by unfold oth; ring
    nlinarith
  refine drift_big H.hℓ.le H.hθ0.le H.kappa_pos.le hc H.hn (mu_le_two_cnt x m H.hn)
    (H.h2.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by have := H.hB; positivity) hbigc 3

/-- **The colour bounds of the invariant are kept** by a good round. -/
lemma col_step (H : Hyp n ℓ θ B φ) (hx : x ∈ Inv ℓ θ B m) (hφ : φ ≤ mu x m)
    (hG : Good ℓ m x y) {i : Fin k} (hi : i ≠ m) :
    cnt y i + 12 * √(ℓ * cnt y m) ≤ θ * cnt y m := by
  have hc := H.cnt_pos hφ
  have hθ0 := H.hθ0
  have hθ1 := H.hθ1
  have hμ1 := H.mu_big_one hφ
  have hμθ := H.mu_big_θ hφ
  have hℓ := H.hℓ
  have hci := inv_col_le hx hi
  have hci0 := cnt_nonneg x i
  have hsμ := sqrt_nonneg (ℓ * mu x m)
  have hX' : cnt y i ≤ mu x i + 2 * √(ℓ * mu x m) := by
    have hle : mu x i ≤ mu x m := mu_le_mu x (by nlinarith)
    have := dev_le hℓ.le hle (by linarith)
    linarith [hG.1 i]
  have hsub := cnt_mu_sub x i m
  have hzA : √(ℓ * mu x m) ≤ mu x m / (32 / θ) :=
    sqrt_le_div hℓ.le (by positivity) (by rw [div_pow]; field_simp; linarith)
  refine thr_cases (κ := 1 - θ) (nn := n) (q := und x) hℓ.le hθ0 (by norm_num) hc
    (by linarith) (by linarith) (H.cnt_next hφ hG) (hx.1 i hi) hX' ?_ ?_ ?_ H.grow
    (by linarith) ?_
  · have : 0 ≤ cnt x i * cnt x m * (cnt x m - cnt x i) / n := by
      apply div_nonneg _ (Nat.cast_nonneg n)
      exact mul_nonneg (mul_nonneg hci0 hc.le) (by nlinarith)
    linarith
  · intro hbig
    have : θ / 2 * (1 - θ) * cnt x m ^ 3 / n ≤ cnt x i * cnt x m * (cnt x m - cnt x i) / n := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      have h1 : θ * cnt x m / 2 * cnt x m ≤ cnt x i * cnt x m :=
        mul_le_mul_of_nonneg_right hbig.le hc.le
      have h2 : (1 - θ) * cnt x m ≤ cnt x m - cnt x i := by linarith
      have := mul_le_mul h1 h2 (by nlinarith) (by nlinarith)
      nlinarith
    linarith
  · have e : mu x m / (32 / θ) = θ * mu x m / 32 := by field_simp
    rw [e] at hzA
    have h16 : 2 * θ + 12 + 2 ≤ 16 := by linarith
    have : (2 * θ + 12 + 2) * √(ℓ * mu x m) ≤ 16 * √(ℓ * mu x m) :=
      mul_le_mul_of_nonneg_right h16 hsμ
    linarith
  · intro hd
    have h := H.drift hx hφ hd
    have e : θ * (1 - θ) * cnt x m ^ 2 / (2 * n) = θ / 2 * (1 - θ) * cnt x m ^ 2 / n := by
      field_simp
    have h16 : 2 * θ + 12 + 2 ≤ 16 := by linarith
    have : (2 * θ + 12 + 2) * √(ℓ * mu x m) ≤ 16 * √(ℓ * mu x m) :=
      mul_le_mul_of_nonneg_right h16 hsμ
    linarith

/-- **The bound on the other colours together is kept** by a good round. -/
lemma oth_step (H : Hyp n ℓ θ B φ) (hx : x ∈ Inv ℓ θ B m) (hφ : φ ≤ mu x m)
    (hG : Good ℓ m x y) : oth y m + 12 * B * √(ℓ * cnt y m) ≤ B * cnt y m := by
  have hc := H.cnt_pos hφ
  have hθ0 := H.hθ0
  have hθ1 := H.hθ1
  have hκ := H.kappa_pos
  have hB := H.hB
  have hμ1 := H.mu_big_one hφ
  have hℓ := H.hℓ
  have hsμ := sqrt_nonneg (ℓ * mu x m)
  have hSB := inv_oth_le hx hB
  have hW := oth_mu_sub_ge x m (fun j hj => inv_col_le hx hj)
  have hS0 := oth_nonneg x m
  have hμ0 := mu_nonneg x m
  have hW0 : 0 ≤ (1 - θ) * cnt x m ^ 2 * oth x m / n := by positivity
  have hμS : muS x m ≤ B * mu x m := by
    have h3 : muS x m * cnt x m ≤ B * mu x m * cnt x m := by
      have := mul_le_mul_of_nonneg_right hSB hμ0
      nlinarith
    exact le_of_mul_le_mul_right h3 hc
  have hX' : oth y m ≤ muS x m + 2 * B * √(ℓ * mu x m) := by
    have h6 : 6 * ℓ ≤ B * mu x m := by nlinarith
    have h7 := dev_le hℓ.le hμS h6
    have h8 : √(ℓ * (B * mu x m)) ≤ B * √(ℓ * mu x m) := by
      rw [show ℓ * (B * mu x m) = B * (ℓ * mu x m) by ring]
      exact sqrt_mul_le_mul_sqrt hB
    linarith [hG.2.2.1]
  have hzA : √(ℓ * mu x m) ≤ mu x m / 32 := sqrt_le_div hℓ.le (by norm_num) (by linarith)
  refine thr_cases (κ := 1 - θ) (nn := n) (q := und x) (E := 2 * B) hℓ.le (by linarith)
    (by positivity) hc (by linarith) ?_ (H.cnt_next hφ hG) hx.2 hX' (by linarith) ?_ ?_
    H.grow (by linarith) ?_
  · have : (12 * B) ^ 2 * ℓ = B ^ 2 * (144 * ℓ) := by ring
    rw [this]
    have h2 : 144 * ℓ ≤ 2 * mu x m := by linarith
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg B)
    linarith
  · intro hbig
    have : B / 2 * (1 - θ) * cnt x m ^ 3 / n ≤ (1 - θ) * cnt x m ^ 2 * oth x m / n := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      have h1 : B * cnt x m / 2 ≤ oth x m := hbig.le
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (1 - θ) * cnt x m ^ 2)
      nlinarith
    linarith
  · have : (2 * B + 12 * B + 2 * B) * √(ℓ * mu x m) = B * (16 * √(ℓ * mu x m)) := by ring
    rw [this]
    have h16 : 16 * √(ℓ * mu x m) ≤ mu x m / 2 := by linarith
    have := mul_le_mul_of_nonneg_left h16 (by linarith : 0 ≤ B)
    nlinarith
  · intro hd
    have h := H.drift hx hφ hd
    have e1 : θ * (1 - θ) * cnt x m ^ 2 / (2 * n) ≤ (1 - θ) * cnt x m ^ 2 / (2 * n) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ (1 - θ) * cnt x m ^ 2 := by positivity
      nlinarith
    have e2 : B / 2 * (1 - θ) * cnt x m ^ 2 / n = B * ((1 - θ) * cnt x m ^ 2 / (2 * n)) := by
      field_simp
    rw [e2]
    have : (2 * B + 12 * B + 2 * B) * √(ℓ * mu x m) = B * (16 * √(ℓ * mu x m)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- **The invariant is kept** by a good round when `Φ = µ_m ≥ φ`. -/
theorem inv_step (H : Hyp n ℓ θ B φ) (hx : x ∈ Inv ℓ θ B m) (hφ : φ ≤ mu x m)
    (hG : Good ℓ m x y) : y ∈ Inv ℓ θ B m :=
  ⟨fun _ hi => col_step H hx hφ hG hi, oth_step H hx hφ hG⟩

end

end Undecided.Plurality
