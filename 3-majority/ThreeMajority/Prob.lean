import Dynamics.Uniform

/-!
Compatibility declarations with the original public statements and names.
The body of `avg` is retained so that existing `simp [avg]` proofs keep working;
its probability laws are supplied by `Dynamics.Uniform`.
-/
namespace ThreeMajority
open Finset
variable {α : Type*} [Fintype α]

@[inherit_doc Dynamics.avg]
noncomputable def avg (f : α → ℝ) : ℝ := (∑ a, f a) / (Fintype.card α : ℝ)
@[inherit_doc Dynamics.expList]
noncomputable abbrev expList (α : Type*) [Fintype α] (T : ℕ) (F : List α → ℝ) : ℝ :=
  Dynamics.expList α T F

lemma avg_nonneg {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ avg f :=
  Dynamics.avg_nonneg hf

lemma avg_le_avg {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : avg f ≤ avg g :=
  Dynamics.avg_le_avg h

lemma avg_add (f g : α → ℝ) : avg (fun a => f a + g a) = avg f + avg g :=
  Dynamics.avg_add f g

lemma avg_sub (f g : α → ℝ) : avg (fun a => f a - g a) = avg f - avg g :=
  Dynamics.avg_sub f g

lemma avg_const_mul (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f :=
  Dynamics.avg_const_mul c f

lemma avg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) :=
  Dynamics.avg_sum s f

@[inherit_doc Dynamics.avg_indicator]
lemma avg_indicator (P : α → Prop) [DecidablePred P] :
    avg (fun a => if P a then (1 : ℝ) else 0)
      = ((univ.filter P).card : ℝ) / (Fintype.card α : ℝ) :=
  Dynamics.avg_indicator P

lemma card_cast_pos [Nonempty α] : (0 : ℝ) < (Fintype.card α : ℝ) :=
  Dynamics.card_cast_pos

lemma avg_const [Nonempty α] (c : ℝ) : avg (fun _ : α => c) = c :=
  Dynamics.avg_const c

@[simp] lemma expList_zero (F : List α → ℝ) : expList α 0 F = F [] :=
  Dynamics.expList_zero F

lemma expList_succ (T : ℕ) (F : List α → ℝ) :
    expList α (T + 1) F = avg fun a : α => expList α T fun l => F (a :: l) :=
  Dynamics.expList_succ T F

lemma expList_nonneg {T : ℕ} {F : List α → ℝ} (h : ∀ l, 0 ≤ F l) :
    0 ≤ expList α T F :=
  Dynamics.expList_nonneg h

lemma expList_le_expList {T : ℕ} {F G : List α → ℝ} (h : ∀ l, F l ≤ G l) :
    expList α T F ≤ expList α T G :=
  Dynamics.expList_le_expList h

lemma expList_add (T : ℕ) (F G : List α → ℝ) :
    expList α T (fun l => F l + G l) = expList α T F + expList α T G :=
  Dynamics.expList_add T F G

lemma expList_const_mul (T : ℕ) (c : ℝ) (F : List α → ℝ) :
    expList α T (fun l => c * F l) = c * expList α T F :=
  Dynamics.expList_const_mul T c F

lemma expList_const [Nonempty α] (T : ℕ) (c : ℝ) :
    expList α T (fun _ => c) = c :=
  Dynamics.expList_const T c

lemma expList_append (T₁ T₂ : ℕ) (F : List α → ℝ) :
    expList α (T₁ + T₂) F
      = expList α T₁ fun l₁ => expList α T₂ fun l₂ => F (l₁ ++ l₂) :=
  Dynamics.expList_append T₁ T₂ F

@[inherit_doc Dynamics.avg_mul_prod]
lemma avg_mul_prod {β δ : Type*} [Fintype β] [Fintype δ] (g : β → ℝ) (h : δ → ℝ) :
    avg (fun p : β × δ => g p.1 * h p.2) = avg g * avg h :=
  Dynamics.avg_mul_prod g h

@[inherit_doc Dynamics.avg_fst_mul]
lemma avg_fst_mul {β δ : Type*} [Fintype β] [Fintype δ] [Nonempty δ] (g : β → ℝ) :
    avg (fun p : β × δ => g p.1) = avg g :=
  Dynamics.avg_fst_mul g

@[inherit_doc Dynamics.avg_snd_mul]
lemma avg_snd_mul {β δ : Type*} [Fintype β] [Nonempty β] [Fintype δ] (h : δ → ℝ) :
    avg (fun p : β × δ => h p.2) = avg h :=
  Dynamics.avg_snd_mul h

@[inherit_doc Dynamics.avg_equiv]
lemma avg_equiv {β : Type*} [Fintype β] (e : α ≃ β) (F : β → ℝ) :
    avg (fun a => F (e a)) = avg F :=
  Dynamics.avg_equiv e F

@[inherit_doc Dynamics.avg_prod_pi]
lemma avg_prod_pi {γ : Type*} [Fintype γ] :
    ∀ (n : ℕ) (f : Fin n → γ → ℝ),
      avg (fun x : Fin n → γ => ∏ i, f i (x i)) = ∏ i, avg (f i) :=
  Dynamics.avg_prod_pi

@[inherit_doc Dynamics.avg_eval]
lemma avg_eval {γ : Type*} [Fintype γ] [Nonempty γ] (n : ℕ) (v : Fin n) (G : γ → ℝ) :
    avg (fun x : Fin n → γ => G (x v)) = avg G :=
  Dynamics.avg_eval n v G

end ThreeMajority
