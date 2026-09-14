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
noncomputable abbrev expList (α : Type*) [Fintype α] (T : ℕ) (F : List α → ℝ) : ℝ := Dynamics.expList α T F

lemma avg_nonneg {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ avg f := by
  intros
  apply Dynamics.avg_nonneg <;> assumption

lemma avg_le_avg {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : avg f ≤ avg g := by
  intros
  apply Dynamics.avg_le_avg <;> assumption

lemma avg_add (f g : α → ℝ) : avg (fun a => f a + g a) = avg f + avg g := by
  intros
  apply Dynamics.avg_add <;> assumption

lemma avg_sub (f g : α → ℝ) : avg (fun a => f a - g a) = avg f - avg g := by
  intros
  apply Dynamics.avg_sub <;> assumption

lemma avg_const_mul (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  intros
  apply Dynamics.avg_const_mul <;> assumption

lemma avg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) := by
  intros
  apply Dynamics.avg_sum <;> assumption

@[inherit_doc Dynamics.avg_indicator]
lemma avg_indicator (P : α → Prop) [DecidablePred P] :
    avg (fun a => if P a then (1 : ℝ) else 0)
      = ((univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := by
  intros
  apply Dynamics.avg_indicator <;> assumption

lemma card_cast_pos [Nonempty α] : (0 : ℝ) < (Fintype.card α : ℝ) := by
  intros
  apply Dynamics.card_cast_pos <;> assumption

lemma avg_const [Nonempty α] (c : ℝ) : avg (fun _ : α => c) = c := by
  intros
  apply Dynamics.avg_const <;> assumption

@[simp] lemma expList_zero (F : List α → ℝ) : expList α 0 F = F [] := by
  intros
  apply Dynamics.expList_zero <;> assumption

lemma expList_succ (T : ℕ) (F : List α → ℝ) :
    expList α (T + 1) F = avg fun a : α => expList α T fun l => F (a :: l) := by
  intros
  apply Dynamics.expList_succ <;> assumption

lemma expList_nonneg {T : ℕ} {F : List α → ℝ} (h : ∀ l, 0 ≤ F l) :
    0 ≤ expList α T F := by
  intros
  apply Dynamics.expList_nonneg <;> assumption

lemma expList_le_expList {T : ℕ} {F G : List α → ℝ} (h : ∀ l, F l ≤ G l) :
    expList α T F ≤ expList α T G := by
  intros
  apply Dynamics.expList_le_expList <;> assumption

lemma expList_add (T : ℕ) (F G : List α → ℝ) :
    expList α T (fun l => F l + G l) = expList α T F + expList α T G := by
  intros
  apply Dynamics.expList_add <;> assumption

lemma expList_const_mul (T : ℕ) (c : ℝ) (F : List α → ℝ) :
    expList α T (fun l => c * F l) = c * expList α T F := by
  intros
  apply Dynamics.expList_const_mul <;> assumption

lemma expList_const [Nonempty α] (T : ℕ) (c : ℝ) :
    expList α T (fun _ => c) = c := by
  intros
  apply Dynamics.expList_const <;> assumption

lemma expList_append (T₁ T₂ : ℕ) (F : List α → ℝ) :
    expList α (T₁ + T₂) F
      = expList α T₁ fun l₁ => expList α T₂ fun l₂ => F (l₁ ++ l₂) := by
  intros
  apply Dynamics.expList_append <;> assumption

@[inherit_doc Dynamics.avg_mul_prod]
lemma avg_mul_prod {β δ : Type*} [Fintype β] [Fintype δ] (g : β → ℝ) (h : δ → ℝ) :
    avg (fun p : β × δ => g p.1 * h p.2) = avg g * avg h := by
  intros
  apply Dynamics.avg_mul_prod <;> assumption

@[inherit_doc Dynamics.avg_fst_mul]
lemma avg_fst_mul {β δ : Type*} [Fintype β] [Fintype δ] [Nonempty δ] (g : β → ℝ) :
    avg (fun p : β × δ => g p.1) = avg g := by
  intros
  apply Dynamics.avg_fst_mul <;> assumption

@[inherit_doc Dynamics.avg_snd_mul]
lemma avg_snd_mul {β δ : Type*} [Fintype β] [Nonempty β] [Fintype δ] (h : δ → ℝ) :
    avg (fun p : β × δ => h p.2) = avg h := by
  intros
  apply Dynamics.avg_snd_mul <;> assumption

@[inherit_doc Dynamics.avg_equiv]
lemma avg_equiv {β : Type*} [Fintype β] (e : α ≃ β) (F : β → ℝ) :
    avg (fun a => F (e a)) = avg F := by
  intros
  apply Dynamics.avg_equiv <;> assumption

@[inherit_doc Dynamics.avg_prod_pi]
lemma avg_prod_pi {γ : Type*} [Fintype γ] :
    ∀ (n : ℕ) (f : Fin n → γ → ℝ),
      avg (fun x : Fin n → γ => ∏ i, f i (x i)) = ∏ i, avg (f i) := by
  intros
  apply Dynamics.avg_prod_pi <;> assumption

@[inherit_doc Dynamics.avg_eval]
lemma avg_eval {γ : Type*} [Fintype γ] [Nonempty γ] (n : ℕ) (v : Fin n) (G : γ → ℝ) :
    avg (fun x : Fin n → γ => G (x v)) = avg G := by
  intros
  apply Dynamics.avg_eval <;> assumption

end ThreeMajority
