import WindowPrefixProgram

set_option autoImplicit false

/-! Exact adjoint identities for the retained opposite transform. Finite sums
are over every ternary word. These are coefficient identities, not an assumed
rectangular algorithm or a cost model. -/
namespace ThinMatrix.OppositeTensorBridge
open CroppedGroupedSuffix OppositeWindowLayer
open scoped BigOperators

def exchange {N : ℕ} (axis : Fin N) (x : Word N × Fin 3) : Word N × Fin 3 :=
  (Function.update x.1 axis x.2,x.1 axis)

theorem exchange_twice {N : ℕ} (axis : Fin N) : Function.Involutive (exchange axis) := by
  rintro ⟨w,a⟩
  apply Prod.ext
  · funext i
    by_cases h : i=axis
    · subst i; simp [exchange]
    · simp [exchange]
  · simp [exchange]

def exchangeEquiv {N : ℕ} (axis : Fin N) : Equiv.Perm (Word N × Fin 3) :=
  ⟨exchange axis,exchange axis,exchange_twice axis,exchange_twice axis⟩

noncomputable def push {N : ℕ} (axis : Fin N) (H : Word N → ℤ) (v : Word N) : ℤ :=
  ∑ a, H (Function.update v axis a)*matrix a (v axis)

theorem local_adjoint {N : ℕ} (axis : Fin N) (H X : Word N → ℤ) :
    (∑ w, H w*localStep axis X w)=∑ v, push axis H v*X v := by
  simp only [localStep_sum,Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun z : Word N × Fin 3 => H z.1*(matrix (z.1 axis) z.2*X (Function.update z.1 axis z.2)))]
  rw [← Equiv.sum_comp (exchangeEquiv axis) (fun z => H z.1*(matrix (z.1 axis) z.2*X (Function.update z.1 axis z.2)))]
  rw [Fintype.sum_prod_type]
  simp only [exchangeEquiv,Equiv.coe_fn_mk,exchange,Function.update_self,Function.update_idem,Function.update_eq_self,push,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro a _
  ring

noncomputable def pushAxes {N : ℕ} : List (Fin N) → (Word N → ℤ) → Word N → ℤ
  | [], H => H
  | axis::axes, H => push axis (pushAxes axes H)

theorem evaluate_adjoint {N : ℕ} (axes : List (Fin N)) (H X : Word N → ℤ) :
    (∑ w, H w*RetainedOppositeTransform.evaluate axes X w)=∑ v, pushAxes axes H v*X v := by
  induction axes generalizing X with
  | nil => rfl
  | cons axis axes ih =>
    simp only [RetainedOppositeTransform.evaluate,pushAxes]
    rw [ih,local_adjoint]

/-- A finite product remains a finite product under the local adjoint. -/
theorem push_product {N : ℕ} (axis : Fin N) (f : Fin N → Fin 3 → ℤ) (v : Word N) :
    push axis (fun w => ∏ i, f i (w i)) v=
      ∏ i, (Function.update f axis (fun b => ∑ a, f axis a*matrix a b)) i (v i) := by
  have hprod (a : Fin 3) : (∏ i, f i (Function.update v axis a i))=
      (∏ i ∈ Finset.univ.erase axis, f i (v i))*f axis a := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ axis)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  unfold push
  simp_rw [hprod,mul_assoc]
  rw [← Finset.mul_sum,← Finset.prod_erase_mul _ _ (Finset.mem_univ axis)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

noncomputable def pushForms {N : ℕ} : List (Fin N) → (Fin N → Fin 3 → ℤ) → Fin N → Fin 3 → ℤ
  | [], f => f
  | axis::axes, f => Function.update (pushForms axes f) axis (fun b => ∑ a, (pushForms axes f) axis a*matrix a b)

theorem pushAxes_product {N : ℕ} (axes : List (Fin N)) (f : Fin N → Fin 3 → ℤ) (v : Word N) :
    pushAxes axes (fun w => ∏ i, f i (w i)) v=∏ i, pushForms axes f i (v i) := by
  induction axes generalizing v with
  | nil => rfl
  | cons axis axes ih =>
    simp only [pushAxes,pushForms]
    have he : pushAxes axes (fun w => ∏ i, f i (w i))=fun w => ∏ i, pushForms axes f i (w i) := funext ih
    rw [he,push_product]

theorem tensor_evaluate {N : ℕ} (axes : List (Fin N)) (f : Fin N → Fin 3 → ℤ) (X : Word N → ℤ) :
    EncoderCorrectness.tensorSum (fun _ : Fin N => 3) f (RetainedOppositeTransform.evaluate axes X)=
      EncoderCorrectness.tensorSum (fun _ : Fin N => 3) (pushForms axes f) X := by
  unfold EncoderCorrectness.tensorSum
  calc
    _ = ∑ w, (∏ i, f i (w i))*RetainedOppositeTransform.evaluate axes X w := by
      apply Finset.sum_congr rfl; intro w _; ring
    _ = ∑ v, pushAxes axes (fun w => ∏ i, f i (w i)) v*X v := evaluate_adjoint axes _ X
    _ = _ := by
      simp only [pushAxes_product]
      apply Finset.sum_congr rfl; intro v _; ring

theorem pushForms_nodup {N : ℕ} (axes : List (Fin N)) (hn : axes.Nodup)
    (f : Fin N → Fin 3 → ℤ) (i : Fin N) (b : Fin 3) :
    pushForms axes f i b=if i∈axes then ∑ a, f i a*matrix a b else f i b := by
  induction axes generalizing i b with
  | nil => simp [pushForms]
  | cons axis axes ih =>
    have hs := List.nodup_cons.mp hn
    by_cases hi : i=axis
    · subst i
      simp only [pushForms,Function.update_self,List.mem_cons_self,↓reduceIte]
      simp only [ih hs.2,if_neg hs.1]
    · simp only [pushForms,Function.update_of_ne hi,List.mem_cons,hi,false_or,ih hs.2]

def renameWords {M N : ℕ} (p : Fin M ≃ Fin N) : Word N ≃ Word M where
  toFun w := fun i => w (p i)
  invFun w := fun i => w (p.symm i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

theorem tensor_reindex {M N : ℕ} (p : Fin M ≃ Fin N) (f : Fin M → Fin 3 → ℤ) (X : Word N → ℤ) :
    EncoderCorrectness.tensorSum (fun _ : Fin M => 3) f (fun w => X (fun i => w (p.symm i)))=
      EncoderCorrectness.tensorSum (fun _ : Fin N => 3) (fun i => f (p.symm i)) X := by
  unfold EncoderCorrectness.tensorSum
  rw [← Equiv.sum_comp (renameWords p) (fun w => X (fun i => w (p.symm i))*∏ i, f i (w i))]
  simp only [renameWords,Equiv.coe_fn_mk,Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  exact (Equiv.prod_comp p.symm (fun i => f i (w (p i)))).symm.trans (by simp)

/-- Original-basis forms after exactly the actual opposite axes. -/
theorem actual_forms {k : ℕ} (f : Fin (2*k) → Fin 3 → ℤ) (i : Fin (2*k)) (a : Fin 3) :
    pushForms (RetainedOppositeTransform.axes k) f i a=
      if k ≤ i.val then ∑ b, f i b*matrix b a else f i a := by
  rw [pushForms_nodup _ (RetainedOppositeTransform.axes_unique k)]
  simp only [RetainedOppositeTransform.axes_cover]

#print axioms tensor_reindex
#print axioms actual_forms
#print axioms exchange_twice
#print axioms local_adjoint
#print axioms evaluate_adjoint
#print axioms push_product
#print axioms pushAxes_product
#print axioms tensor_evaluate
#print axioms pushForms_nodup
end ThinMatrix.OppositeTensorBridge
