import OppositeWindowLayer

set_option autoImplicit false

/-! Full forward opposite transform with every intermediate layer retained.
The input is the actual flattened window storage. Axes and coefficient
columns retain their order, including the empty-axis boundary case. -/
namespace ThinMatrix.RetainedOppositeTransform
open BinaryGroupedCoordinates OppositeWindowLayer CroppedGroupedSuffix
open scoped BigOperators

structure Trace (N C : ℕ) where
  result : Source N C
  layers : List (Source N C)

def run {N C : ℕ} : List (Fin N) → Source N C → Run (Trace N C)
  | [], X => ⟨⟨X,[]⟩,0,4⟩
  | axis::axes, X =>
      let layer := OppositeWindowLayer.execute axis X
      let rest := run axes layer.value
      ⟨⟨rest.value.result,layer.value::rest.value.layers⟩,
        layer.bitSteps+rest.bitSteps,layer.control+rest.control+8⟩

def evaluate {N : ℕ} : List (Fin N) → (Word N → ℤ) → Word N → ℤ
  | [], X => X
  | axis::axes, X => evaluate axes (localStep axis X)

theorem run_value {N C : ℕ} (axes : List (Fin N)) (X : Source N C) (w : Word N) (c : Fin C) :
    value (run axes X).value.result w c=evaluate axes (fun w => value X w c) w := by
  induction axes generalizing X with
  | nil => rfl
  | cons axis axes ih =>
    simp only [run,ih,evaluate]
    congr 1
    funext v
    exact OppositeWindowLayer.execute_value axis X v c

theorem run_bound {N C : ℕ} (axes : List (Fin N)) (X : Source N C) (A : ℕ) (ha : Bound X A) :
    Bound (run axes X).value.result (2^axes.length*A) := by
  induction axes generalizing X A with
  | nil => simpa only [run,List.length_nil,pow_zero,one_mul] using ha
  | cons axis axes ih =>
    have h := ih (OppositeWindowLayer.execute axis X).value (2*A) (OppositeWindowLayer.execute_bound axis X A ha)
    simpa only [run,List.length_cons,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem run_supported {N C : ℕ} (axes : List (Fin N)) (X : Source N C)
    (P : (Fin N → Bool) → Prop) (hs : Supported P X) : Supported P (run axes X).value.result := by
  induction axes generalizing X with
  | nil => exact hs
  | cons axis axes ih => exact ih _ (OppositeWindowLayer.execute_supported axis X P hs)

def layerPrice (N C A : ℕ) : ℕ := 3^N*(3*addressBudget N+C*(5*BackendScalarBits.backendScalarUnit A.size))

theorem layerPrice_mono (N C A B : ℕ) (h : A≤B) : layerPrice N C A≤layerPrice N C B := by
  have hs := Nat.size_le_size h
  unfold layerPrice BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  gcongr

def bitBudget (N C n A : ℕ) : ℕ := n*layerPrice N C (2^n*A)
def controlBudget (N C n : ℕ) : ℕ := n*(OppositeWindowLayer.controlBudget N C+8)+4

theorem run_bits {N C : ℕ} (axes : List (Fin N)) (X : Source N C) (A : ℕ) (ha : Bound X A) :
    (run axes X).bitSteps≤bitBudget N C axes.length A := by
  induction axes generalizing X A with
  | nil => simp [run,bitBudget]
  | cons axis axes ih =>
    have hr := ih (OppositeWindowLayer.execute axis X).value (2*A) (OppositeWindowLayer.execute_bound axis X A ha)
    have hl := OppositeWindowLayer.execute_bits axis X A ha
    have hp : 2*A≤2^(axes.length+1)*A := by
      have hh : (2:ℕ)^1≤2^(axes.length+1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa only [pow_one] using Nat.mul_le_mul_right A hh
    have hm := layerPrice_mono N C (2*A) (2^(axes.length+1)*A) hp
    change _≤layerPrice N C (2*A) at hl
    have he : 2^axes.length*(2*A)=2^(axes.length+1)*A := by ring
    simp only [bitBudget,he] at hr
    simp only [run,bitBudget,List.length_cons]
    nlinarith

theorem run_control {N C : ℕ} (axes : List (Fin N)) (X : Source N C) :
    (run axes X).control≤controlBudget N C axes.length := by
  induction axes generalizing X with
  | nil => simp [run,controlBudget]
  | cons axis axes ih =>
    have hr := ih (OppositeWindowLayer.execute axis X).value
    have hl := OppositeWindowLayer.execute_control axis X
    simp only [run,controlBudget,List.length_cons] at *
    nlinarith

theorem run_layers {N C : ℕ} (axes : List (Fin N)) (X : Source N C) :
    (run axes X).value.layers.length=axes.length := by
  induction axes generalizing X with
  | nil => rfl
  | cons axis axes ih => simp only [run,List.length_cons,ih]

theorem run_cells {N C : ℕ} (axes : List (Fin N)) (X : Source N C) :
    ((run axes X).value.layers.map (fun layer => (layer.toList.map (fun row => row.toArray.size)).sum)).sum=
      axes.length*3^N*C := by
  simp only [Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul,run_layers]
  ring

def axes (k : ℕ) : List (Fin (2*k)) := (List.finRange k).map (BinaryWindowPartition.halfIndex false)

theorem axes_length (k : ℕ) : (axes k).length=k := by simp [axes]

theorem axes_unique (k : ℕ) : (axes k).Nodup := by
  apply List.Nodup.map _ (List.nodup_finRange k)
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [BinaryWindowPartition.halfIndex,Bool.false_eq_true,↓reduceIte] at hh
  omega

theorem axes_cover {k : ℕ} (i : Fin (2*k)) : i∈axes k ↔ k ≤ i.val := by
  simp only [axes,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,rfl⟩
    simp [BinaryWindowPartition.halfIndex]
  · intro hi
    refine ⟨⟨i.val-k,by have := i.isLt; omega⟩,?_⟩
    apply Fin.ext
    simp only [BinaryWindowPartition.halfIndex,Bool.false_eq_true,↓reduceIte]
    omega

def execute {k C : ℕ} (X : BinaryWindowPartition.Source k C) : Run (Trace (2*k) C) :=
  let out := run (axes k) X
  ⟨out.value,out.bitSteps,out.control+8*k+8⟩

theorem execute_value {k C : ℕ} (X : BinaryWindowPartition.Source k C) (w : Word (2*k)) (c : Fin C) :
    value (execute X).value.result w c=evaluate (axes k) (fun w => BinaryWindowPartition.sourceValue X w c) w :=
  run_value _ _ _ _

theorem execute_bound {k C : ℕ} (X : BinaryWindowPartition.Source k C) (A : ℕ) (ha : BinaryWindowPartition.InputBound X A) :
    Bound (execute X).value.result (2^k*A) := by simpa only [execute,axes_length] using run_bound (axes k) X A ha

theorem execute_bits {k C : ℕ} (X : BinaryWindowPartition.Source k C) (A : ℕ) (ha : BinaryWindowPartition.InputBound X A) :
    (execute X).bitSteps≤bitBudget (2*k) C k A := by simpa only [execute,axes_length] using run_bits (axes k) X A ha

theorem execute_control {k C : ℕ} (X : BinaryWindowPartition.Source k C) :
    (execute X).control≤controlBudget (2*k) C k+8*k+8 := by
  have h := run_control (axes k) X
  simpa only [execute,axes_length,Nat.add_assoc] using Nat.add_le_add_right h (8*k+8)

theorem localStep_sum_inputs {N : ℕ} {I : Type*} [Fintype I] (axis : Fin N)
    (X : I → Word N → ℤ) (w : Word N) :
    localStep axis (fun w => ∑ i, X i w) w=∑ i, localStep axis (X i) w := by
  simp only [localStep_sum,Finset.mul_sum]
  exact Finset.sum_comm

theorem evaluate_sum {N : ℕ} {I : Type*} [Fintype I] (axes : List (Fin N))
    (X : I → Word N → ℤ) (w : Word N) :
    evaluate axes (fun w => ∑ i, X i w) w=∑ i, evaluate axes (X i) w := by
  induction axes generalizing X w with
  | nil => rfl
  | cons axis axes ih =>
    simp only [evaluate]
    have he : localStep axis (fun w => ∑ i, X i w)=fun w => ∑ i, localStep axis (X i) w := by
      funext v; exact localStep_sum_inputs axis X v
    rw [he,ih]

/-- Window components may be transformed separately and then summed. This
uses arbitrary coefficient functions, including entangled original roots. -/
theorem sum_windows {L m C : ℕ} [NeZero C] (ell : ℕ)
    (raw : BinarySourceFormation.RawStore L C) (a b : ResidualFamilyKeys.Mask L m)
    (channel : ResidualFamilyKeys.Channel m) (w : Word (2*(L-m))) (d : Fin (m+1)) (r : Fin C) :
    (∑ slot, value (execute (((RetainedRootWindows.execute ell (RetainedResidualFamily.produce raw a b channel).value).value.windows.components.get slot))).value.result
      w (finProdFinEquiv (d,r)))=
      evaluate (axes (L-m)) (fun word => BinaryResidualPolynomial.cellView
        ((ResidualWindowSource.rows (RetainedResidualFamily.produce raw a b channel).value).get
          (StoredGroupedCompletion.rawIndex _ word)) d r) w := by
  simp_rw [execute_value]
  rw [← evaluate_sum]
  congr 1
  funext word
  exact RetainedRootWindows.produce_reconstruct ell raw a b channel word d r

/-- The selected window cap is preserved by every forward layer. -/
theorem window_supported {k C : ℕ} [NeZero k] (ell cap cn co : ℕ)
    (X : BinaryWindowPartition.Source k C) (s : Fin k) :
    Supported (fun bits => CyclicLightWindow.weight ell
      (fun i => bits (BinaryWindowPartition.halfIndex (decide (co≤cn)) i)) s≤(cap-max cn co)*ell/k)
      (execute ((BinaryWindowPartition.prepare ell cap cn co X).value.components.get s)).value.result := by
  apply run_supported
  intro word col hp
  exact BinaryWindowPartition.window_supported ell _ _ X s word col (by
    change ¬CyclicLightWindow.weight ell (BinaryWindowPartition.bits (decide (co≤cn)) word) s≤_ at hp
    omega)

#print axioms localStep_sum_inputs
#print axioms evaluate_sum
#print axioms sum_windows
#print axioms window_supported
#print axioms run_value
#print axioms run_bound
#print axioms run_supported
#print axioms layerPrice_mono
#print axioms run_bits
#print axioms run_control
#print axioms run_layers
#print axioms run_cells
#print axioms axes_length
#print axioms axes_unique
#print axioms axes_cover
#print axioms execute_value
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.RetainedOppositeTransform
