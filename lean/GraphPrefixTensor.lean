import GraphPrefixProgram

set_option autoImplicit false

/-! Full tensor identity back to the actual original graph-derived window.
These queries specify retained encoded cells. Executable request generation,
batching and completion are separate pending connections. -/
namespace ThinMatrix.GraphPrefixTensor
open CroppedGroupedSuffix ExactHalfSourcePlan ResidualFamilyKeys GoodMapEmbedding
open scoped BigOperators

noncomputable def originalForms {k : ℕ} (ell : ℕ) (normal : Bool)
    (slot : Fin (RetainedRootWindows.slots k))
    (f : Fin (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell) → Fin 3 → ℤ) :
    Fin (2*k) → Fin 3 → ℤ :=
  OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes k)
    (fun i => f (Fin.cast (WindowPrefixProgram.dimension k ell).symm
      ((RetainedWindowPermutation.order k (min ell k) normal slot).symm i)))

theorem originalForms_value {k : ℕ} (ell : ℕ) (normal : Bool)
    (slot : Fin (RetainedRootWindows.slots k))
    (f : Fin (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell) → Fin 3 → ℤ)
    (i : Fin (2*k)) (a : Fin 3) :
    originalForms ell normal slot f i a=
      let b := Fin.cast (WindowPrefixProgram.dimension k ell).symm
        ((RetainedWindowPermutation.order k (min ell k) normal slot).symm i)
      if k ≤ i.val then ∑ j, f b j*OppositeWindowLayer.matrix j a else f b a :=
  OppositeTensorBridge.actual_forms _ i a

theorem window_tensor {k C : ℕ} (ell : ℕ) (normal : Bool)
    (slot : Fin (RetainedRootWindows.slots k)) (X : BinaryWindowPartition.Source k C)
    (f : Fin (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell) → Fin 3 → ℤ) (col : Fin C) :
    EncoderCorrectness.tensorSum (fun _ : Fin (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell) => 3) f
      (fun w => OppositeWindowLayer.value
        (RetainedWindowPermutation.prepare (min ell k) normal slot (RetainedOppositeTransform.execute X).value.result).value.coefficients
        (fun i => w (Fin.cast (WindowPrefixProgram.dimension k ell).symm i)) col)=
      EncoderCorrectness.tensorSum (fun _ : Fin (2*k) => 3) (originalForms ell normal slot f)
        (fun w => BinaryWindowPartition.sourceValue X w col) := by
  let Y := (RetainedOppositeTransform.execute X).value.result
  let order := RetainedWindowPermutation.order k (min ell k) normal slot
  calc
    _ = EncoderCorrectness.tensorSum (fun _ : Fin (2*k) => 3)
        (fun i => f (Fin.cast (WindowPrefixProgram.dimension k ell).symm i))
        (fun w => OppositeWindowLayer.value (RetainedWindowPermutation.prepare (min ell k) normal slot Y).value.coefficients w col) := by
      simpa only [finCongr,Equiv.symm_mk,Equiv.coe_fn_mk] using
        OppositeTensorBridge.tensor_reindex (finCongr (WindowPrefixProgram.dimension k ell)) f
          (fun w => OppositeWindowLayer.value (RetainedWindowPermutation.prepare (min ell k) normal slot Y).value.coefficients w col)
    _ = EncoderCorrectness.tensorSum (fun _ : Fin (2*k) => 3)
        (fun i => f (Fin.cast (WindowPrefixProgram.dimension k ell).symm (order.symm i)))
        (fun w => OppositeWindowLayer.value Y w col) := by
      simp_rw [RetainedWindowPermutation.prepare_value]
      exact OppositeTensorBridge.tensor_reindex order _ (fun w => OppositeWindowLayer.value Y w col)
    _ = _ := by
      dsimp only [Y]
      simp_rw [RetainedOppositeTransform.execute_value]
      exact OppositeTensorBridge.tensor_evaluate _ _ _

theorem fromInputs_left_original_query {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m)))
    (pair : Fin (2^(WindowPrefixProgram.length (p.L-p.m) ell)))
    (q : Fin (WindowPrefixProgram.prefixLength (p.L-p.m) ell) → Fin 4)
    (active : Finset (Fin (WindowPrefixProgram.length (p.L-p.m) ell))) (col : Fin ((p.m+1)*f.cyclic)) :
    let window := ((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).1).get i).get j).get c)
    CappedPrefixProgram.query (((((((((GraphPrefixProgram.fromInputs f p block input bandL bandR ell).encoded.value.get u).get v).get run).1).get i).get j).get c).get slot).encoded pair q active col=
      EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3)
        (originalForms ell (decide (window.counts.2≤window.counts.1)) slot
          (Fin.append (fun a => BinaryPrefixContraction.form (q a))
          (fun a => CroppedGroupedSuffix.localForm (((GroupedPreparation.pairKeys (WindowPrefixProgram.length (p.L-p.m) ell)).get pair).get a) (decide (a∈active)))))
        (fun w => BinaryWindowPartition.sourceValue (window.windows.components.get slot) w col) := by
  dsimp only
  rw [GraphPrefixProgram.fromInputs_left_query]
  simp_rw [GraphWindowPermutations.fromInputs_left_entry,GraphWindowTransforms.fromInputs_left_entry]
  exact window_tensor ell _ slot _ _ col

theorem fromInputs_right_original_query {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m)))
    (pair : Fin (2^(WindowPrefixProgram.length (p.L-p.m) ell)))
    (q : Fin (WindowPrefixProgram.prefixLength (p.L-p.m) ell) → Fin 4)
    (active : Finset (Fin (WindowPrefixProgram.length (p.L-p.m) ell))) (col : Fin ((p.m+1)*f.cyclic)) :
    let window := ((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).2).get i).get j).get c)
    CappedPrefixProgram.query (((((((((GraphPrefixProgram.fromInputs f p block input bandL bandR ell).encoded.value.get u).get v).get run).2).get i).get j).get c).get slot).encoded pair q active col=
      EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3)
        (originalForms ell (decide (window.counts.2≤window.counts.1)) slot
          (Fin.append (fun a => BinaryPrefixContraction.form (q a))
          (fun a => CroppedGroupedSuffix.localForm (((GroupedPreparation.pairKeys (WindowPrefixProgram.length (p.L-p.m) ell)).get pair).get a) (decide (a∈active)))))
        (fun w => BinaryWindowPartition.sourceValue (window.windows.components.get slot) w col) := by
  dsimp only
  rw [GraphPrefixProgram.fromInputs_right_query]
  simp_rw [GraphWindowPermutations.fromInputs_right_entry,GraphWindowTransforms.fromInputs_right_entry]
  exact window_tensor ell _ slot _ _ col

#print axioms fromInputs_left_original_query
#print axioms fromInputs_right_original_query
#print axioms originalForms_value
#print axioms window_tensor
end ThinMatrix.GraphPrefixTensor
