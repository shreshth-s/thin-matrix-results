import FiniteFoldedPlan

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 400000

/-! Retain every executed graph block and copy each original incidence answer.
The dependent type alias below is erased; it does not evaluate another graph.
This finite scheduler retains all repeated preparations and all requested
coefficient copies. Its mixed ledger preserves the earlier setup omissions;
it is not a fast backend or a complete binary execution-cost theorem. -/
namespace ThinMatrix.GraphBlockSchedule
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators
variable {n h r : ℕ}

abbrev Trace (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) :=
  type_of% (GraphBandSchedule.execute f p block input ell)

def child (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) :
    ToomCook.Counted (((b : Fin (CompactBlocks.blockCount n h)) × Trace f p b input ell) ×
      Vector Cell (FoldedBackendExecution.windowQuerySize n)) :=
  let out := GraphBandSchedule.execute f p block input ell
  let rows := Vector.ofFn (fun i => (CountedCyclicCollection.output out.2.2.value i).get 0)
  ⟨(⟨block,out⟩,rows),out.1.operations+out.2.1.control+out.2.2.operations+32*FoldedBackendExecution.windowQuerySize n+8⟩

def execute (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) :=
  let ids : Vector (Fin (CompactBlocks.blockCount n h)) (CompactBlocks.blockCount n h) := Vector.ofFn id
  let blocks := GroupedPreparation.ofStoredFn ids (fun i => child f p i input ell)
  let indices : Vector (Fin (EndToEndAPSP.incidenceSize n h)) (EndToEndAPSP.incidenceSize n h) := Vector.ofFn id
  let cells := tabulate indices (fun i =>
    let x := (FoldedBackendExecution.groupedIncidenceEquiv n h).symm (indices.get i)
    let out := copy ((blocks.get x.1).value.2.get x.2)
    (⟨out.value,out.bitSteps,24⟩ : Run Cell))
  (ids,blocks,indices,cells)

def output (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) : Cell :=
  (execute f p input ell).2.2.2.value.get i

theorem execute_value (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    view (output f p input ell i)=
      let x := (FoldedBackendExecution.groupedIncidenceEquiv n h).symm i
      FoldedRequestBounds.count f x.1 input x.2 := by
  simp only [output,execute,tabulate_get,Vector.get_ofFn,id_eq,GroupedPreparation.ofStoredFn_eq,child,copy_view]
  change view (GraphBandSchedule.output f p ((FoldedBackendExecution.groupedIncidenceEquiv n h).symm i).1 input ell
    ((FoldedBackendExecution.groupedIncidenceEquiv n h).symm i).2)=_
  exact GraphBandSchedule.execute_value f p _ input ell _

theorem execute_bound (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    (view (output f p input ell i)).natAbs≤h := by
  rw [execute_value]; exact FoldedRequestBounds.count_bound f _ input _

theorem execute_nonnegative (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    0≤view (output f p input ell i) := by
  rw [execute_value]; exact FoldedRequestBounds.count_nonnegative f _ input _

theorem extraction_bits (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) :
    (execute f p input ell).2.2.2.bitSteps≤EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size := by
  unfold execute
  dsimp only
  apply tabulate_bits
  intro i
  apply copy_price
  apply Nat.size_le_size
  simp only [GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn,id_eq,child]
  exact GraphBandSchedule.execute_bound f p _ input ell _

theorem extraction_control (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) :
    (execute f p input ell).2.2.2.control≤56*EndToEndAPSP.incidenceSize n h+8 := by
  have hc := tabulate_control (execute f p input ell).2.2.1
    (fun i =>
      let x := (FoldedBackendExecution.groupedIncidenceEquiv n h).symm ((execute f p input ell).2.2.1.get i)
      let out := copy (((execute f p input ell).2.1.get x.1).value.2.get x.2)
      (⟨out.value,out.bitSteps,24⟩ : Run Cell)) (W:=24) (fun _ => le_refl _)
  simpa only [execute,Nat.reduceAdd,Nat.mul_comm] using hc

/-- Includes every child, both explicit index arrays and copied incidence
cells. Child charges retain translation numerator arithmetic and binary-state
updates, but still omit selection/power-table control and binary address prices. -/
def recordedWork (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) : ℕ :=
  let out := execute f p input ell
  (∑ b, (out.2.1.get b).operations)+out.2.2.2.bitSteps+out.2.2.2.control+
    64*out.1.toArray.size+32*out.2.2.1.toArray.size+24

noncomputable def recordedBudget (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) : ℕ :=
  (∑ b : Fin (CompactBlocks.blockCount n h), (
    (BinaryBackendExecution.prepareShapeRuntime p.L p.m).operations+
    (32*TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)+32)+
    GraphBandSchedule.accumulationBudget f p b input ell+32*FoldedBackendExecution.windowQuerySize n+8))+
    EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size+
    (56*EndToEndAPSP.incidenceSize n h+8)+64*CompactBlocks.blockCount n h+
    32*EndToEndAPSP.incidenceSize n h+24

theorem recorded_work_le (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) : recordedWork f p input ell≤recordedBudget f p input ell := by
  have hs := Finset.sum_le_sum (fun b (_ : b∈(Finset.univ : Finset (Fin (CompactBlocks.blockCount n h)))) =>
    Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left (GraphBandSchedule.execute_accumulation_work f p b input ell)
      ((BinaryBackendExecution.prepareShapeRuntime p.L p.m).operations+
      (32*TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)+32))) (32*FoldedBackendExecution.windowQuerySize n)) 8)
  have hb := extraction_bits f p input ell
  have hc := extraction_control f p input ell
  simp only [recordedWork,recordedBudget,execute,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn,id_eq,
    child,GraphBandSchedule.execute,RetainedBandIndices.produce_control,Vector.size_toArray] at hs hb hc ⊢
  omega

#print axioms execute_value
#print axioms execute_bound
#print axioms execute_nonnegative
#print axioms extraction_bits
#print axioms extraction_control
#print axioms recorded_work_le
end ThinMatrix.GraphBlockSchedule
