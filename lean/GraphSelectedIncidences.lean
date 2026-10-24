import GraphSelectedNormalize

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

/-! Copy the selected normalized M by B scalar grid into the controller's
incidence order. The quotient/remainder index is evaluated once per output;
original occurrences, including identical physical requests, stay distinct. -/
namespace ThinMatrix.GraphSelectedIncidences
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev B := CompactBlocks.blockCount n h
abbrev Values := Vector (Vector BinaryLowHighNormalize.CellOutput (B (n:=n) (h:=h))) (M (n:=n))

variable {p} in
 def execute (values : Values (n:=n) (h:=h)) : Run (Vector Cell (EndToEndAPSP.incidenceSize n h)) :=
  tabulate (Vector.replicate (EndToEndAPSP.incidenceSize n h) ()) fun i =>
    let x := (FoldedBackendExecution.groupedIncidenceEquiv n h).symm i
    let out := copy (BinaryLowHighNormalize.output values x.2 x.1)
    ⟨out.value,out.bitSteps,64*(EndToEndAPSP.incidenceSize n h).size^2+8⟩

theorem get (values : Values (n:=n) (h:=h)) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    view ((execute values).value.get i)=
      let x := (FoldedBackendExecution.groupedIncidenceEquiv n h).symm i
      view (BinaryLowHighNormalize.output values x.2 x.1) := by
  simp only [execute,tabulate_get,copy_view]

theorem semantic (input : BinaryFoldedFormation.Inputs n) (values : Values (n:=n) (h:=h))
    (hv : ∀ j b,view (BinaryLowHighNormalize.output values j b)=FoldedRequestBounds.count f b input j)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    view ((execute values).value.get i)=
      let x := (EndToEndAPSP.incidenceEquiv n h).symm i
      FoldedBackendExecution.semanticCoefficient f x.2.1 (BinaryFoldedFormation.viewTable input.left)
        (BinaryFoldedFormation.viewTable input.right) (BinaryFoldedFormation.viewTable input.target) x.1.1 x.1.2 x.2.2 := by
  rw [get]
  dsimp only
  rw [hv]
  let x := (FoldedBackendExecution.groupedIncidenceEquiv n h).symm i
  have he : (FoldedBackendExecution.groupedIncidenceEquiv n h) x=i := Equiv.apply_symm_apply _ _
  rw [←he,FoldedBackendExecution.groupedIncidenceEquiv_decode,Equiv.symm_apply_apply]
  rfl

theorem modCount (hh : 0<h) (input : BinaryFoldedFormation.Inputs n) (values : Values (n:=n) (h:=h))
    (hv : ∀ j b,view (BinaryLowHighNormalize.output values j b)=FoldedRequestBounds.count f b input j)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    (view ((execute values).value.get i)).toNat=
      (EndToEndAPSP.flatInstance (h:=h) (BinaryFoldedFormation.viewTable input.left)
        (BinaryFoldedFormation.viewTable input.right) (BinaryFoldedFormation.viewTable input.target)).modCount r i := by
  rw [semantic f input values hv]
  dsimp only
  rw [←FoldedBackendExecution.physicalTable_semantic CompleteAPSP.naiveBackend,
    CompactBlocks.physicalTable_correct hh]
  simp only [EndToEndAPSP.flatInstance,CompositeCertification.Instance.modCount,
    CompleteAPSP.incidenceInstance,Finset.card_filter]
  rfl

theorem nonnegative (input : BinaryFoldedFormation.Inputs n) (values : Values (n:=n) (h:=h))
    (hv : ∀ j b,view (BinaryLowHighNormalize.output values j b)=FoldedRequestBounds.count f b input j)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) : 0≤view ((execute values).value.get i) := by
  rw [get]
  dsimp only
  rw [hv]
  exact FoldedRequestBounds.count_nonnegative f _ input _

theorem bound (input : BinaryFoldedFormation.Inputs n) (values : Values (n:=n) (h:=h))
    (hv : ∀ j b,view (BinaryLowHighNormalize.output values j b)=FoldedRequestBounds.count f b input j)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) : (view ((execute values).value.get i)).natAbs≤h := by
  rw [get]
  dsimp only
  rw [hv]
  exact FoldedRequestBounds.count_bound f _ input _

theorem bits (values : Values (n:=n) (h:=h))
    (hv : ∀ j b,(view (BinaryLowHighNormalize.output values j b)).natAbs≤h) :
    (execute values).bitSteps≤EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size := by
  apply tabulate_bits
  intro i
  exact copy_price h.size _ (Nat.size_le_size (hv _ _))

theorem control (values : Values (n:=n) (h:=h)) :
    (execute values).control≤EndToEndAPSP.incidenceSize n h*
      (64*(EndToEndAPSP.incidenceSize n h).size^2+40)+8 := by
  exact tabulate_control _ _ (fun _=>le_refl _)

#print axioms get
#print axioms semantic
#print axioms modCount
#print axioms nonnegative
#print axioms bound
#print axioms bits
#print axioms control
end ThinMatrix.GraphSelectedIncidences
