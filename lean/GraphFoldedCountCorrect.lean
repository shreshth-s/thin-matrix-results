import GraphBlockSchedule

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

/-! Exact original modular counts from the new retained LOW/HIGH program,
including band scheduling and requested-coefficient collection. This endpoint
has no supplied answer, no rectangular oracle, and in `finite_modCount` no
supplied valid plan. The finite fallback has no improved complexity claim. -/
namespace ThinMatrix.GraphFoldedCountCorrect
open BinaryCell BinaryFoldedFormation
variable {n h r : ℕ}

theorem original_semantic (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (input : Inputs n) (ell : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    view (GraphBlockSchedule.output f p input ell i)=
      let x := (EndToEndAPSP.incidenceEquiv n h).symm i
      FoldedBackendExecution.semanticCoefficient f x.2.1 (viewTable input.left) (viewTable input.right)
        (viewTable input.target) x.1.1 x.1.2 x.2.2 := by
  obtain ⟨⟨b,j⟩,rfl⟩ := (FoldedBackendExecution.groupedIncidenceEquiv n h).surjective i
  rw [GraphBlockSchedule.execute_value,Equiv.symm_apply_apply,FoldedBackendExecution.groupedIncidenceEquiv_decode]
  rfl

theorem modCount (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (input : Inputs n) (ell : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    (view (GraphBlockSchedule.output f p input ell i)).toNat=
      (EndToEndAPSP.flatInstance (h:=h) (viewTable input.left) (viewTable input.right)
        (viewTable input.target)).modCount r i := by
  rw [original_semantic]
  dsimp only
  rw [←FoldedBackendExecution.physicalTable_semantic CompleteAPSP.naiveBackend,
    CompactBlocks.physicalTable_correct hh]
  simp only [EndToEndAPSP.flatInstance,CompositeCertification.Instance.modCount,
    CompleteAPSP.incidenceInstance,Finset.card_filter]
  rfl

def execute (f : CompactBlocks.PhysicalFactorization r) (input : Inputs n) (h : ℕ) :=
  GraphBlockSchedule.execute f (FiniteFoldedPlan.produce n h f) input 0

def output (f : CompactBlocks.PhysicalFactorization r) (input : Inputs n) (h : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) : Cell := (execute f input h).2.2.2.value.get i

theorem finite_modCount (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r) (input : Inputs n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    (view (output f input h i)).toNat=
      (EndToEndAPSP.flatInstance (h:=h) (viewTable input.left) (viewTable input.right)
        (viewTable input.target)).modCount r i :=
  modCount hh f _ input 0 i

theorem finite_nonnegative (f : CompactBlocks.PhysicalFactorization r) (input : Inputs n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) : 0≤view (output f input h i) :=
  GraphBlockSchedule.execute_nonnegative f _ input 0 i

theorem finite_bound (f : CompactBlocks.PhysicalFactorization r) (input : Inputs n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) : (view (output f input h i)).natAbs≤h :=
  GraphBlockSchedule.execute_bound f _ input 0 i

#print axioms original_semantic
#print axioms modCount
#print axioms finite_modCount
#print axioms finite_nonnegative
#print axioms finite_bound
end ThinMatrix.GraphFoldedCountCorrect
