import GraphBandSchedule

set_option autoImplicit false

/-! A constructed finite fallback plan, so finite count correctness need not
assume caller-supplied valid dimensions. This uses L=m and t=0, not the
optimized rounded parameters required by the improved exponent. Native
parameter arithmetic is executable but has no binary cost theorem here. -/
namespace ThinMatrix.FiniteFoldedPlan

def produce (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    BinaryFoldedFactory.Plan (n:=n) (h:=h) f where
  L := FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)
  m := FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)
  t := 0
  foldWidth := FoldedCounts.foldWidth (FoldedBackendExecution.physicalFold f)
  N := FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)
  D := FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)
  raw := FoldedBackendExecution.rawMiddle h (FoldedBackendExecution.physicalFold f)
  lowWidth := 0
  foldWidth_eq := rfl
  N_eq := rfl
  D_eq := rfl
  raw_eq := rfl
  m_le_L := le_refl _
  t_le := Nat.zero_le _
  middle_fit := le_of_eq (FoldedBackendExecution.middleSize_eq h (FoldedBackendExecution.physicalFold f))

theorem dimensions (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (produce n h f).m=(produce n h f).L ∧ (produce n h f).t=0 ∧
      (produce n h f).D=4^(produce n h f).m :=
  ⟨rfl,rfl,FoldedBackendExecution.middleSize_eq h (FoldedBackendExecution.physicalFold f)⟩

theorem band_count_value {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    BinaryCell.view (GraphBandSchedule.output f (produce n h f) block input 0 i)=FoldedRequestBounds.count f block input i :=
  GraphBandSchedule.execute_value f _ block input 0 i

#print axioms dimensions
#print axioms band_count_value
end ThinMatrix.FiniteFoldedPlan
