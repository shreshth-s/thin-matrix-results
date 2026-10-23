import GraphCompletionRequests

set_option autoImplicit false

/-! Sharpen the target-formation analysis to the largest original cell width.
This is a specification parameter, not an uncharged preprocessing scan: the
unchanged circuit does not inspect or need this bound in order to execute. -/
namespace ThinMatrix.GraphTargetWidth
open BinaryCell

noncomputable def width {n : ℕ} (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  Finset.univ.sup (fun i => Finset.univ.sup (fun j => (view ((target.get i).get j)).natAbs.size))

theorem cell_le {n : ℕ} (target : BinaryFoldedFormation.BinaryTable n) (i j : Fin n) :
    (view ((target.get i).get j)).natAbs.size≤width target :=
  (Finset.le_sup (f:=fun j => (view ((target.get i).get j)).natAbs.size) (Finset.mem_univ j)).trans
    (Finset.le_sup (f:=fun i => Finset.univ.sup (fun j => (view ((target.get i).get j)).natAbs.size)) (Finset.mem_univ i))

theorem width_le {n W : ℕ} (target : BinaryFoldedFormation.BinaryTable n)
    (h : ∀ i j, (view ((target.get i).get j)).natAbs.size≤W) : width target≤W := by
  apply Finset.sup_le
  intro i _
  apply Finset.sup_le
  intro j _
  exact h i j

@[simp] theorem width_empty (target : BinaryFoldedFormation.BinaryTable 0) : width target=0 := by
  simp [width]

theorem prepare_formation_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (target : BinaryFoldedFormation.BinaryTable n) :
    let B := GraphCompletionRequests.metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic
    (GraphCompletionRequests.prepare f p shape target).folded.geometry.bitSteps+
      (GraphCompletionRequests.prepare f p shape target).folded.requests.bitSteps≤
      10000*(B+1)^2+2000000*FoldedBackendExecution.windowQuerySize n*(width target+B+10)^2 := by
  dsimp only
  have hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic 0
      (GraphCompletionRequests.metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic) := by
    constructor <;> simp only [GraphCompletionRequests.metadataWidth,Nat.size_zero] <;> omega
  have ht : BinaryFoldedTargets.MetadataBound n (FoldedBackendExecution.physicalFold f) f.cyclic
      (GraphCompletionRequests.metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic) :=
    ⟨hb.n_size,hb.d_size,hb.q_size,hb.width_size⟩
  have hg := BinaryFoldedFormationCost.makeGeometry_cost hb
  have hr := BinaryFoldedTargets.requests_cost f (BinaryFoldedFactory.prepareRequests f p target).geometry.value target ht (cell_le target)
  apply Nat.add_le_add _ hr
  simpa only [GraphCompletionRequests.prepare,BinaryFoldedFactory.prepareRequests,BinaryFoldedFormation.makeGeometryCached_refines] using hg

#print axioms cell_le
#print axioms width_le
#print axioms width_empty
#print axioms prepare_formation_bits
end ThinMatrix.GraphTargetWidth
