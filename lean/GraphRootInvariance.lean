import GraphAdaptiveRootCorrect

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 500000
namespace ThinMatrix.GraphRootInvariance
open BinaryCell GraphAdaptiveRootBatch
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

/-- The retained root and projection do not depend on the completion length. -/
theorem root_length_independent (input : BinaryFoldedFormation.Inputs n) (a b ell ell' : ℕ)
    (i : Index f p) (block : Fin (CompactBlocks.blockCount n h)) :
    GraphRootCompletion.root (GraphPrefixProgram.fromInputs f p block input a b ell) i=
      GraphRootCompletion.root (GraphPrefixProgram.fromInputs f p block input a b ell') i := by
  simp only [GraphRootCompletion.root,GraphPrefixProgram.fromInputs,
    GraphWindowPermutations.fromInputs,GraphWindowTransforms.fromInputs,GraphRootWindows.fromInputs]

private theorem get_eq_of_array_eq {V : Type} {xs ys : Array V} (he : xs=ys)
    (j : ℕ) (hx : j<xs.size) (hy : j<ys.size) : xs[j]=ys[j] := by
  cases he
  rfl

theorem length_independent (input : BinaryFoldedFormation.Inputs n) (a b ell ell' : ℕ)
    (i : Index f p) (block : Fin (CompactBlocks.blockCount n h))
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (c : Fin ((p.m+1)*f.cyclic)) :
    view (((GraphRootCompletion.fromInputs f p block input a b ell i).completed.value.sums.value.get request).output.get c)=
      view (((GraphRootCompletion.fromInputs f p block input a b ell' i).completed.value.sums.value.get request).output.get c) := by
  obtain ⟨⟨d,residue⟩,rfl⟩ := finProdFinEquiv.surjective c
  rw [GraphRootCompletion.fromInputs_contraction f p block input a b ell i request d residue,
    GraphRootCompletion.fromInputs_contraction f p block input a b ell' i request d residue]
  have hl : (GraphRootCompletion.fromInputs f p block input a b ell i).residuals.value.labels[request.val]'(by simp [GraphRootCompletion.fromInputs])=
      (GraphRootCompletion.fromInputs f p block input a b ell' i).residuals.value.labels[request.val]'(by simp [GraphRootCompletion.fromInputs]) := by
    apply get_eq_of_array_eq
    exact congrArg (fun x : BinaryGroupedCoordinates.Run (GraphCompletionRequests.Residuals p.L p.m) => x.value.labels)
      ((GraphSharedTargets.legacy_residuals f p block input a b ell i).trans
        (GraphSharedTargets.legacy_residuals f p block input a b ell' i).symm)
  rw [hl,root_length_independent f p input a b ell ell' i block]

#print axioms root_length_independent
#print axioms length_independent

end ThinMatrix.GraphRootInvariance
