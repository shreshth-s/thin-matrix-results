import GraphRootInvariance
import GraphBandSharing

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1400000

/-! A completed oriented root depends on its own input band only. Its physical
projection still uses the original target coordinates and original masks.
This permits gathering all opposite-band requests in one shared completion. -/
namespace ThinMatrix.GraphRootBandValue
open BinaryCell GraphAdaptiveRootBatch
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

theorem root_eq (input : BinaryFoldedFormation.Inputs n) (a b a' b' ell ell' : ℕ)
    (i : Index f p) (block : Fin (CompactBlocks.blockCount n h))
    (hs : if i.right then b=b' else a=a') :
    GraphRootCompletion.root (GraphPrefixProgram.fromInputs f p block input a b ell) i=
      GraphRootCompletion.root (GraphPrefixProgram.fromInputs f p block input a' b' ell') i := by
  simp only [GraphRootCompletion.root,GraphPrefixProgram.fromInputs,
    GraphWindowPermutations.fromInputs,GraphWindowTransforms.fromInputs,GraphRootWindows.fromInputs]
  cases hi : i.right
  · have ha : a=a' := by simpa only [hi,Bool.false_eq_true,ite_false] using hs
    subst a'
    simp only [GraphPrefixCompletion.side,Bool.false_eq_true,ite_false]
    rw [GraphBandSharing.roots_left_independent f p block input a b b' i.u i.v i.run]
  · have hb : b=b' := by simpa only [hi,ite_true] using hs
    subst b'
    simp only [GraphPrefixCompletion.side,ite_true]
    rw [GraphBandSharing.roots_right_independent f p block input a a' b i.u i.v i.run]

private theorem get_eq_of_array_eq {V : Type} {xs ys : Array V} (he : xs=ys)
    (j : ℕ) (hx : j<xs.size) (hy : j<ys.size) : xs[j]=ys[j] := by
  cases he
  rfl

theorem output_eq (input : BinaryFoldedFormation.Inputs n) (a b a' b' ell ell' : ℕ)
    (i : Index f p) (block : Fin (CompactBlocks.blockCount n h))
    (hs : if i.right then b=b' else a=a')
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (c : Fin ((p.m+1)*f.cyclic)) :
    view (((GraphRootCompletion.fromInputs f p block input a b ell i).completed.value.sums.value.get request).output.get c)=
      view (((GraphRootCompletion.fromInputs f p block input a' b' ell' i).completed.value.sums.value.get request).output.get c) := by
  obtain ⟨⟨d,residue⟩,rfl⟩ := finProdFinEquiv.surjective c
  rw [GraphRootCompletion.fromInputs_contraction f p block input a b ell i request d residue,
    GraphRootCompletion.fromInputs_contraction f p block input a' b' ell' i request d residue]
  have hl : (GraphRootCompletion.fromInputs f p block input a b ell i).residuals.value.labels[request.val]'(by simp [GraphRootCompletion.fromInputs])=
      (GraphRootCompletion.fromInputs f p block input a' b' ell' i).residuals.value.labels[request.val]'(by simp [GraphRootCompletion.fromInputs]) := by
    apply get_eq_of_array_eq
    exact congrArg (fun x : BinaryGroupedCoordinates.Run (GraphCompletionRequests.Residuals p.L p.m) => x.value.labels)
      ((GraphSharedTargets.legacy_residuals f p block input a b ell i).trans
        (GraphSharedTargets.legacy_residuals f p block input a' b' ell' i).symm)
  rw [hl,root_eq f p input a b a' b' ell ell' i block hs]

#print axioms root_eq
#print axioms output_eq
end ThinMatrix.GraphRootBandValue
