import GraphAdaptiveLegacy
import GraphOwnResiduals

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1400000

/-! Physical target geometry and original-coordinate projection masks depend
only on the public graph shape and target, not on a middle block, band pair,
channel or adaptive prefix length. Callers retain this preparation once. -/
namespace ThinMatrix.GraphSharedTargets
open BinaryGroupedCoordinates
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

def shape := BinaryBackendExecution.prepareShapeRuntime p.L p.m
def keys := ResidualFamilyKeys.prepare (shape f p).layout p.t

def prepare (target : BinaryFoldedFormation.BinaryTable n) :=
  GraphCompletionRequests.prepare f p (shape f p) target

def project (target : BinaryFoldedFormation.BinaryTable n) (i : GraphRootCompletion.Index p.L p.m p.t) :=
  GraphCompletionRequests.project i.right ((keys f p).value.masks.get i.normal)
    ((keys f p).value.masks.get i.opposite) (prepare f p target).physical.value

theorem source_shape (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (a b : ℕ) : (GraphResidualFamilies.fromInputs f p block input a b).source.shape=shape f p := rfl

theorem source_keys (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (a b : ℕ) : (GraphResidualFamilies.fromInputs f p block input a b).keys=keys f p := rfl

theorem legacy_targets (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (a b ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) :
    (GraphRootCompletion.fromInputs f p block input a b ell i).targets=prepare f p input.target := rfl

theorem legacy_residuals (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (a b ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) :
    (GraphRootCompletion.fromInputs f p block input a b ell i).residuals=project f p input.target i := rfl

@[simp] theorem project_size (target : BinaryFoldedFormation.BinaryTable n) (i : GraphRootCompletion.Index p.L p.m p.t) :
    (project f p target i).value.labels.size=FoldedBackendExecution.windowQuerySize n := by
  simp only [project,GraphCompletionRequests.project_size]

theorem prefix_residuals (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (a b ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) (s : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    (GraphPrefixCompletion.fromInputs f p block input a b ell (i.atSlot s)).residuals=project f p input.target i := rfl

#print axioms source_shape
#print axioms source_keys
#print axioms legacy_targets
#print axioms legacy_residuals
#print axioms project_size
#print axioms prefix_residuals
end ThinMatrix.GraphSharedTargets
