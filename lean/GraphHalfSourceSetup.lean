import GraphSharedSourceProduction
import GraphOwnLowProduction

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2200000

/-! Shared production setup for both optimized families. Raw/encoded sources,
targets, both LOW routers, shape, channel keys and residual weights are retained
before either family is executed. Every formation ledger is charged. -/
namespace ThinMatrix.GraphHalfSourceSetup
open BinaryCell SourceFormation ExactHalfSourcePlan
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
abbrev S := TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)
abbrev B := CompactBlocks.blockCount n h

structure Context where
  shared : GraphSharedSourceProduction.Stores f p (S:=S f p)
  low : GraphOwnBandPreparation.Stores f p (S:=S f p)
  high : Vector (GraphRetainedHigh.Sources f p (K:=S f p)) (B (n:=n) (h:=h))
  targets : GraphOwnBandTargets.Prepared f p (S:=S f p)
  shape : ThinMatrixBackend.ShapePlan p.L p.m
  keys : ResidualFamilyKeys.Prepared p.L p.m p.t
  weights : Vector Cell p.t

theorem physical_eq (target : BinaryFoldedFormation.BinaryTable n)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    (GraphSharedTargets.prepare f p target).physical.value.get i=FoldedBandTransport.physical f p target i := by
  unfold GraphSharedTargets.prepare
  rw [GraphCompletionRequests.prepare_get]
  rfl

theorem bands_bound (target : BinaryFoldedFormation.BinaryTable n)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    ((GraphSharedTargets.prepare f p target).physical.value.get i).bandL<S f p ∧
      ((GraphSharedTargets.prepare f p target).physical.value.get i).bandR<S f p := by
  rw [physical_eq]
  exact FoldedRequestBounds.bands_lt f p target i

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)

def execute : Program (Context f p) :=
  let shared := GraphSharedSourceProduction.execute f p hm input (S:=S f p)
  let low := GraphSharedSourceProduction.low f p shared.value
  let high := vectorBuild (B (n:=n) (h:=h)) (GraphSharedSourceProduction.high f p shared.value)
  let targets := GraphOwnBandTargets.prepare f p input (bands_bound f p input.target)
  let shape := GraphSharedTargets.shape f p
  let keys := ResidualFamilyKeys.prepare shape.layout p.t
  let weights := WeightedRootProducts.weights (2*p.m) p.t
  ⟨⟨shared.value,low.value,high.value,targets.value,shape,keys.value,weights.value⟩,
    shared.operations+low.operations+high.operations+targets.operations+shape.operations+
      keys.bitSteps+keys.control+weights.bitSteps+weights.control+64⟩

theorem low_correct (a : Fin (S f p)) :
    GraphAdaptiveBatchSources.Correct f p hm input a.val a.val ((execute f p hm input).value.low.get a) :=
  GraphSharedSourceProduction.low_correct f p hm input a

theorem high_correct (b : Fin (B (n:=n) (h:=h))) :
    GraphRetainedHigh.Correct f p b input (Vector.ofFn (fun a : Fin (S f p)=>a.val))
      ((execute f p hm input).value.high.get b) := by
  simp only [execute,vectorBuild_get]
  exact GraphSharedSourceProduction.high_correct f p hm input b

theorem targets_eq : (execute f p hm input).value.targets=
    (GraphOwnBandTargets.prepare f p input (bands_bound f p input.target)).value := rfl

theorem shape_eq : (execute f p hm input).value.shape=GraphSharedTargets.shape f p := rfl

theorem channels_eq : (execute f p hm input).value.keys.channels=(GraphSharedTargets.keys f p).value.channels := rfl

theorem weights_eq (d : Fin p.t) : view ((execute f p hm input).value.weights.get d)=
    (TensorContraction.residualWeight (2*p.m) p.t d.val : ℤ) := WeightedRootProducts.weights_get _ _ _

theorem requests_eq : (execute f p hm input).value.targets.requests=
    (GraphSharedTargets.prepare f p input.target).physical.value := rfl

theorem requests_bound (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    ((execute f p hm input).value.targets.requests.get i).bandL<S f p ∧
      ((execute f p hm input).value.targets.requests.get i).bandR<S f p :=
  bands_bound f p input.target i

#print axioms physical_eq
#print axioms bands_bound
#print axioms low_correct
#print axioms high_correct
#print axioms targets_eq
#print axioms shape_eq
#print axioms channels_eq
#print axioms weights_eq
#print axioms requests_eq
#print axioms requests_bound
end ThinMatrix.GraphHalfSourceSetup
