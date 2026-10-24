import GraphOwnBandCollection
import GraphOwnRootSpec

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 7000

namespace ThinMatrix.GraphOwnBandCanonical
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (base : Index f p) (input : BinaryFoldedFormation.Inputs n)
  (requests : GraphOwnBandCompletion.Requests f p)

attribute [local irreducible] GraphRootCompletion.fromInputs GraphPrefixProgram.fromInputs

/-- Adaptive own-band rows have the canonical length-zero root specification. -/
theorem expected_eq
    (hreq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
    (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) :
    GraphOwnBandCollection.expected f p base requests input request (PrefixBlockBatch.column block c)=
      GraphOwnRootSpec.rootValue f p input base.u base.v base.run base.channel base.right request block c := by
  subst requests
  simp only [GraphOwnBandCollection.expected,PrefixBlockBatch.column,
    finProdFinEquiv.symm_apply_apply, GraphOwnRootSpec.rootValue, GraphOwnRootSpec.physical, GraphOwnBandCollection.requestIndex, GraphOwnRootSpec.index]
  rw [Equiv.symm_apply_apply]
  exact GraphRootInvariance.length_independent f p input _ _ _ _ _ _ _ _

#print axioms expected_eq
end ThinMatrix.GraphOwnBandCanonical
