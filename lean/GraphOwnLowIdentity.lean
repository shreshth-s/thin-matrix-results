import GraphOwnRootSpec
import LowRequestLocator

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1800000

/-! Selecting the two own masks for an original occurrence removes the
exhaustive good-mask sums without changing the LOW numerator. All strict
channels, degree runs, and both translation-list indices remain summed. -/
namespace ThinMatrix.GraphOwnLowIdentity
open BinaryCell GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

theorem physical (input : BinaryFoldedFormation.Inputs n)
    (block : Fin (CompactBlocks.blockCount n h)) (j : Fin (FoldedBackendExecution.windowQuerySize n)) :
    LowRequestLocator.physical (GraphOwnRootSpec.graph f p input block j) input.target j=
      GraphOwnRootSpec.physical f p input.target j := rfl

attribute [local irreducible] GraphPrefixProgram.fromInputs

theorem channels (input : BinaryFoldedFormation.Inputs n) (u v : Fin (J p.m))
    (run : Fin (2*p.m+1)) (block : Fin (CompactBlocks.blockCount n h))
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) :
    (∑ c : Fin (channelCount p.m p.t),
      GraphWeightedRootProducts.sourceValue (GraphOwnRootSpec.graph f p input block j)
        (GraphOwnRootSpec.pairIndex f p u v run c (GraphOwnRootSpec.physical f p input.target j))
        input.target (GraphOwnRootSpec.physical f p input.target j).bandL
        (GraphOwnRootSpec.physical f p input.target j).bandR j
        (GraphOwnRootSpec.physical f p input.target j).coefficient)=
      LowRequestLocator.runValue (GraphOwnRootSpec.graph f p input block j) u v run
        (RootRequestSelection.rowRank (GraphOwnRootSpec.physical f p input.target j).row)
        (RootRequestSelection.rowRank (GraphOwnRootSpec.physical f p input.target j).column)
        input.target j (GraphOwnRootSpec.physical f p input.target j).coefficient := by
  simp only [GraphOwnRootSpec.graph,GraphOwnRootSpec.pairIndex]
  rw [GraphShiftedLow.channel_sum f p block input _ _ 0 u v run _ _ j _]
  change (if RootRequestSelection.accepts _ _ false _ _
    (LowRequestLocator.physical (GraphOwnRootSpec.graph f p input block j) input.target j)
      then _ else 0)=_
  rw [physical]
  simp only [RootRequestSelection.accepts,RootRequestSelection.ranks,Bool.false_eq_true,ite_false,and_self,decide_true,ite_true]
  rfl

theorem family (input : BinaryFoldedFormation.Inputs n) (block : Fin (CompactBlocks.blockCount n h))
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) :
    (∑ u : Fin (J p.m), ∑ v : Fin (J p.m), ∑ run : Fin (2*p.m+1),
      ∑ c : Fin (channelCount p.m p.t),
        GraphWeightedRootProducts.sourceValue (GraphOwnRootSpec.graph f p input block j)
          (GraphOwnRootSpec.pairIndex f p u v run c (GraphOwnRootSpec.physical f p input.target j))
          input.target (GraphOwnRootSpec.physical f p input.target j).bandL
          (GraphOwnRootSpec.physical f p input.target j).bandR j
          (GraphOwnRootSpec.physical f p input.target j).coefficient)=
      LowRequestLocator.value (GraphOwnRootSpec.graph f p input block j) input.target
        (GraphOwnRootSpec.physical f p input.target j).bandL
        (GraphOwnRootSpec.physical f p input.target j).bandR j
        (GraphOwnRootSpec.physical f p input.target j).coefficient := by
  simp_rw [channels f p input]
  unfold LowRequestLocator.value
  rw [physical f p input block j]
  simp only [and_self,ite_true]

#print axioms physical
#print axioms channels
#print axioms family
end ThinMatrix.GraphOwnLowIdentity
