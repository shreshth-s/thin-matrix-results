import GraphOwnRootProduct
import GraphOwnLowCollection
import GraphSelectedNormalize

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1800000

/-! Pair independently routed left/right root completions by their original
request IDs, use the actual transposed channel locator once, and accumulate
the complete selected LOW numerator. Source banks/target geometry/weights are
retained inputs; both oriented child executions and every join are charged. -/
namespace ThinMatrix.GraphOwnLowProgram
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
abbrev RootFamily := Fin (J p.m) → Fin (J p.m) → Fin (2*p.m+1) →
  Fin (channelCount p.m p.t) → Bool → Run (GraphOwnRootProduct.Rows f p)

variable (ws : Vector Cell p.t) (channels : Vector (Channel p.m) (channelCount p.m p.t))
  (requests : GraphOwnRootProduct.Requests f p) (roots : RootFamily f p)

def channel (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t)) :
    Run (GraphOwnLowCollection.Rows (n:=n) (h:=h)) :=
  let left := roots u v run c false
  let transpose := ResidualChannelTranspose.locate channels c
  let right := roots u v run transpose.value true
  let product := GraphOwnRootProduct.execute f p ws (channels.get c) requests left.value right.value
  ⟨product.value,left.bitSteps+transpose.bitSteps+right.bitSteps+product.bitSteps,
    left.control+transpose.control+right.control+product.control+32⟩

def execute := GraphOwnLowCollection.execute f p (channel f p ws channels requests roots)

attribute [local irreducible] GraphPrefixProgram.fromInputs

variable (input : BinaryFoldedFormation.Inputs n)
  (hw : ∀ d,view (ws.get d)=(TensorContraction.residualWeight (2*p.m) p.t d.val : ℤ))
  (hc : channels=(GraphSharedTargets.keys f p).value.channels)
  (hq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
  (hr : ∀ u v run c side j block col,
    view (((roots u v run c side).value.get j).get (PrefixBlockBatch.column block col))=
      GraphOwnRootSpec.rootValue f p input u v run c side j block col)
include hw hc hq hr

theorem channel_value (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t))
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) (block : Fin (CompactBlocks.blockCount n h)) :
    view (((channel f p ws channels requests roots u v run c).value.get j).get block)=
      GraphWeightedRootProducts.sourceValue (GraphOwnRootSpec.graph f p input block j)
        (GraphOwnRootSpec.pairIndex f p u v run c (GraphOwnRootSpec.physical f p input.target j))
        input.target (GraphOwnRootSpec.physical f p input.target j).bandL
        (GraphOwnRootSpec.physical f p input.target j).bandR j
        (GraphOwnRootSpec.physical f p input.target j).coefficient := by
  change view (((GraphOwnRootProduct.execute f p ws (channels.get c) requests _ _).value.get j).get block)=_
  apply GraphOwnRootProduct.correct f p input u v run c ws hw (channels.get c) (by rw [hc]) requests hq
  · intro j block col
    exact hr u v run c false j block col
  · intro j block col
    rw [hr]
    rw [hc]
    rfl

theorem correct (j : Fin (FoldedBackendExecution.windowQuerySize n)) (block : Fin (CompactBlocks.blockCount n h)) :
    view ((RootProductCollection.output (execute f p ws channels requests roots).value j).get block)=
      GraphSelectedNormalize.lowValue f p input j block := by
  unfold execute
  rw [GraphOwnLowCollection.correct f p input _
    (channel_value f p ws channels requests roots input hw hc hq hr)]
  symm
  exact GraphLowMaskAssembly.fromInputs_value f p block input _ _ 0 j _

omit hw hc hq hr in
 theorem channel_bits (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t)) :
    (channel f p ws channels requests roots u v run c).bitSteps=
      (roots u v run c false).bitSteps+(ResidualChannelTranspose.locate channels c).bitSteps+
      (roots u v run (ResidualChannelTranspose.locate channels c).value true).bitSteps+
      (GraphOwnRootProduct.execute f p ws (channels.get c) requests
        (roots u v run c false).value (roots u v run (ResidualChannelTranspose.locate channels c).value true).value).bitSteps := rfl

omit hw hc hq hr in
 theorem channel_control (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t)) :
    (channel f p ws channels requests roots u v run c).control=
      (roots u v run c false).control+(ResidualChannelTranspose.locate channels c).control+
      (roots u v run (ResidualChannelTranspose.locate channels c).value true).control+
      (GraphOwnRootProduct.execute f p ws (channels.get c) requests
        (roots u v run c false).value (roots u v run (ResidualChannelTranspose.locate channels c).value true).value).control+32 := rfl

#print axioms channel_value
#print axioms correct
#print axioms channel_bits
#print axioms channel_control
end ThinMatrix.GraphOwnLowProgram
