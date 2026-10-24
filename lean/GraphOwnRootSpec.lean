import GraphSelectedRootProduct
import GraphRootBandValue
import GraphOwnBandRouter

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1800000

/-! Canonical per-occurrence root specifications for the shared LOW schedule.
The source band is selected separately on each side, and the full original
request ID is retained for the later selected-coefficient product. -/
namespace ThinMatrix.GraphOwnRootSpec
open BinaryCell BinaryGroupedCoordinates GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

def physical (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :=
  (GraphSharedTargets.prepare f p target).physical.value.get request

def index (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (channel : Fin (channelCount p.m p.t)) (right : Bool)
    (q : GraphCompletionRequests.Physical p.L p.m f.cyclic) : GraphRootCompletion.Index p.L p.m p.t :=
  ⟨u,v,run,(RootRequestSelection.ranks right q).1,(RootRequestSelection.ranks right q).2,channel,right⟩

def pairIndex (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (channel : Fin (channelCount p.m p.t))
    (q : GraphCompletionRequests.Physical p.L p.m f.cyclic) : GraphRootProducts.Index p.L p.m p.t :=
  ⟨u,v,run,RootRequestSelection.rowRank q.row,RootRequestSelection.rowRank q.column,channel⟩

def transposed (channel : Fin (channelCount p.m p.t)) : Run (Fin (channelCount p.m p.t)) :=
  ResidualChannelTranspose.locate (GraphSharedTargets.keys f p).value.channels channel

def graph (input : BinaryFoldedFormation.Inputs n) (block : Fin (CompactBlocks.blockCount n h))
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :=
  let q := physical f p input.target request
  GraphPrefixProgram.fromInputs f p block input q.bandL q.bandR 0

def rootValue (input : BinaryFoldedFormation.Inputs n) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (channel : Fin (channelCount p.m p.t)) (right : Bool)
    (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) : ℤ :=
  let q := physical f p input.target request
  let own := GraphOwnBandRouter.ownBand right q
  view (((GraphRootCompletion.fromInputs f p block input own own 0
    (index f p u v run channel right q)).completed.value.sums.value.get request).output.get c)

theorem rootValue_eq (input : BinaryFoldedFormation.Inputs n) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (channel : Fin (channelCount p.m p.t)) (right : Bool)
    (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) :
    rootValue f p input u v run channel right request block c=
      view (((GraphRootCompletion.execute (graph f p input block request)
        (index f p u v run channel right (physical f p input.target request)) input.target).completed.value.sums.value.get request).output.get c) := by
  apply GraphRootBandValue.output_eq
  cases right <;> rfl

theorem left_index (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (channel : Fin (channelCount p.m p.t)) (q : GraphCompletionRequests.Physical p.L p.m f.cyclic) :
    (pairIndex f p u v run channel q).leftIndex=index f p u v run channel false q := rfl

theorem right_index (input : BinaryFoldedFormation.Inputs n) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (channel : Fin (channelCount p.m p.t)) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) :
    (GraphRootProducts.transpose (graph f p input block request)
      (pairIndex f p u v run channel (physical f p input.target request))).value=
      index f p u v run (transposed f p channel).value true (physical f p input.target request) := rfl

theorem accepts (input : BinaryFoldedFormation.Inputs n) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (channel : Fin (channelCount p.m p.t)) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) :
    GraphRootProducts.accepted (graph f p input block request)
      (pairIndex f p u v run channel (physical f p input.target request)).leftIndex input.target
      (physical f p input.target request).bandL (physical f p input.target request).bandR request=true := by
  change RootRequestSelection.accepts _ _ false _ _ (physical f p input.target request)=true
  simp only [pairIndex,GraphRootProducts.Index.leftIndex,RootRequestSelection.accepts,RootRequestSelection.ranks,Bool.false_eq_true,ite_false,
    and_self,decide_true]

#print axioms rootValue_eq
#print axioms left_index
#print axioms right_index
#print axioms accepts
end ThinMatrix.GraphOwnRootSpec
