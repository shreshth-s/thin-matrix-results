import GraphOwnLowProgram
import GraphOwnBandTargets

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 2200000

/-! Concrete LOW production over retained diagonal sources and shared target
routers. Both normal/opposite masks are selected by each own-band collection;
the inert seed masks merely complete the common root-index record. -/
namespace ThinMatrix.GraphOwnLowProduction
open BinaryCell BinaryGroupedCoordinates GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

def seed : Fin (goodSlots p.L p.m).card :=
  ⟨0,by
    have ha := goodSlots_density p.L p.m
    have hb := Nat.choose_pos p.m_le_L
    omega⟩

def index (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (c : Fin (channelCount p.m p.t)) (right : Bool) : GraphAdaptiveRootBatch.Index f p :=
  ⟨u,v,run,seed f p,seed f p,c,right⟩

theorem dimension_pos (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (c : Fin (channelCount p.m p.t)) (right : Bool) :
    0<GraphAdaptiveRootBatch.D f p (index f p u v run c right) := CappedSubsetList.count_pos _ _

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (hb : ∀ i,((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandL<S ∧
    ((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandR<S)
  (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
  (stored : GraphOwnBandPreparation.Stores f p (S:=S))
  (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a))

omit hb in
def roots (targets : GraphOwnBandTargets.Prepared f p (S:=S)) : GraphOwnLowProgram.RootFamily f p :=
  fun u v run c side => GraphOwnBandTargets.execute f p input hm
    (index f p u v run c side) scheme hnum hden hz (dimension_pos f p u v run c side) stored hc targets

omit hb in
def execute (targets : GraphOwnBandTargets.Prepared f p (S:=S))
    (channels : Vector (Channel p.m) (channelCount p.m p.t)) (ws : Vector Cell p.t) :=
  GraphOwnLowProgram.execute f p ws channels targets.requests
    (roots f p hm input scheme hnum hden hz stored hc targets)

attribute [local irreducible] GraphAdaptiveBatchSources.Correct GraphPrefixProgram.fromInputs

theorem root_correct (hv : scheme.Valid) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (c : Fin (channelCount p.m p.t)) (side : Bool)
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) (block : Fin (CompactBlocks.blockCount n h))
    (col : Fin ((p.m+1)*f.cyclic)) :
    view ((((roots f p hm input scheme hnum hden hz stored hc
      (GraphOwnBandTargets.prepare f p input hb).value) u v run c side).value.get j).get (PrefixBlockBatch.column block col))=
      GraphOwnRootSpec.rootValue f p input u v run c side j block col :=
  GraphOwnBandTargets.correct f p input hb hm (index f p u v run c side) scheme hnum hden hz
    (dimension_pos f p u v run c side) stored hc hv j block col

theorem correct (hv : scheme.Valid)
    (channels : Vector (Channel p.m) (channelCount p.m p.t))
    (hchannels : channels=(GraphSharedTargets.keys f p).value.channels)
    (ws : Vector Cell p.t)
    (hw : ∀ d,view (ws.get d)=(TensorContraction.residualWeight (2*p.m) p.t d.val : ℤ))
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) (block : Fin (CompactBlocks.blockCount n h)) :
    view ((RootProductCollection.output
      (execute f p hm input scheme hnum hden hz stored hc
        (GraphOwnBandTargets.prepare f p input hb).value channels ws).value j).get block)=
      GraphSelectedNormalize.lowValue f p input j block := by
  exact GraphOwnLowProgram.correct f p ws channels _ _ input hw hchannels
    (GraphOwnBandTargets.requests_eq f p input hb)
    (root_correct f p hm input hb scheme hnum hden hz stored hc hv) j block

#print axioms dimension_pos
#print axioms root_correct
#print axioms correct
end ThinMatrix.GraphOwnLowProduction
