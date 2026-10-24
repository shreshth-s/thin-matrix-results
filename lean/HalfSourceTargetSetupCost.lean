import GraphHalfSourceSetup
import BackendCostRefinement
import HalfSourceRootSetupCost
import HalfSourceEmptyRootCost

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceTargetSetupCost
open BinaryCell SourceFormation
open scoped BigOperators

/-- Uniform per-cell input width, rather than the sum of all target widths. -/
theorem formation {n h r W V : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (target : BinaryFoldedFormation.BinaryTable n)
    (hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic 0 V)
    (ht : ∀ i j,(view ((target.get i).get j)).natAbs.size≤W) :
    (GraphSharedTargets.prepare f p target).folded.geometry.bitSteps+
      (GraphSharedTargets.prepare f p target).folded.requests.bitSteps≤
        10000*(V+1)^2+2000000*FoldedBackendExecution.windowQuerySize n*(W+V+10)^2 := by
  have hr := BinaryFoldedTargets.requests_cost f
    (BinaryFoldedFactory.prepareRequests f p target).geometry.value target
    ⟨hb.n_size,hb.d_size,hb.q_size,hb.width_size⟩ ht
  have hg := BinaryFoldedFormationCost.makeGeometry_cost hb
  apply Nat.add_le_add _ hr
  simpa only [GraphSharedTargets.prepare,GraphCompletionRequests.prepare,
    BinaryFoldedFactory.prepareRequests,BinaryFoldedFormation.makeGeometryCached_refines] using hg

def routerBudget (S L m M : ℕ) : ℕ :=
  let G := GraphOwnBandRouter.count S L m
  24*(G+1)+M*(16*(G.size+1)^2+64*(G.size+1)^3+128*(G.size+L+m+1)^3+36)+36

def targetBudget (S L m t M W V : ℕ) : ℕ :=
  50000*(L+m+1)^6*12^L*2^(L-m)+
    ResidualFamilyKeys.prepareBudget L m t (GoodMapEmbedding.goodSlots L m).card+
    10000*(V+1)^2+2000000*M*(W+V+10)^2+
    M*(1000*(L+m+1)^5+32)+8+2*routerBudget S L m M+32

theorem targets {n h r S W V : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (input : BinaryFoldedFormation.Inputs n)
    (hb : ∀ i,((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandL<S ∧
      ((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandR<S)
    (hm : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic 0 V)
    (ht : ∀ i j,(view ((input.target.get i).get j)).natAbs.size≤W) :
    (GraphOwnBandTargets.prepare f p input hb).operations≤
      targetBudget S p.L p.m p.t (FoldedBackendExecution.windowQuerySize n) W V := by
  have hs := BackendCostRefinement.BandShapeCosts.prepareShape_polynomial p.L p.m 1 p.m_le_L (by decide)
  have hk := ResidualFamilyKeys.prepare_control (GraphSharedTargets.shape f p).layout p.t
  have hf := formation f p input.target hm ht
  have hp := GraphCompletionRequests.prepare_control f p (GraphSharedTargets.shape f p) input.target
  have hl := GraphOwnBandRouter.cost false (GraphSharedTargets.prepare f p input.target).physical.value hb
  have hr := GraphOwnBandRouter.cost true (GraphSharedTargets.prepare f p input.target).physical.value hb
  have hz : (GraphSharedTargets.prepare f p input.target).physical.bitSteps=0 :=
    GraphCompletionRequests.prepare_bits f p (GraphSharedTargets.shape f p) input.target
  rw [GraphOwnBandTargets.work,hl.1,hr.1,hz]
  simp only [GraphSharedTargets.keys,ResidualFamilyKeys.prepare_bits,Nat.add_zero]
  change (GraphSharedTargets.shape f p).operations≤_ at hs
  simp only [Nat.mul_one] at hs
  change (GraphSharedTargets.prepare f p input.target).physical.control≤_ at hp
  unfold targetBudget routerBudget
  dsimp only
  omega

def extraBudget (S B L m t M W V : ℕ) : ℕ :=
  48*S*B+8*S+8*B+targetBudget S L m t M W V+
    50000*(L+m+1)^6*12^L*2^(L-m)+
    ResidualFamilyKeys.prepareBudget L m t (GoodMapEmbedding.goodSlots L m).card+
    t*WeightedRootProducts.weightBudget (2*m) t+
    (t*(WeightedRootProducts.weightBudget (2*m) t+48)+8+3*t+4)+64

theorem execute {n h r W V : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m≤p.L-p.m)
    (input : BinaryFoldedFormation.Inputs n)
    (hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic 0 V)
    (ht : ∀ i j,(view ((input.target.get i).get j)).natAbs.size≤W) :
    (GraphHalfSourceSetup.execute f p hm input).operations≤
      (GraphSharedSourceProduction.execute f p hm input (S:=GraphHalfSourceSetup.S f p)).operations+
      extraBudget (GraphHalfSourceSetup.S f p) (CompactBlocks.blockCount n h) p.L p.m p.t
        (FoldedBackendExecution.windowQuerySize n) W V := by
  have htarget := targets f p input (GraphHalfSourceSetup.bands_bound f p input.target) hb ht
  have hs := BackendCostRefinement.BandShapeCosts.prepareShape_polynomial p.L p.m 1 p.m_le_L (by decide)
  have hk := ResidualFamilyKeys.prepare_control (GraphSharedTargets.shape f p).layout p.t
  have hw := WeightedRootProducts.weights_bits (2*p.m) p.t
  have hwc := WeightedRootProducts.weights_control (2*p.m) p.t
  have hhigh : (vectorBuild (CompactBlocks.blockCount n h)
      (GraphSharedSourceProduction.high f p (GraphSharedSourceProduction.execute f p hm input
        (S:=GraphHalfSourceSetup.S f p)).value)).operations=
        CompactBlocks.blockCount n h*(24*GraphHalfSourceSetup.S f p+8) := by
    simp only [vectorBuild,GraphSharedSourceProduction.high_work,Vector.get_ofFn,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  change (GraphSharedTargets.shape f p).operations≤_ at hs
  simp only [Nat.mul_one] at hs
  simp only [GraphHalfSourceSetup.execute,GraphSharedSourceProduction.low_work,hhigh,
    ResidualFamilyKeys.prepare_bits,Nat.add_zero]
  unfold extraBudget
  nlinarith only [htarget,hs,hk,hw,hwc]

#print axioms formation
#print axioms targets
#print axioms execute
end ThinMatrix.HalfSourceTargetSetupCost
