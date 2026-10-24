import HalfSourceInputMetadata
import HalfSourceLowRoundedRate
import HalfSourceHighScheduleCost
import GraphHalfSourceOutputCost

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourcePublicWidths
open HalfSourceBatchFit HalfSourceAddressGeometry HalfSourceInputMetadata HalfSourcePublicFit
noncomputable section
attribute [local irreducible] shapeConstant metadataCoefficient HalfSourceDispatch.prepare

 def coefficient (scheme : RectangularBatch.Scheme) (κ : ℕ) :=
  scheme.q.size+20*shapeConstant+κ+metadataCoefficient+100
 def bound (scheme : RectangularBatch.Scheme) (n κ : ℕ) := coefficient scheme κ*(n.size+1)

 theorem fields (n : ℕ) (call : Call n) (hn : 3≤ n) (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    let f:=out.split.plan
    let p:=out.plan.value
    p.L≤ shapeConstant*n.size ∧ p.m≤ shapeConstant*n.size ∧ p.t≤ 2*shapeConstant*n.size ∧
    f.cyclic.size≤ shapeConstant*n.size ∧ p.N.size≤ shapeConstant*n.size ∧
    (bands f p).size≤ shapeConstant*n.size ∧
    (GraphOwnBandRouter.count (bands f p) p.L p.m).size≤ 3*shapeConstant*n.size+2 := by
  intro out f p
  have hw := shape_width n call hn hv
  change GraphOwnBandShapeBounds.width f p≤ shapeConstant*n.size at hw
  unfold GraphOwnBandShapeBounds.width at hw
  have hL : p.L≤ shapeConstant*n.size := by omega
  have hm : p.m≤ shapeConstant*n.size := by omega
  have ht := p.t_le
  have hq : f.cyclic.size≤ shapeConstant*n.size := by omega
  have hN : p.N.size≤ shapeConstant*n.size := by omega
  have hS : bands f p≤ p.N := (ceilDiv_le_iff_le_mul (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L)).mpr
    (Nat.le_mul_of_pos_left _ (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L))
  have hSs := (Nat.size_le_size hS).trans hN
  have hg := (HalfSourceActualVolumes.good_count p.L p.m).trans (Nat.choose_le_two_pow p.L p.m)
  have hgs := (Nat.size_le_size hg).trans_eq Nat.size_pow
  have hmul:=ParameterExecution.size_mul (bands f p) ((GoodMapEmbedding.goodSlots p.L p.m).card*(GoodMapEmbedding.goodSlots p.L p.m).card)
  have hsq:=ParameterExecution.size_mul (GoodMapEmbedding.goodSlots p.L p.m).card (GoodMapEmbedding.goodSlots p.L p.m).card
  refine ⟨hL,hm,by nlinarith only [ht,hm],hq,hN,hSs,?_⟩
  unfold GraphOwnBandRouter.count
  nlinarith only [hmul,hsq,hgs,hSs,hL]

 theorem widths (scheme : RectangularBatch.Scheme) (n κ : ℕ) (call : Call n) (hn : 3≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    let f:=out.split.plan
    let p:=out.plan.value
    inputWidth n κ+metadataWidth n+p.m+20≤ bound scheme n κ ∧
    HalfSourceLowRoundedRate.width f p (scheme.q.size+3*GraphOwnBandShapeBounds.width f p+30)≤ bound scheme n κ ∧
    p.L+p.m+p.t+inputWidth n κ+metadataWidth n+
      (GraphOwnBandRouter.count (bands f p) p.L p.m).size+10≤ bound scheme n κ ∧
    HalfSourceHighScheduleCost.width (bands f p) p.L p.m f.cyclic≤ bound scheme n κ ∧
    GraphHalfSourceOutputCost.width f p≤ bound scheme n κ := by
  intro out f p
  have hf:=fields n call hn hv
  change p.L≤ _ ∧ p.m≤ _ ∧ p.t≤ _ ∧ f.cyclic.size≤ _ ∧ p.N.size≤ _ ∧ (bands f p).size≤ _ ∧ _ at hf
  rcases hf with ⟨hL,hm,ht,hq,hN,hS,hG⟩
  have hshape := shape_width n call hn hv
  change GraphOwnBandShapeBounds.width f p≤ shapeConstant*n.size at hshape
  have hSsq := ParameterExecution.size_mul (bands f p) (bands f p)
  have hs : 1≤ n.size := Nat.size_pos.mpr (by omega)
  have hI0 := BinaryControllerPolynomialBounds.incidence_pow n (block n) (block_pos n) hs
  have hI := (Nat.size_le_size hI0).trans_eq Nat.size_pow
  have hblock := Nat.size_le_size (HalfSourceBatchGeometry.block_le_n n (by omega))
  have hb : bound scheme n κ=(scheme.q.size+20*shapeConstant+κ+metadataCoefficient+100)*(n.size+1) := rfl
  rw [hb]
  unfold inputWidth metadataWidth HalfSourceLowRoundedRate.width HalfSourceHighScheduleCost.width GraphHalfSourceOutputCost.width
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith only [hL,hm,ht,hq,hSsq,hS,hG,hI,hblock,hshape,
    Nat.zero_le scheme.q.size,Nat.zero_le shapeConstant,Nat.zero_le κ,Nat.zero_le metadataCoefficient]

 theorem bound_log (scheme : RectangularBatch.Scheme) (n κ : ℕ) (hn : 3≤ n) :
    (bound scheme n κ:ℝ)≤ (5*coefficient scheme κ:ℝ)*Real.log n := by
  have hs:=BinaryAPSPPublicCostBounds.size_add_one_le_log n hn
  unfold bound
  push_cast at hs ⊢
  nlinarith [Nat.cast_nonneg (α:=ℝ) (coefficient scheme κ)]

 theorem grid_fit : ∀ᶠ n : ℕ in Filter.atTop, ∀ call : Call n, ∀ _ : 3≤ n,
    ∀ hv : EndToEndAPSP.ValidFactors call.factors,
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    ThinProductCosts.gridSide out.plan.value.L out.plan.value.m≤ out.plan.value.N := by
  filter_upwards [HalfSourceCandidatePlan.original_grid_fit] with n hfit
  intro call hn hv out
  have hp:=hfit call hn hv.1 0
  have hphase:=HalfSourceDispatch.actual_phase n call hv
  have hcanonical:=HalfSourceDispatch.canonical n (block n) call.factors hv
  change (OptimizedFoldedPlan.ordinaryLength (HalfSourceLogGeometry.innerPower n call)).choose (HalfSourceLogGeometry.innerPower n call)*
    4^(OptimizedFoldedPlan.ordinaryLength (HalfSourceLogGeometry.innerPower n call)-HalfSourceLogGeometry.innerPower n call)≤ HalfSourceBatchGeometry.outer n call at hp
  unfold ThinProductCosts.gridSide
  simpa only [out,hcanonical.1,hphase.2.2.1,hphase.2.2.2.2] using hp

#print axioms fields
#print axioms widths
#print axioms bound_log
#print axioms grid_fit
end
end ThinMatrix.HalfSourcePublicWidths
