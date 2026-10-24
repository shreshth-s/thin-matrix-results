import HalfSourceLowRoundedRate
import GraphHalfSourceExecution
import HalfSourceDispatchFit

namespace ThinMatrix.HalfSourceLowExecutionRate
open BinaryCell GraphOwnBandTypeRate
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
noncomputable section

 theorem exists_execution_rate : ∃ scheme : RectangularBatch.Scheme,
    ∃ hnum : scheme.num=861, ∃ hden : scheme.den=500, ∃ hz : scheme.z=15,
    scheme.Valid ∧ ∃ K : ℝ, 0<K ∧
    ∀ n h r : ℕ, ∀ f : CompactBlocks.PhysicalFactorization r,
    ∀ p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f,
    ∀ hm : p.m≤p.L-p.m, ∀ input : BinaryFoldedFormation.Inputs n,
    ∀ price Lw : ℕ, 1≤CompactBlocks.blockCount n h →
    p.L=OptimizedFoldedPlan.ordinaryLength p.m → p.t=OptimizedFoldedPlan.channelLength p.m →
    32 ≤ p.m → ThinProductCosts.gridSide p.L p.m ≤ p.N →
    (∀ u v run c side,Fits f p (GraphOwnLowProduction.index f p u v run c side) scheme
      (GraphOwnBandTargets.prepare f p input (GraphHalfSourceSetup.bands_bound f p input.target)).value Lw) →
    let out := GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz price
    (out.low.bitSteps+price*out.low.control:ℝ)≤K*(price+1)*(HalfSourceLowRoundedRate.width f p Lw:ℝ)^19*
      ((CompactBlocks.blockCount n h:ℝ)*f.cyclic*
        ((FoldedBackendExecution.windowQuerySize n:ℝ)*(((4:ℝ)^p.m)^HalfSourceParameters.q1)+
          (p.N:ℝ)*(((4:ℝ)^p.m)^HalfSourceParameters.E))+(4:ℝ)^p.m) := by
  obtain ⟨scheme,hnum,hden,hz,hvalid,K,hK,hcost⟩ := HalfSourceLowProductionCost.exists_production_rate
  refine ⟨scheme,hnum,hden,hz,hvalid,HalfSourceLowRoundedRate.coefficient K,?_,?_⟩
  · unfold HalfSourceLowRoundedRate.coefficient
    have hc := HalfSourceCompletionTotal.constant_pos
    positivity
  intro n h r f p hm input price Lw hB hL ht hm0 hfit hfits
  let setup := GraphHalfSourceSetup.execute f p hm input
  have hkeys : setup.value.keys.channels.toList=(ResidualFamilyKeys.channels p.m p.t).value := by
    change (ResidualFamilyKeys.prepare (GraphSharedTargets.shape f p).layout p.t).value.channels.toList=_
    exact ResidualFamilyKeys.prepare_channels _ _
  have hws : ∀ d,(view (setup.value.weights.get d)).natAbs≤2^(2*p.m) := by
    intro d
    exact WeightedRootProducts.weights_bound _ _ d
  have hc := hcost n h r (GraphHalfSourceSetup.S f p) f p hm input
    (GraphHalfSourceSetup.bands_bound f p input.target) setup.value.low
    (GraphHalfSourceSetup.low_correct f p hm input) setup.value.keys.channels hkeys setup.value.weights hws price Lw hB hfits
  have hr := HalfSourceLowRoundedRate.bound f p K hK.le price Lw hL ht hm0 hB hfit
  exact hc.trans hr

#print axioms exists_execution_rate
end
end ThinMatrix.HalfSourceLowExecutionRate
