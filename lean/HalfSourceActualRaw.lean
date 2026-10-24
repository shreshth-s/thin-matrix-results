import HalfSourceRawAbsorption
import HalfSourceDispatch

namespace ThinMatrix.HalfSourceActualRaw
open HalfSourceBatchFit
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

theorem eq_phase (n : ℕ) (call : Call n) (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    HalfSourceRawAbsorption.total n out.plan.value.N ((4:ℝ)^out.plan.value.m) out.split.plan.cyclic
      (CompactBlocks.blockCount n (block n))=HalfSourceComputedCosts.phaseRawSum n call := by
  dsimp only
  have hh := HalfSourceDispatch.actual_phase n call hv
  dsimp only at hh
  simp only[HalfSourceRawAbsorption.total,HalfSourceComputedCosts.phaseRawSum,hh.2.2.1,hh.2.2.2.2,hh.2.1,
    HalfSourceLogGeometry.dimension_eq,Nat.cast_pow,Nat.cast_ofNat,blocks]

#print axioms eq_phase
end
end ThinMatrix.HalfSourceActualRaw
