import HalfSourceDispatchFit
import GraphCallbackStorage

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceAddressGeometry
open HalfSourceBatchFit HalfSourceBatchGeometry HalfSourcePublicFit
noncomputable section

/-- Fixed natural constants, independent of the input and candidate history. -/
def shapeConstant : ℕ := Nat.ceil |widthConstant|+1

def scaleConstant (scheme : RectangularBatch.Scheme) : ℕ :=
  (SharedPreparedWidths.cellSlope scheme+SharedPreparedWidths.fieldSlope scheme+1)*(3*shapeConstant+10)

def payloadConstant (scheme : RectangularBatch.Scheme) : ℕ := 40*scaleConstant scheme+40

def singlePayload (scheme : RectangularBatch.Scheme) (n : ℕ) := 2^(payloadConstant scheme*n.size)

 theorem shape_width (n : ℕ) (call : Call n) (hn : 3≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    GraphOwnBandShapeBounds.width out.split.plan out.plan.value≤ shapeConstant*n.size := by
  dsimp only
  rw [HalfSourceDispatchFit.widths n call hn hv]
  have hw := HalfSourcePublicFit.width_bound n call hn hv.1 0
  have hlog := AdaptiveBitBounds.real_log_le_size n (by omega)
  have hnlog : 0≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤ n by omega))
  have habs : widthConstant≤ |widthConstant| := le_abs_self _
  have hc : |widthConstant|≤ (shapeConstant:ℝ) := by
    have hh := Nat.le_ceil |widthConstant|
    unfold shapeConstant
    push_cast
    linarith
  have hwidth : (GraphOwnBandShapeBounds.width (HalfSourceCandidatePlan.factorization n call hn hv.1)
      (HalfSourceCandidatePlan.produce n call hn hv.1 0):ℝ)≤ (shapeConstant:ℝ)*(n.size:ℝ) :=
    hw.trans ((mul_le_mul_of_nonneg_right habs hnlog).trans
      ((mul_le_mul_of_nonneg_left hlog (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))))
  exact_mod_cast hwidth

 theorem scale_width (scheme : RectangularBatch.Scheme) (n : ℕ) (call : Call n) (hn : 3≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    GraphOwnBandStorage.scale scheme (GraphOwnBandShapeBounds.width out.split.plan out.plan.value)
      ≤ scaleConstant scheme*n.size := by
  have hw := shape_width n call hn hv
  have hs : 1≤ n.size := Nat.size_pos.mpr (by omega)
  dsimp only at hw ⊢
  unfold GraphOwnBandStorage.scale scaleConstant
  calc
    _ ≤  (SharedPreparedWidths.cellSlope scheme+SharedPreparedWidths.fieldSlope scheme+1)*
      ((3*shapeConstant+10)*n.size) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by ring

 theorem payload_bound (scheme : RectangularBatch.Scheme) (n : ℕ) (call : Call n) (hn : 3≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    GraphCallbackStorage.payload out.split.plan out.plan.value scheme
      (S:=bands out.split.plan out.plan.value)≤ singlePayload scheme n := by
  let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
  have ht:=ThinMatrixBackend.tileWidth_pos out.plan.value.L out.plan.value.m out.plan.value.m_le_L
  have hSN : bands out.split.plan out.plan.value≤ out.plan.value.N :=
    (ceilDiv_le_iff_le_mul ht).mpr (Nat.le_mul_of_pos_left _ ht)
  have hp := GraphCallbackStorage.payload_bound out.split.plan out.plan.value scheme (block_pos n) hSN
  have hs:=scale_width scheme n call hn hv
  have hnsize : 1≤ n.size := Nat.size_pos.mpr (by omega)
  apply hp.trans
  unfold singlePayload
  apply Nat.pow_le_pow_right (by decide)
  unfold payloadConstant
  nlinarith

/-- A type's recursive matrix scalar/counter fields fit a fixed linear
width, independently of the requested output incidences. -/
 theorem recursive_field_width (scheme : RectangularBatch.Scheme)
    (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
    (n : ℕ) (call : Call n) (hn : 3≤ n) (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    ∀ base : GraphAdaptiveRootBatch.Index out.split.plan out.plan.value,
    GraphOwnBandStorage.fields out.split.plan out.plan.value base scheme hnum hden hz≤ scaleConstant scheme*n.size := by
  intro out base
  have hb : (0:ℕ)≤ out.plan.value.N := Nat.zero_le _
  exact (GraphOwnBandStorage.recursive_bounds out.split.plan out.plan.value base scheme hnum hden hz
    (block_pos n) hb).2.trans (scale_width scheme n call hn hv)

#print axioms shape_width
#print axioms scale_width
#print axioms payload_bound
#print axioms recursive_field_width
end
end ThinMatrix.HalfSourceAddressGeometry
