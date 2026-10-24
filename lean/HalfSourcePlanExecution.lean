import BinaryTriangleSetupCosts
import HalfSourceLogGeometry

/-! Literal public plan setup using the exact-half source parameters.
All loops are the charged finite indexed-array programs; the coefficient
width remains an upper bound, and no old exponent parameters are used. -/
namespace ThinMatrix.HalfSourcePlanExecution
open BinaryTriangleSetupCosts
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
/-- Joint actual public setup. Square-root candidates, bit lengths, logarithm
and the padded power are computed by the charged loops above. The remaining
eighty sites cover the fixed straight-line rational parameter arithmetic,
dimensions, width arithmetic and payload construction. -/
def preparePlan (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    Run (BinaryFoldedFactory.Plan (n:=n) (h:=h) f) :=
  let d:=3*f.folded
  let width:=foldWidth d
  let raw:=h*d
  let rawBits:=bitLength raw
  let exponent:=clogLoop (rawBits.value+1) raw
  let padded:=power4 exponent.value
  let L:=OptimizedFoldedPlan.ordinaryLength exponent.value
  let t:=OptimizedFoldedPlan.channelLength exponent.value
  let qBits:=bitLength f.cyclic
  have hexponent : exponent.value=FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f) := by
    dsimp only [exponent,FoldedBackendExecution.middleExponent,FoldedBackendExecution.rawMiddle,
      FoldedBackendExecution.physicalFold]
    apply clogLoop_value
    rw [bitLength_value]
    exact (clog4_le_size raw).trans (by omega)
  let plan : BinaryFoldedFactory.Plan (n:=n) (h:=h) f :=
    { L:=L,m:=exponent.value,t:=t,foldWidth:=width.value,N:=n*width.value,D:=padded.value,raw:=raw
      lowWidth:=runtimeLowWidth L exponent.value qBits.value
      foldWidth_eq:=foldWidth_value d
      N_eq:=by
        change n*(foldWidth d).value=n*FoldedCounts.foldWidth d
        rw [foldWidth_value]
      D_eq:=by rw [power4_value,hexponent];rfl
      raw_eq:=rfl
      m_le_L:=OptimizedFoldedPlan.ordinaryLength_lower _
      t_le:=(OptimizedFoldedPlan.channelLength_upper _).trans (by omega)
      middle_fit:=(power4_value exponent.value).le }
  ⟨plan,width.sites+rawBits.sites+exponent.sites+padded.sites+qBits.sites+80⟩

theorem preparePlan_m (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.m=FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f) := by
  change (clogLoop ((bitLength (h*(3*f.folded))).value+1) (h*(3*f.folded))).value=_
  apply clogLoop_value
  rw [bitLength_value]
  exact (clog4_le_size _).trans (by omega)

theorem preparePlan_L (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.L=OptimizedFoldedPlan.ordinaryLength
      (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)) := by
  change OptimizedFoldedPlan.ordinaryLength (preparePlan n h f).value.m=_
  rw [preparePlan_m]

theorem preparePlan_t (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.t=OptimizedFoldedPlan.channelLength
      (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)) := by
  change OptimizedFoldedPlan.channelLength (preparePlan n h f).value.m=_
  rw [preparePlan_m]

theorem preparePlan_lowWidth (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.lowWidth=runtimeLowWidth (preparePlan n h f).value.L
      (preparePlan n h f).value.m f.cyclic.size := by
  exact congrArg (fun qBits => runtimeLowWidth (preparePlan n h f).value.L
    (preparePlan n h f).value.m qBits) (bitLength_value f.cyclic)

theorem preparePlan_lowWidth_common (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.lowWidth=AdaptiveBitBounds.commonBitWidth 2 0
      (preparePlan n h f).value.L (preparePlan n h f).value.m f.cyclic.size := by
  rw [preparePlan_lowWidth,runtimeLowWidth_eq_common]

theorem preparePlan_sites (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).sites≤7*(3*f.folded)+15*(h*(3*f.folded)).size+
      4*(preparePlan n h f).value.m+7*f.cyclic.size+110 := by
  have hw:=foldWidth_sites (3*f.folded)
  have hr:=bitLength_sites (h*(3*f.folded))
  have hc:=clogLoop_sites ((bitLength (h*(3*f.folded))).value+1) (h*(3*f.folded))
  have hp:=power4_sites (preparePlan n h f).value.m
  have hq:=bitLength_sites f.cyclic
  rw [bitLength_value] at hc
  change (foldWidth (3*f.folded)).sites+(bitLength (h*(3*f.folded))).sites+
    (clogLoop ((bitLength (h*(3*f.folded))).value+1) (h*(3*f.folded))).sites+
    (power4 (preparePlan n h f).value.m).sites+(bitLength f.cyclic).sites+80≤_
  rw [bitLength_value]
  omega


 theorem preparePlan_half (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.m ≤ (preparePlan n h f).value.L-(preparePlan n h f).value.m := by
  rw[preparePlan_L,preparePlan_m]
  have hbounds := OptimizedFoldedPlan.rounded_bounds (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f))
  have hc : (2:ℝ) ≤ OptimizedFoldedPlan.c := by norm_num[OptimizedFoldedPlan.c]
  have hh : (2:ℝ)*(FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f):ℝ) ≤
      OptimizedFoldedPlan.ordinaryLength (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)) := by nlinarith [hbounds.1, Nat.cast_nonneg (α:=ℝ) (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f))]
  have hhN : 2*FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f) ≤
      OptimizedFoldedPlan.ordinaryLength (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)) := by exact_mod_cast hh
  omega

#print axioms preparePlan_m
#print axioms preparePlan_L
#print axioms preparePlan_t
#print axioms preparePlan_lowWidth_common
#print axioms preparePlan_sites
#print axioms preparePlan_half
end ThinMatrix.HalfSourcePlanExecution
