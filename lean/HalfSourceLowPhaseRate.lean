import HalfSourceLowExecutionRate
import HalfSourceActualRaw
import HalfSourcePublicWidths

namespace ThinMatrix.HalfSourceLowPhaseRate
open Filter HalfSourceBatchFit HalfSourceParameters
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
noncomputable section
attribute [local irreducible] HalfSourceDispatch.prepare GraphHalfSourceExecution.execute

def Bound (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861)
    (hden : scheme.den=500) (hz : scheme.z=15) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ hv : EndToEndAPSP.ValidFactors call.factors,
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    let hm := (HalfSourceDispatch.canonical n (block n) call.factors hv).2.2
    ∀ input : BinaryFoldedFormation.Inputs n, ∀ price : ℕ,
    let execution := GraphHalfSourceExecution.execute out.split.plan out.plan.value hm input scheme hnum hden hz price
    (execution.low.bitSteps+price*execution.low.control:ℝ)≤
      C*(price+1)*(Real.log (n:ℝ))^19*HalfSourceComputedCosts.phaseRawSum n call

 theorem exists_phase_rate : ∃ scheme : RectangularBatch.Scheme,
    ∃ hnum : scheme.num=861, ∃ hden : scheme.den=500, ∃ hz : scheme.z=15,
    scheme.Valid ∧ ∃ C : ℝ, 0<C ∧ Bound scheme hnum hden hz C := by
  obtain ⟨scheme,hnum,hden,hz,hvalid,K,hK,hcost⟩ := HalfSourceLowExecutionRate.exists_execution_rate
  let H : ℝ := (5*HalfSourcePublicWidths.coefficient scheme 0:ℝ)
  have hH : 0<H := by dsimp[H,HalfSourcePublicWidths.coefficient];positivity
  refine ⟨scheme,hnum,hden,hz,hvalid,3*K*H^19,by positivity,?_⟩
  unfold Bound
  filter_upwards [HalfSourceDispatchFit.eventually_fits scheme,HalfSourcePublicWidths.grid_fit,
    HalfSourceLogGeometry.uniformly_large 32,eventually_ge_atTop (3:ℕ)] with n hfits hgrid hm32 hn
  intro call hv out hm input price
  let f := out.split.plan
  let p := out.plan.value
  let Lw := scheme.q.size+3*GraphOwnBandShapeBounds.width f p+30
  have hc := HalfSourceDispatch.canonical n (block n) call.factors hv
  have hp := HalfSourceDispatch.actual_phase n call hv
  have hB := HalfSourceInputMetadata.blocks_positive (h:=block n) (show 0 < n by omega) (block_pos n)
  have hfit : ThinProductCosts.gridSide p.L p.m≤p.N := hgrid call hn hv
  have hm0 : 32 ≤ p.m := by dsimp[p,out];rw[hp.2.2.1];exact hm32 call
  have hN : 1 ≤ p.N := (ThinProductCosts.gridSide_pos p.L p.m p.m_le_L).trans_le hfit
  have hall u v run c side : GraphOwnBandTypeRate.Fits f p (GraphOwnLowProduction.index f p u v run c side) scheme
      (GraphOwnBandTargets.prepare f p input (GraphHalfSourceSetup.bands_bound f p input.target)).value Lw := by
    apply hfits call hn hv (GraphOwnLowProduction.index f p u v run c side)
      (GraphOwnBandTargets.prepare f p input (GraphHalfSourceSetup.bands_bound f p input.target)).value
      (GraphHalfSourceSetup.bands_bound f p input.target)
    exact GraphOwnBandTargets.tree_eq f p input (GraphHalfSourceSetup.bands_bound f p input.target) side
  have he := hcost n (block n) call.factors.prod f p hm input price Lw hB hc.1 hc.2.1 hm0 hfit hall
  have hw := (HalfSourcePublicWidths.widths scheme n 0 call hn hv).2.1
  have hwR : (HalfSourceLowRoundedRate.width f p Lw:ℝ) ≤ H*Real.log (n:ℝ) := by
    have hh : (HalfSourceLowRoundedRate.width f p Lw:ℝ) ≤ (HalfSourcePublicWidths.bound scheme n 0:ℝ) := by exact_mod_cast hw
    exact hh.trans (HalfSourcePublicWidths.bound_log scheme n 0 hn)
  have hraw := HalfSourceRawAbsorption.low (n:ℝ) (p.N:ℝ) ((4:ℝ)^p.m) (f.cyclic:ℝ)
    (CompactBlocks.blockCount n (block n):ℝ) (by exact_mod_cast hN) (one_le_pow₀ (by norm_num))
    (by exact_mod_cast f.cyclic_pos) (by exact_mod_cast hB)
  have hM : (FoldedBackendExecution.windowQuerySize n:ℝ)=3*(n:ℝ)^2 := by unfold FoldedBackendExecution.windowQuerySize;push_cast;ring
  have htot := HalfSourceActualRaw.eq_phase n call hv
  change HalfSourceRawAbsorption.total (n:ℝ) (p.N:ℝ) ((4:ℝ)^p.m) (f.cyclic:ℝ)
    (CompactBlocks.blockCount n (block n):ℝ)=_ at htot
  rw[htot] at hraw
  rw[hM] at he
  have hpw := pow_le_pow_left₀ (Nat.cast_nonneg _) hwR 19
  have hprice : 0 ≤ K*(price+1:ℝ) := by positivity
  calc
    _ ≤K*(price+1)*(HalfSourceLowRoundedRate.width f p Lw:ℝ)^19*
      ((CompactBlocks.blockCount n (block n):ℝ)*f.cyclic*
        ((3*(n:ℝ)^2)*(((4:ℝ)^p.m)^q1)+(p.N:ℝ)*(((4:ℝ)^p.m)^E))+(4:ℝ)^p.m) := he
    _ ≤K*(price+1)*(H*Real.log (n:ℝ))^19*(3*HalfSourceComputedCosts.phaseRawSum n call) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpw hprice) hraw (by positivity)
        (by have hl := PhaseGeometry.one_le_log_nat n hn;positivity)
    _ =_ := by ring

#print axioms exists_phase_rate
end
end ThinMatrix.HalfSourceLowPhaseRate
