import HalfSourceHighBlockCost
import HalfSourcePublicWidths
import HalfSourceRawAbsorption
import GraphHalfSourceExecution

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
namespace ThinMatrix.HalfSourceHighExecutionRate
open HalfSourceParameters HalfSourceBatchFit HalfSourcePublicFit
open Filter
noncomputable section
attribute [local irreducible] GraphHalfSourceSetup.execute HalfSourceDispatch.prepare

 theorem actual {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
    (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
    (price : ℕ) (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m)
    (ht : p.t=OptimizedFoldedPlan.channelLength p.m) (hm0 : 0 < p.m)
    (hB : 1≤CompactBlocks.blockCount n h) (hfit : ThinProductCosts.gridSide p.L p.m≤p.N) :
    ((GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz price).high.operations:ℝ)≤
      HalfSourceHighBlockCost.constant*(CompactBlocks.blockCount n h:ℝ)*
        (HalfSourceHighScheduleCost.width (bands f p) p.L p.m f.cyclic:ℝ)^40*
        HalfSourceHighBlockCost.terms p.N p.m (FoldedBackendExecution.windowQuerySize n) f.cyclic := by
  let setup := GraphHalfSourceSetup.execute f p hm input
  exact HalfSourceHighBlockCost.actual f p setup.value.shape (fun b=>setup.value.high.get b)
    setup.value.targets.requests (GraphHalfSourceSetup.requests_bound f p hm input) input
    (GraphHalfSourceSetup.high_correct f p hm input) hL ht hm0 hB hfit

 def coefficient (scheme : RectangularBatch.Scheme) (κ : ℕ) : ℝ :=
  3*HalfSourceHighBlockCost.constant*(5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)^40

 theorem eventual (scheme : RectangularBatch.Scheme)
    (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15) (κ : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ _ : 3≤n,
    ∀ hv : EndToEndAPSP.ValidFactors call.factors,
    ∀ input : BinaryFoldedFormation.Inputs n, ∀ price : ℕ,
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    let f:=out.split.plan
    let p:=out.plan.value
    ((GraphHalfSourceExecution.execute f p
      (HalfSourceDispatch.canonical n (block n) call.factors hv).2.2 input
      scheme hnum hden hz price).high.operations:ℝ)≤
      coefficient scheme κ*(Real.log n)^40*HalfSourceComputedCosts.phaseRawSum n call := by
  filter_upwards [HalfSourcePublicWidths.grid_fit,HalfSourceLogGeometry.uniformly_large 1] with n hfit hm
  intro call hn hv input price out f p
  have hcanonical:=HalfSourceDispatch.canonical n (block n) call.factors hv
  have hphase:=HalfSourceDispatch.actual_phase n call hv
  have hm0 : 0 < p.m := by
    have hh:=hm call
    have he : p.m=HalfSourceLogGeometry.innerPower n call := hphase.2.2.1
    omega
  have hB : 1≤CompactBlocks.blockCount n (block n) :=
    HalfSourceInputMetadata.blocks_positive (by omega) (block_pos n)
  have hgrid : ThinProductCosts.gridSide p.L p.m≤p.N := hfit call hn hv
  have hex:=actual f p hcanonical.2.2 input scheme hnum hden hz price
    hcanonical.1 hcanonical.2.1 hm0 hB hgrid
  have hp: (HalfSourceHighScheduleCost.width (bands f p) p.L p.m f.cyclic:ℝ)≤
      (5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)*Real.log n := by
    have hh: (HalfSourceHighScheduleCost.width (bands f p) p.L p.m f.cyclic:ℝ)≤
      (HalfSourcePublicWidths.bound scheme n κ:ℝ) := by
      exact_mod_cast (HalfSourcePublicWidths.widths scheme n κ call hn hv).2.2.2.1
    exact hh.trans (HalfSourcePublicWidths.bound_log scheme n κ hn)
  have hD : (4:ℝ)^p.m=(dimension n call:ℝ) := by
    rw[hphase.2.2.1,HalfSourceLogGeometry.dimension_eq]
    push_cast
    rfl
  have hvolume : (CompactBlocks.blockCount n (block n):ℝ)*
      HalfSourceHighBlockCost.terms p.N p.m (FoldedBackendExecution.windowQuerySize n) f.cyclic≤
      3*HalfSourceComputedCosts.phaseRawSum n call := by
    have hh:=HalfSourceRawAbsorption.high (n:ℝ) (p.N:ℝ) ((4:ℝ)^p.m) (f.cyclic:ℝ)
      (CompactBlocks.blockCount n (block n):ℝ) (by positivity) (by positivity)
      (by exact_mod_cast f.cyclic_pos) (by positivity)
    convert hh using 1
    · unfold HalfSourceHighBlockCost.terms FoldedBackendExecution.windowQuerySize
      push_cast
      ring
    · unfold HalfSourceRawAbsorption.total HalfSourceComputedCosts.phaseRawSum
      rw[hphase.2.1,hphase.2.2.2.2,hD]
      rfl
  have hc := HalfSourceHighBlockCost.constant_nonneg
  have hl : 0≤Real.log (n:ℝ) := by linarith[PhaseGeometry.one_le_log_nat n hn]
  have hterms : 0≤HalfSourceHighBlockCost.terms p.N p.m (FoldedBackendExecution.windowQuerySize n) f.cyclic := by
    unfold HalfSourceHighBlockCost.terms;positivity
  calc
    _ ≤HalfSourceHighBlockCost.constant*(CompactBlocks.blockCount n (block n):ℝ)*
        ((5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)*Real.log n)^40*
        HalfSourceHighBlockCost.terms p.N p.m (FoldedBackendExecution.windowQuerySize n) f.cyclic := hex.trans (by gcongr)
    _ = HalfSourceHighBlockCost.constant*(5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)^40*(Real.log n)^40*
        ((CompactBlocks.blockCount n (block n):ℝ)*HalfSourceHighBlockCost.terms p.N p.m (FoldedBackendExecution.windowQuerySize n) f.cyclic) := by ring
    _ ≤HalfSourceHighBlockCost.constant*(5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)^40*(Real.log n)^40*
        (3*HalfSourceComputedCosts.phaseRawSum n call) := by gcongr
    _ =_ := by unfold coefficient;ring

#print axioms actual
#print axioms eventual
end
end ThinMatrix.HalfSourceHighExecutionRate
