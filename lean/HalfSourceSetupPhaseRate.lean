import HalfSourceSharedSourceRate
import HalfSourceSetupTransfer
import HalfSourcePhaseAlgebra
import HalfSourceActualRaw
import HalfSourceTargetActualCost
import HalfSourcePublicWidths

namespace ThinMatrix.HalfSourceSetupPhaseRate
open Filter HalfSourceBatchFit HalfSourceInputMetadata
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 16000
noncomputable section
attribute [local irreducible] HalfSourceDispatch.prepare GraphHalfSourceSetup.execute

def Bound (κ : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ hv : EndToEndAPSP.ValidFactors call.factors,
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    let hm := (HalfSourceDispatch.canonical n (block n) call.factors hv).2.2
    ∀ X Y T : BinaryTriangleExecution.IntTable n,
    CountedEndToEndAPSP.entryQueryBound (BinaryTriangleExecution.viewTable X)
      (BinaryTriangleExecution.viewTable Y) (BinaryTriangleExecution.viewTable T)≤n^κ →
    ((GraphHalfSourceSetup.execute out.split.plan out.plan.value hm ⟨X,Y,T⟩).operations:ℝ)≤
      C*(Real.log (n:ℝ))^17*HalfSourceComputedCosts.phaseRawSum n call

 theorem exists_setup_rate (scheme : RectangularBatch.Scheme) (κ : ℕ) :
    ∃ C : ℝ, 0<C ∧ Bound κ C := by
  let H : ℝ := (5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)
  let C : ℝ := (8*HalfSourceSharedSourceRate.constant+3*1000000000000000)*H^17
  have hH : 0<H := by dsimp[H,HalfSourcePublicWidths.coefficient];positivity
  have hsourceC : 0<HalfSourceSharedSourceRate.constant := lt_of_lt_of_le (by positivity) HalfSourceSharedSourceRate.constant_bounds.1
  refine ⟨C,by dsimp[C];positivity,?_⟩
  obtain ⟨m0,hm0⟩ := Filter.eventually_atTop.mp HalfSourceDirectSetup.eventual_budget_fit
  unfold Bound
  filter_upwards [HalfSourcePublicWidths.grid_fit,HalfSourceLogGeometry.uniformly_large (max 32 m0),
    eventually_ge_atTop (3:ℕ)] with n hgrid hlarge hn
  intro call hv out hm X Y T hentry
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  let f := out.split.plan
  let p := out.plan.value
  let W := inputWidth n κ
  let V := metadataWidth n
  have hc := HalfSourceDispatch.canonical n (block n) call.factors hv
  have hp := HalfSourceDispatch.actual_phase n call hv
  have hB := blocks_positive (h:=block n) hn0 (block_pos n)
  have hfit : ThinProductCosts.gridSide p.L p.m≤p.N := hgrid call hn hv
  have hm32 : 32≤p.m := by dsimp[p,out];rw[hp.2.2.1];exact le_trans (le_max_left _ _) (hlarge call)
  have hmFit : m0≤p.m := by dsimp[p,out];rw[hp.2.2.1];exact le_trans (le_max_right _ _) (hlarge call)
  have hmpos : 0 < p.m := lt_of_lt_of_le (by decide : 0 < 32) hm32
  have hN : 1≤p.N := (ThinProductCosts.gridSide_pos p.L p.m p.m_le_L).trans_le hfit
  have htBound := input_bounds X Y T hentry
  have hmetadata (b : Fin (CompactBlocks.blockCount n (block n))) :
      BinaryFoldedFormationCost.MetadataBound n (block n) (FoldedBackendExecution.physicalFold f) f.cyclic b.val V :=
    (metadata n call hn hv b).1
  have hback : (p.N*p.D).size≤V := (metadata n call hn hv ⟨0,hB⟩).2
  have hd : 0<FoldedBackendExecution.physicalFold f := by unfold FoldedBackendExecution.physicalFold;exact Nat.mul_pos (by decide) f.folded_pos
  have hactual := HalfSourceSharedSourceBudget.actual f p hm ⟨X,Y,T⟩ W V hmetadata htBound.1 htBound.2.1
    hn0 hd hback hc.1 hc.2.1 hmpos hfit
  have hdirect := hm0 p.m hmFit f.cyclic
  have hLm : HalfSourceAdaptiveFamilyCost.L p.m=p.L := hc.1.symm
  rw[hLm] at hdirect
  have hfinite := HalfSourceSharedSourceRate.budget f p W V hm32 hB hc.1 hfit hdirect
  have hsource := (show ((GraphSharedSourceProduction.execute f p hm ⟨X,Y,T⟩
      (S:=HalfSourceSharedSourceBudget.bands f p)).operations:ℝ)≤(HalfSourceSharedSourceBudget.budget f p W V:ℝ) by exact_mod_cast hactual).trans hfinite
  have hw := HalfSourcePublicWidths.widths scheme n κ call hn hv
  have hwLog := HalfSourcePublicWidths.bound_log scheme n κ hn
  have hP1 : (W+V+p.m+20:ℝ)≤H*Real.log n := (show (W+V+p.m+20:ℝ)≤(HalfSourcePublicWidths.bound scheme n κ:ℝ) by exact_mod_cast hw.1).trans hwLog
  have hpoly1 := pow_le_pow_left₀ (show 0≤(W+V+p.m+20:ℝ) by positivity) hP1 17
  have hvol := HalfSourceRawAbsorption.source (n:ℝ) (p.N:ℝ) ((4:ℝ)^p.m) (f.cyclic:ℝ)
    (CompactBlocks.blockCount n (block n):ℝ) (Nat.cast_nonneg _) (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htot := HalfSourceActualRaw.eq_phase n call hv
  change HalfSourceRawAbsorption.total n p.N ((4:ℝ)^p.m) f.cyclic (CompactBlocks.blockCount n (block n))=_ at htot
  rw[htot] at hvol
  change (CompactBlocks.blockCount n (block n):ℝ)*HalfSourceSharedSourceRate.volume p.N p.m f.cyclic≤_ at hvol
  have hsource' : ((GraphSharedSourceProduction.execute f p hm ⟨X,Y,T⟩
      (S:=GraphHalfSourceSetup.S f p)).operations:ℝ)≤
      8*HalfSourceSharedSourceRate.constant*H^17*(Real.log n)^17*HalfSourceComputedCosts.phaseRawSum n call :=
    HalfSourceSetupTransfer.source _ _ _ _ _ _ _ _ hsourceC.le
      (show 0≤(W+V+p.m+20:ℝ) by positivity)
      (mul_nonneg (Nat.cast_nonneg _) (HalfSourceSharedSourceRate.volume_bounds p.N p.m f.cyclic).1)
      hP1 hvol hsource
  have htarget := HalfSourceTargetActualCost.actual f p hm ⟨X,Y,T⟩ (metadata_zero n call hn hv)
    htBound.2.2 hmpos hB hc.1 hc.2.1 hfit
  let P := HalfSourceTargetPolynomial.width (GraphHalfSourceSetup.S f p) p.L p.m p.t W V
  have hP : (P:ℝ)≤H*Real.log n := (show (P:ℝ)≤(HalfSourcePublicWidths.bound scheme n κ:ℝ) by exact_mod_cast hw.2.2.1).trans hwLog
  have hHlog : 1≤H*Real.log n := by
    have hpos : 1≤P := by
      dsimp only[P,HalfSourceTargetPolynomial.width]
      exact (by decide : 1≤10).trans (Nat.le_add_left 10 _)
    exact (show (1:ℝ)≤P by exact_mod_cast hpos).trans hP
  have hpoly2 := (pow_le_pow_left₀ (Nat.cast_nonneg P) hP 7).trans (pow_le_pow_right₀ hHlog (show 7≤17 by decide))
  have hvTarget := HalfSourceRawAbsorption.target (n:ℝ) (p.N:ℝ) ((4:ℝ)^p.m) (f.cyclic:ℝ)
    (CompactBlocks.blockCount n (block n):ℝ) (Nat.cast_nonneg _) (by positivity) (by exact_mod_cast f.cyclic_pos) (by exact_mod_cast hB)
  rw[htot] at hvTarget
  have hM : (FoldedBackendExecution.windowQuerySize n:ℝ)=3*(n:ℝ)^2 := by unfold FoldedBackendExecution.windowQuerySize;push_cast;ring
  dsimp only at htarget
  change _≤_+(1000000000000000*(P:ℝ)^7)*_ at htarget
  rw[hM] at htarget
  have htx := mul_le_mul (mul_le_mul_of_nonneg_left hpoly2 (show (0:ℝ)≤1000000000000000 by norm_num)) hvTarget
    (by positivity) (by positivity)
  have hh := add_le_add hsource' htx
  apply htarget.trans
  apply hh.trans_eq
  dsimp only[C]
  convert HalfSourcePhaseAlgebra.source_target HalfSourceSharedSourceRate.constant H (Real.log n) (HalfSourceComputedCosts.phaseRawSum n call) using 1 <;> norm_num only [show (10:ℝ)^15=1000000000000000 by norm_num]

#print axioms exists_setup_rate
end
end ThinMatrix.HalfSourceSetupPhaseRate
