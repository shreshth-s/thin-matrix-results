import HalfSourcePublicFit
import HalfSourceDispatch

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceDispatchFit
open Filter GraphAdaptiveRootBatch GraphOwnBandTypeRate
open HalfSourceBatchFit HalfSourceBatchGeometry HalfSourceCandidatePlan
open HalfSourcePublicFit

 theorem widths (n : ℕ) (call : Call n) (hn : 3≤n) (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    GraphOwnBandShapeBounds.width out.split.plan out.plan.value=
      GraphOwnBandShapeBounds.width (factorization n call hn hv.1) (produce n call hn hv.1 0) := by
  have hphase := HalfSourceDispatch.actual_phase n call hv
  have hcanonical := HalfSourceDispatch.canonical n (block n) call.factors hv
  dsimp only at hphase hcanonical ⊢
  simp only [GraphOwnBandShapeBounds.width,hcanonical.1,hphase.2.2.1,hphase.2.2.2.2,hphase.2.1]
  rfl

attribute [local irreducible] HalfSourceDispatch.prepare HalfSourceCandidatePlan.produce HalfSourceCandidatePlan.factorization HalfSourceBatchFit.R HalfSourceBatchFit.S

 theorem eventually_fits (scheme : RectangularBatch.Scheme) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ _ : 3≤n, ∀ hv : EndToEndAPSP.ValidFactors call.factors,
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    let f:=out.split.plan
    let p:=out.plan.value
    ∀ base : Index f p, ∀ targets : GraphOwnBandTargets.Prepared f p (S:=bands f p),
    ∀ hb : ∀ i,(targets.requests.get i).bandL<bands f p ∧ (targets.requests.get i).bandR<bands f p,
    GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value →
    Fits f p base scheme targets (scheme.q.size+3*GraphOwnBandShapeBounds.width f p+30) := by
  filter_upwards [HalfSourceSuffixPlan.selected_support_batch_fit,HalfSourceCandidatePlan.tileWidth_fit] with n hfit htile
  intro call hn hv out f p base targets hb htree
  let fp:=factorization n call hn hv.1
  let pp:=produce n call hn hv.1 0
  have hphase := HalfSourceDispatch.actual_phase n call hv
  have hcanonical := HalfSourceDispatch.canonical n (block n) call.factors hv
  have hppm : pp.m=HalfSourceLogGeometry.innerPower n call := by
    unfold pp produce HalfSourceCandidatePlan.factorization
    rfl
  have hppL : pp.L=OptimizedFoldedPlan.ordinaryLength pp.m := by
    unfold pp produce
    rfl
  have hdims := dimensions n call hn hv.1 0
  have hm : p.m=pp.m := hphase.2.2.1.trans hppm.symm
  have hL : p.L=pp.L := (hcanonical.1.trans (congrArg OptimizedFoldedPlan.ordinaryLength hm)).trans hppL.symm
  have hN : p.N=pp.N := hphase.2.2.2.2.trans hdims.1.symm
  have hq : f.cyclic=fp.cyclic := hphase.2.1.trans hdims.2.2.2.symm
  have hpos : 0<p.N := by
    rw [hN]
    exact (ThinMatrixBackend.tileWidth_pos pp.L pp.m pp.m_le_L).trans_le (htile call hn hv.1 0)
  have hbnds := bands_bounds f p hpos
  apply GraphOwnBandShapeBounds.fits f p base (block_pos n) hbnds.1 hbnds.2 scheme targets hb htree
  have hf := hfit call hn hv.1 0 (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2
  have hell := (HalfSourceSuffixChoice.forType_fit p.L p.m (GraphWindowCompatibility.counts base.channel).1
    (GraphWindowCompatibility.counts base.channel).2).1
  change (WindowSharedCompletion.D (p.L-p.m) (E f p base) (p.m/2)
    (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2)^15≤_
  simp only [WindowSharedCompletion.D,E,GraphAdaptiveCompatibility.typeLength,
    WindowPrefixProgram.length,Nat.min_eq_left hell]
  change CappedSubsetList.count (HalfSourceSuffixChoice.forType p.L p.m _ _)
    (WindowPrefixProgram.cap (p.L-p.m) (HalfSourceSuffixChoice.forType p.L p.m _ _) (p.m/2) _ _)^15≤
    CompactBlocks.blockCount n (block n)*((p.m+1)*f.cyclic)
  let pred (x : ℕ×ℕ×ℕ) :=
    CappedSubsetList.count (HalfSourceSuffixChoice.forType x.1 x.2.1
      (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2)
      (WindowPrefixProgram.cap (x.1-x.2.1) (HalfSourceSuffixChoice.forType x.1 x.2.1
        (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2)
        (x.2.1/2) (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2)^15≤
        CompactBlocks.blockCount n (block n)*((x.2.1+1)*x.2.2)
  have htup : (p.L,p.m,f.cyclic)=(pp.L,pp.m,fp.cyclic) := Prod.ext hL (Prod.ext hm hq)
  have hpred := congrArg pred htup
  change pred (p.L,p.m,f.cyclic)
  rw [hpred]
  exact hf

 theorem fit_width_bound (scheme : RectangularBatch.Scheme) (n : ℕ) (call : Call n)
    (hn : 3≤n) (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out:=HalfSourceDispatch.prepare n (block n) call.factors hv
    (scheme.q.size+3*GraphOwnBandShapeBounds.width out.split.plan out.plan.value+30:ℝ)
      ≤fitConstant scheme*Real.log n := by
  dsimp only
  rw [widths n call hn hv]
  exact HalfSourcePublicFit.fit_width_bound scheme n call hn hv.1 0

#print axioms widths
#print axioms eventually_fits
#print axioms fit_width_bound
end ThinMatrix.HalfSourceDispatchFit
