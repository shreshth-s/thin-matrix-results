import GraphOwnBandShapeBounds
import HalfSourceSuffixPlan
import HalfSourceLogGeometry

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourcePublicFit
open Filter GraphAdaptiveRootBatch GraphOwnBandTypeRate
open HalfSourceBatchFit HalfSourceBatchGeometry HalfSourceCandidatePlan

abbrev bands {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) :=
  TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)

 theorem bands_bounds {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hN : 0<p.N) :
    1≤bands f p ∧ bands f p≤p.N := by
  have ht := ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L
  exact ⟨TilingCosts.bandCount_pos _ _ hN ht,
    (ceilDiv_le_iff_le_mul ht).mpr (Nat.le_mul_of_pos_left _ ht)⟩

/-- The independent batch guard and every address/control width in the
per-type rate hold on the actual computed candidate shapes. No numeric Fits
premise is carried into the final rate. -/
 theorem eventually_fits (scheme : RectangularBatch.Scheme) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ hn : 3≤n, ∀ hnd : call.factors.Nodup,
    ∀ lowWidth : ℕ,
    let f:=factorization n call hn hnd
    let p:=produce n call hn hnd lowWidth
    ∀ base : Index f p, ∀ targets : GraphOwnBandTargets.Prepared f p (S:=bands f p),
    ∀ hb : ∀ i,(targets.requests.get i).bandL<bands f p ∧ (targets.requests.get i).bandR<bands f p,
    GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value →
    Fits f p base scheme targets (scheme.q.size+3*GraphOwnBandShapeBounds.width f p+30) := by
  filter_upwards [HalfSourceSuffixPlan.selected_support_batch_fit,HalfSourceCandidatePlan.tileWidth_fit] with n hfit htile
  intro call hn hnd lowWidth f p base targets hb htree
  have htilepos := ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L
  have hN : 0<p.N := htilepos.trans_le (htile call hn hnd lowWidth)
  have hbands := bands_bounds f p hN
  apply GraphOwnBandShapeBounds.fits f p base (block_pos n) hbands.1 hbands.2 scheme targets hb htree
  have hf := hfit call hn hnd lowWidth (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2
  have hell := (HalfSourceSuffixChoice.forType_fit p.L p.m (GraphWindowCompatibility.counts base.channel).1
    (GraphWindowCompatibility.counts base.channel).2).1
  simpa only [SharedCompletionTile.col,GraphAdaptiveRootBatch.D,WindowSharedCompletion.D,
    E,GraphAdaptiveCompatibility.typeLength,WindowPrefixProgram.length,Nat.min_eq_left hell] using hf

noncomputable def widthConstant : ℝ :=
  32*(12*HalfSourceLogGeometry.indexConstant+
    (HalfSourceLogGeometry.cyclicLogConstant/Real.log 2+1)+
    (HalfSourceLogGeometry.outerLogConstant/Real.log 2+1)+(1/Real.log 2+1)+1)

 theorem width_bound (n : ℕ) (call : Call n) (hn : 3≤n) (hnd : call.factors.Nodup) (lowWidth : ℕ) :
    (GraphOwnBandShapeBounds.width (factorization n call hn hnd) (produce n call hn hnd lowWidth):ℝ)
      ≤widthConstant*Real.log n := by
  let f:=factorization n call hn hnd
  let p:=produce n call hn hnd lowWidth
  have hL : p.L≤11*p.m := HalfSourceSuffixPlan.ordinaryLength_le p.m
  have hm : p.m=HalfSourceLogGeometry.innerPower n call := rfl
  have hmR : (p.m:ℝ)≤HalfSourceLogGeometry.indexConstant*Real.log n := by
    have hh := HalfSourceLogGeometry.innerPower_bound n hn call
    rw [←hm] at hh
    linarith
  have hLR : (p.L:ℝ)≤11*(p.m:ℝ) := by exact_mod_cast hL
  have hq := HalfSourceLogGeometry.cyclic_size n hn call
  have hN := HalfSourceLogGeometry.outer_size n hn call
  have hnsize := HalfSourceLogGeometry.size_from_log n n 1 hn (by simp)
  have hlog := PhaseGeometry.one_le_log_nat n hn
  have hfq : f.cyclic=call.cyclic S := rfl
  have hpN : p.N=outer n call := rfl
  rw [←hfq] at hq
  rw [←hpN] at hN
  change (GraphOwnBandShapeBounds.width f p:ℝ)≤_
  unfold GraphOwnBandShapeBounds.width widthConstant
  push_cast
  nlinarith

noncomputable def fitConstant (scheme : RectangularBatch.Scheme) : ℝ :=
  scheme.q.size+3*widthConstant+30

 theorem fit_width_bound (scheme : RectangularBatch.Scheme) (n : ℕ) (call : Call n)
    (hn : 3≤n) (hnd : call.factors.Nodup) (lowWidth : ℕ) :
    (scheme.q.size+3*GraphOwnBandShapeBounds.width (factorization n call hn hnd)
      (produce n call hn hnd lowWidth)+30:ℝ)≤fitConstant scheme*Real.log n := by
  have hw := width_bound n call hn hnd lowWidth
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hc : 0≤(scheme.q.size:ℝ)+30 := by positivity
  have hh := mul_le_mul_of_nonneg_left hl hc
  unfold fitConstant
  nlinarith

#print axioms bands_bounds
#print axioms eventually_fits
#print axioms width_bound
#print axioms fit_width_bound
end ThinMatrix.HalfSourcePublicFit
