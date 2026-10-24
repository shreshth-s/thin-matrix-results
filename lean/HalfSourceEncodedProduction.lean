import HalfSourceAdaptiveActualCost
import GraphSharedSourceProduction

/-! Price adaptive encoders directly on the actual callback source producer.
The bound is independent of input values and band identifiers. -/
namespace ThinMatrix.HalfSourceEncodedProduction
open HalfSourceAdaptiveFamilyCost
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000
noncomputable section

 def budget (m q : ℕ) : ℕ :=
  1000000000000000000000000*q*(m+1)^12*
    (HalfSourceActualVolumes.roots m+HalfSourceGroupVolume.groupCount m*cap m)

 theorem uniform {L0 m t0 q : ℕ} (hL : L0=L m) (ht : t0=t m)
    (hm0 : 0 < m) (hm : m≤L0-m)
    (keys : ResidualFamilyKeys.Prepared L0 m t0)
    (hk : keys.channels.toList=(ResidualFamilyKeys.channels m t0).value)
    (sources : ExactHalfBandSources.Families L0 m q) (hq : 1≤q)
    (ha : GraphResidualFamilies.SourceBound sources (2^(L0+m))) :
    (GraphAdaptivePrefix.execute hm (HalfSourceSuffixChoice.limit m (L0-m))
      (GraphResidualFamilies.execute keys sources).value).bitSteps+
      (GraphAdaptivePrefix.execute hm (HalfSourceSuffixChoice.limit m (L0-m))
        (GraphResidualFamilies.execute keys sources).value).control≤budget m q := by
  subst L0
  subst t0
  exact (HalfSourceAdaptiveActualCost.execute_work hm0 hm keys sources hq ha).trans (by
    unfold budget HalfSourceAdaptiveGraphCost.volume
    gcongr
    exact HalfSourceActualVolumes.groups_le m keys.channels hk)

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 theorem actual (hm : p.m≤p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (a b : ℕ)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m)
    (ht : p.t=OptimizedFoldedPlan.channelLength p.m) (hm0 : 0 < p.m) :
    let out := GraphAdaptivePrefix.fromInputs f p hm block input a b
      (HalfSourceSuffixChoice.limit p.m (p.L-p.m))
    out.encoded.bitSteps+out.encoded.control≤budget p.m f.cyclic := by
  dsimp only[GraphAdaptivePrefix.fromInputs]
  apply uniform hL ht hm0 hm
  · exact ResidualFamilyKeys.prepare_channels _ _
  · exact f.cyclic_pos
  · exact GraphResidualFamilies.source_bound f p block input a b

#print axioms uniform
#print axioms actual
end
end ThinMatrix.HalfSourceEncodedProduction
