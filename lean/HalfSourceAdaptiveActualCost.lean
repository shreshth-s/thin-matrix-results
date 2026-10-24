import HalfSourceAdaptiveGraphCost

/-! Discharge the adaptive encoder's structural hypotheses on the actual
retained root-producing program. Only the raw source coefficient bound remains,
which ExactHalfSourceBounds proves for original callback inputs. -/
namespace ThinMatrix.HalfSourceAdaptiveActualCost
open HalfSourceAdaptiveFamilyCost HalfSourceAdaptiveGraphCost
noncomputable section
set_option maxHeartbeats 3000000
attribute [local irreducible] GoodMapEmbedding.goodSlots OptimizedFoldedPlan.ordinaryLength

variable {m C : ℕ}

 theorem channels (keys : ResidualFamilyKeys.Prepared (L m) m (t m))
    (sources : ExactHalfBandSources.Families (L m) m C) :
    Channels (GraphResidualFamilies.execute keys sources).value keys.channels := by
  intro u v run i j c
  simp only [GraphResidualFamilies.execute_get,RetainedResidualFamily.execute_get]
  constructor <;> rfl

 theorem magnitude (keys : ResidualFamilyKeys.Prepared (L m) m (t m))
    (sources : ExactHalfBandSources.Families (L m) m C)
    (ha : GraphResidualFamilies.SourceBound sources (2^(L m+m))) :
    GraphRootWindows.RootBound (GraphResidualFamilies.execute keys sources).value (2^(L m+4*m)) := by
  have heq : 2^m*(4^m*2^(L m+m))=(2:ℕ)^(L m+4*m) := by
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_add,←pow_add]
    congr 1
    omega
  rw [← heq]
  intro u v run
  constructor <;> intro i j c
  · simp only [GraphResidualFamilies.execute_get,RetainedResidualFamily.execute_get]
    exact ResidualWindowSupport.produce_bound _ _ _ _ _ (ha u v run).1
  · simp only [GraphResidualFamilies.execute_get,RetainedResidualFamily.execute_get]
    exact ResidualWindowSupport.produce_bound _ _ _ _ _ (ha u v run).2

 theorem execute_work (hm0 : 0 < m) (hm : m≤L m-m)
    (keys : ResidualFamilyKeys.Prepared (L m) m (t m))
    (sources : ExactHalfBandSources.Families (L m) m C) (hC : 1≤C)
    (ha : GraphResidualFamilies.SourceBound sources (2^(L m+m))) :
    (GraphAdaptivePrefix.execute hm (cap m) (GraphResidualFamilies.execute keys sources).value).bitSteps+
      (GraphAdaptivePrefix.execute hm (cap m) (GraphResidualFamilies.execute keys sources).value).control≤
      1000000000000000000000000*C*(m+1)^12*volume m keys.channels :=
    HalfSourceAdaptiveGraphCost.execute_work hm0 hm _ keys.channels (channels keys sources) hC (magnitude keys sources ha)

#print axioms channels
#print axioms magnitude
#print axioms execute_work
end
end ThinMatrix.HalfSourceAdaptiveActualCost
