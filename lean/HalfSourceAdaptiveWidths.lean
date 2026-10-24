import HalfSourceAdaptiveControl
import HalfSourceBatchCopyVolume
import HalfSourceCapSetup
import HalfSourceChannelTypes

set_option autoImplicit false
set_option maxHeartbeats 2200000

/-! Concrete word widths and the common selected-support factor for actual
adaptive entries. No numeric-magnitude cost is hidden in these bounds. -/
namespace ThinMatrix.HalfSourceAdaptiveWidths
open HalfSourceAdaptiveVolume HalfSourcePrefixVolume

 theorem cap_size (m k : ℕ) : (HalfSourceSuffixChoice.limit m k).size ≤ k.size+2*m+3 := by
  have hh := ParameterExecution.size_mul (k+1) (ComputableParameters.roundedPower 11 50 (4^m))
  have hk := ParameterExecution.size_succ k
  have hr := (Nat.size_le_size (ParameterExecution.roundedPower_le 11 50 (4^m))).trans (ParameterExecution.size_succ (4^m))
  rw [HalfSourceCapSetup.four_size] at hr
  unfold HalfSourceSuffixChoice.limit
  omega

 theorem selected_groups {m C : ℕ} (hm : m ≤ OptimizedFoldedPlan.ordinaryLength m-m)
    (root : RetainedResidualFamily.Entry (OptimizedFoldedPlan.ordinaryLength m) m C) :
    entryGroups (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm
      (HalfSourceSuffixChoice.limit m (OptimizedFoldedPlan.ordinaryLength m-m)) root).value) root ≤
      HalfSourceChannelTypes.groupWeight m (RetainedRootWindows.weights root.channel).value.1
        (RetainedRootWindows.weights root.channel).value.2*
        HalfSourceSuffixChoice.limit m (OptimizedFoldedPlan.ordinaryLength m-m) := by
  let cn := (RetainedRootWindows.weights root.channel).value.1
  let co := (RetainedRootWindows.weights root.channel).value.2
  have hfit := HalfSourceSuffixChoice.forType_fit (OptimizedFoldedPlan.ordinaryLength m) m cn co
  unfold entryGroups
  rw [GraphAdaptivePrefix.entry_optimal_length]
  unfold groups WindowPrefixProgram.prefixLength WindowPrefixProgram.length
  rw [Nat.min_eq_left hfit.1]
  have hh := Nat.mul_le_mul_left
    (4^(2*(OptimizedFoldedPlan.ordinaryLength m-m)-HalfSourceSuffixChoice.forType (OptimizedFoldedPlan.ordinaryLength m) m cn co)*
      2^(HalfSourceSuffixChoice.forType (OptimizedFoldedPlan.ordinaryLength m) m cn co)) hfit.2
  exact hh

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 theorem raw_eq : GraphAdaptiveBatchSources.rawMagnitude f p=2^(p.L+4*p.m) := by
  unfold GraphAdaptiveBatchSources.rawMagnitude
  rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_add,←pow_add]
  congr 1
  omega

 theorem raw_size : (GraphAdaptiveBatchSources.rawMagnitude f p).size=p.L+4*p.m+1 := by
  rw [raw_eq,Nat.size_pow]

 theorem window_size : (GraphAdaptiveBatchSources.windowMagnitude f p).size=(p.L-p.m)+p.L+4*p.m+1 := by
  unfold GraphAdaptiveBatchSources.windowMagnitude
  rw [raw_eq,←pow_add,Nat.size_pow]
  omega

 theorem leaf_size (index : GraphPrefixCompletion.Index p.L p.m p.t) :
    (2^(GraphAdaptiveBatchSources.P f p index)*GraphAdaptiveBatchSources.windowMagnitude f p).size=
      GraphAdaptiveBatchSources.P f p index+(p.L-p.m)+p.L+4*p.m+1 := by
  unfold GraphAdaptiveBatchSources.windowMagnitude
  rw [raw_eq,←pow_add,←pow_add,Nat.size_pow]
  omega

 theorem leaf_size_le (index : GraphPrefixCompletion.Index p.L p.m p.t) :
    (2^(GraphAdaptiveBatchSources.P f p index)*GraphAdaptiveBatchSources.windowMagnitude f p).size ≤ 4*p.L+4*p.m+1 := by
  rw [leaf_size]
  dsimp only [GraphAdaptiveBatchSources.P,WindowPrefixProgram.prefixLength]
  omega

#print axioms cap_size
#print axioms selected_groups
#print axioms raw_eq
#print axioms raw_size
#print axioms window_size
#print axioms leaf_size
#print axioms leaf_size_le
end ThinMatrix.HalfSourceAdaptiveWidths
