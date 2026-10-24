import HalfSourceTypeCounts

/-! Explicit finite group volume at the actual selected suffix lengths.
Every ordered channel type and every good-mask pair is included. Pair-bit
groups and prefix ordinary outputs are counted separately from support-vector
length; the latter is paid in the completion exponent identity. -/
namespace ThinMatrix.HalfSourceGroupVolume
open HalfSourceParameters HalfSourceTypeCounts HalfSourceSuffixChoice
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def suffixLength (m cn co : ℕ) : ℕ := forType (OptimizedFoldedPlan.ordinaryLength m) m cn co

def typeGroups (m cn co : ℕ) : ℕ := if cn+co < OptimizedFoldedPlan.channelLength m then
  m.choose cn*m.choose co*4^(2*(OptimizedFoldedPlan.ordinaryLength m-m)-suffixLength m cn co)*2^(suffixLength m cn co)
  else 0

def groupCount (m : ℕ) : ℕ := (OptimizedFoldedPlan.ordinaryLength m).choose m^2*
  (∑ cn ∈ Finset.range (m+1), ∑ co ∈ Finset.range (m+1), typeGroups m cn co)

theorem suffix_factor (k ell : ℕ) (hell : ell ≤ k) :
    (4:ℝ)^(2*k-ell)*(2:ℝ)^ell=(4:ℝ)^(2*k)*(2:ℝ)^(-(ell:ℝ)) := by
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow,Real.log_rpow (by norm_num : (0:ℝ)<2),
    Nat.cast_sub (by omega : ell ≤ 2*k),Nat.cast_mul,Nat.cast_ofNat,RealCertificate.logFour]
  ring

theorem typeGroups_factor (m cn co : ℕ) :
    (typeGroups m cn co:ℝ)=(4:ℝ)^(2*(OptimizedFoldedPlan.ordinaryLength m-m))*typeMass m cn co := by
  have hell := (forType_fit (OptimizedFoldedPlan.ordinaryLength m) m cn co).1
  unfold typeGroups typeMass suffixLength
  split_ifs with ht
  · push_cast
    calc
      _ = (m.choose cn:ℝ)*(m.choose co:ℝ)*
        ((4:ℝ)^(2*(OptimizedFoldedPlan.ordinaryLength m-m)-forType (OptimizedFoldedPlan.ordinaryLength m) m cn co)*
          2^forType (OptimizedFoldedPlan.ordinaryLength m) m cn co) := by ring
      _ = _ := by rw [suffix_factor _ _ hell]; ring
  · simp

theorem groupCount_factor (m : ℕ) :
    (groupCount m:ℝ)=EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m^2*
      (∑ cn ∈ Finset.range (m+1), ∑ co ∈ Finset.range (m+1), typeMass m cn co) := by
  unfold groupCount
  push_cast
  simp_rw [typeGroups_factor]
  simp_rw [← Finset.mul_sum]
  unfold EntropyBounds.gridCount
  rw [mul_comm 2 (OptimizedFoldedPlan.ordinaryLength m-m),pow_mul]
  ring

def groupConstant : ℝ := 2*(Real.exp (Real.log 4+Real.log (c/(c-1))))^2

theorem typeMass_nonnegative (m cn co : ℕ) : 0 ≤ typeMass m cn co := by
  unfold typeMass
  split_ifs <;> positivity

/-- Explicit finite (L3) group bound. The only tensor-parameter overhead is
quadratic; the remaining factor is a fixed real constant. -/
theorem groupCount_bound (m : ℕ) (hm : 32 ≤ m) :
    (groupCount m:ℝ) ≤ groupConstant*(m+1:ℝ)^2*
      (((4:ℝ)^m)^(2*T+Q-zeta/(2*gamt))) := by
  have hm0 : 0 < m := by omega
  have hc : 1 < c := by norm_num [c]
  have hcEq : OptimizedFoldedPlan.c=c := by norm_num [OptimizedFoldedPlan.c,c]
  have hT : EntropyBounds.tileExponent c=T := by
    unfold EntropyBounds.tileExponent T CK
    rw [EntropyBounds.binEntropy_eq]
    unfold entropy RealCertificate.entropy
    ring
  have hg := (EntropyBounds.rounded_gridCount c m hc hm0).2
  rw [← hcEq,← OptimizedFoldedPlan.ordinaryLength_eq,hcEq,hT] at hg
  have hg0 : 0 ≤ EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m := by
    unfold EntropyBounds.gridCount
    positivity
  have hgSq : EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m^2 ≤
      (Real.exp (Real.log 4+Real.log (c/(c-1)))*((4:ℝ)^m)^T)^2 := by
    nlinarith [sq_nonneg (Real.exp (Real.log 4+Real.log (c/(c-1)))*((4:ℝ)^m)^T-
      EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m)]
  have hs0 : 0 ≤ ∑ cn ∈ Finset.range (m+1), ∑ co ∈ Finset.range (m+1), typeMass m cn co := by
    exact Finset.sum_nonneg fun cn _ => Finset.sum_nonneg fun co _ => typeMass_nonnegative m cn co
  have hh := mul_le_mul hgSq (all_types_bound m hm) hs0 (by positivity)
  rw [groupCount_factor]
  apply hh.trans_eq
  unfold groupConstant
  rw [show 2*T+Q-zeta/(2*gamt)=T+T+(Q-zeta/(2*gamt)) by ring,
    Real.rpow_add (by positivity),Real.rpow_add (by positivity)]
  ring

/-- Multiplying the group count by the rectangular completion's support
charge gives exactly the canonical per-band residual exponent. -/
theorem completion_exponent_identity :
    (2*T+Q-zeta/(2*gamt))+(1+alpha)*zeta=T+E := by
  unfold E A
  field_simp
  ring

theorem completion_volume_bound (m : ℕ) (hm : 32 ≤ m) :
    (groupCount m:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta)) ≤
      groupConstant*(m+1:ℝ)^2*(((4:ℝ)^m)^(T+E)) := by
  have h := mul_le_mul_of_nonneg_right (groupCount_bound m hm)
    (show 0 ≤ ((4:ℝ)^m)^((1+alpha)*zeta) by positivity)
  apply h.trans_eq
  rw [mul_assoc (groupConstant*(m+1:ℝ)^2),← Real.rpow_add (by positivity),completion_exponent_identity]

#print axioms suffix_factor
#print axioms typeGroups_factor
#print axioms groupCount_factor
#print axioms groupCount_bound
#print axioms completion_exponent_identity
#print axioms completion_volume_bound
end
end ThinMatrix.HalfSourceGroupVolume
