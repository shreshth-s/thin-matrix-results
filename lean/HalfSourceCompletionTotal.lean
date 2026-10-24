import HalfSourceCompletionVolume

/-! Sum the two proved rectangular-completion monomials over every own-band
source, channel type, window, degree run and translation pair. The cyclic
column count remains B*(m+1)*q. -/
namespace ThinMatrix.HalfSourceCompletionTotal
open HalfSourceParameters HalfSourceAdaptiveFamilyCost HalfSourceCompletionVolume
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

def constant : ℝ := 212992*(26+281216*HalfSourceGroupVolume.groupConstant)

theorem constant_pos : 0 < constant := by
  unfold constant HalfSourceGroupVolume.groupConstant
  positivity

theorem total_rate {I : Type} [Fintype I] (N m M B q : ℕ) (hm : 32 ≤ m)
    (hfit : ThinProductCosts.gridSide (L m) m ≤ N) (count : I → ℕ) (htotal : ∑ i,count i=M)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : keys.toList=(ResidualFamilyKeys.channels m (t m)).value) :
    (repetitions m:ℝ)*(B*((m+1)*q):ℕ)*
      (queryVolume m count keys+
       (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
         (HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ)^(1+alpha)) ≤
      constant*(B:ℝ)*(q:ℝ)*(m+1:ℝ)^14*
        ((M:ℝ)*(((4:ℝ)^m)^q1)+(N:ℝ)*(((4:ℝ)^m)^E)) := by
  have hq := query_partition m M count htotal keys (by omega)
  have hg := own_padding N m hm hfit keys hk
  have hr := repetitions_bound m
  have hrR : (repetitions m:ℝ) ≤ 212992*(m+1:ℝ)^8 := by exact_mod_cast hr
  have hp : (m+1:ℝ)^2 ≤ (m+1:ℝ)^5 := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) m;linarith) (by decide)
  have hc : 0 ≤ HalfSourceGroupVolume.groupConstant := by unfold HalfSourceGroupVolume.groupConstant;positivity
  have hquery : 0 ≤ queryVolume m count keys := by unfold queryVolume;positivity
  have hs : queryVolume m count keys+
      (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
        (HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ)^(1+alpha) ≤
      (26+281216*HalfSourceGroupVolume.groupConstant)*(m+1:ℝ)^5*
        ((M:ℝ)*(((4:ℝ)^m)^q1)+(N:ℝ)*(((4:ℝ)^m)^E)) := by
    have hq' : queryVolume m count keys ≤ 26*(M:ℝ)*(m+1:ℝ)^5*(((4:ℝ)^m)^q1) := hq.trans (by gcongr)
    nlinarith only [hq',hg,mul_nonneg (show 0≤281216*HalfSourceGroupVolume.groupConstant by positivity)
      (show 0≤(m+1:ℝ)^5*((M:ℝ)*(((4:ℝ)^m)^q1)) by positivity),
      show 0≤26*(m+1:ℝ)^5*((N:ℝ)*(((4:ℝ)^m)^E)) by positivity]
  calc
    _ ≤ (212992*(m+1:ℝ)^8)*(B*((m+1)*q):ℕ)*
      ((26+281216*HalfSourceGroupVolume.groupConstant)*(m+1:ℝ)^5*
        ((M:ℝ)*(((4:ℝ)^m)^q1)+(N:ℝ)*(((4:ℝ)^m)^E))) := by gcongr
    _ = _ := by unfold constant;push_cast;ring

theorem channel_q1 (m : ℕ) (hm : 0 < m) :
    (ResidualFamilyKeys.channelCount m (t m):ℝ) ≤ (m+1:ℝ)*(((4:ℝ)^m)^q1) := by
  have hh := HalfSourceRootVolume.channelCount_bound m hm
  have he : Q ≤ q1 := by unfold q1;norm_num[beta,zeta]
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) he) (by positivity))

#print axioms constant_pos
#print axioms total_rate
#print axioms channel_q1
end
end ThinMatrix.HalfSourceCompletionTotal
