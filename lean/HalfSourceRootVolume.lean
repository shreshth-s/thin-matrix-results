import HalfSourceChannelTypes

/-! Rounded full distinguished-root volume, including all retained channel
keys. The dense raw root arrays are allowed here and are charged separately
from prefix completion. -/
namespace ThinMatrix.HalfSourceRootVolume
open HalfSourceParameters
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem channelCount_bound (m : ℕ) (hm : 0 < m) :
    (ResidualFamilyKeys.channelCount m (OptimizedFoldedPlan.channelLength m):ℝ) ≤
      (m+1:ℝ)*(((4:ℝ)^m)^Q) := by
  let t := OptimizedFoldedPlan.channelLength m
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have htheta : (0:ℝ)< theta := by norm_num [theta]
  have ht : 0< t := by
    dsimp [t]
    rw [OptimizedFoldedPlan.channelLength_eq,Nat.ceil_pos]
    change 0<2*theta*(m:ℝ)
    positivity
  have htceil : ((t-1:ℕ):ℝ)<2*theta*(m:ℝ) := by
    apply Nat.lt_ceil.mp
    rw [show theta=OptimizedFoldedPlan.theta by rfl,← OptimizedFoldedPlan.channelLength_eq]
    change t-1< t
    omega
  have hp : ((t-1:ℕ):ℝ)/(2*m) ≤ theta := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*m)).mpr
    linarith
  have hp0 : 0 ≤ ((t-1:ℕ):ℝ)/(2*m) := by positivity
  have hthetaHalf : theta < (1:ℝ)/2 := by norm_num [theta]
  have hH := Real.binEntropy_strictMonoOn.monotoneOn
    (show ((t-1:ℕ):ℝ)/(2*m)∈Set.Icc (0:ℝ) (2⁻¹) from ⟨hp0,by norm_num; linarith⟩)
    (show theta∈Set.Icc (0:ℝ) (2⁻¹) from ⟨htheta.le,by norm_num; linarith⟩) hp
  have htail := (EntropyBounds.channelTail_entropy (2*m) (t-1) (by omega)
    (by push_cast; linarith : ((t-1:ℕ):ℝ)/(2*m:ℕ)≤1/2)).2
  have hc : (ResidualFamilyKeys.channelCount m t:ℝ)=EntropyBounds.channelTail (2*m) (t-1) := by
    rw [ResidualFamilyKeys.channelCount_sum]
    unfold EntropyBounds.channelTail
    rw [Nat.sub_add_cancel (by omega : 1≤ t)]
    simp only [Nat.cast_sum]
  have hexp : Real.exp ((2*m:ℕ)*Real.binEntropy (((t-1:ℕ):ℝ)/(2*m:ℕ)))≤
      ((4:ℝ)^m)^Q := by
    rw [Real.rpow_def_of_pos (by positivity),Real.log_pow]
    apply Real.exp_le_exp.mpr
    have he : (m:ℝ)*Real.log 4*Q=2*(m:ℝ)*Real.binEntropy theta := by
      unfold Q entropy RealCertificate.entropy
      rw [EntropyBounds.binEntropy_eq]
      field_simp
    rw [he]
    push_cast
    exact mul_le_mul_of_nonneg_left hH (by positivity)
  have htM : (t-1:ℕ)+1 ≤ m+1 := by have := OptimizedFoldedPlan.channelLength_upper m; dsimp [t] at *; omega
  rw [hc]
  calc
    _ ≤ ((t-1:ℕ)+1:ℝ)*Real.exp ((2*m:ℕ)*Real.binEntropy (((t-1:ℕ):ℝ)/(2*m:ℕ))) := htail
    _ ≤ (m+1:ℝ)*(((4:ℝ)^m)^Q) := by gcongr; exact_mod_cast (Nat.le_of_add_le_add_right htM)

def rawRatio (m : ℕ) : ℝ :=
  (3:ℝ)^(2*(OptimizedFoldedPlan.ordinaryLength m-m)+m)/(4:ℝ)^(2*(OptimizedFoldedPlan.ordinaryLength m-m))
def ratioExponent : ℝ := (2*c-1)*Real.log 3/Real.log 4-2*(c-1)

theorem rawRatio_bound (m : ℕ) : rawRatio m ≤ ((4:ℝ)^m)^ratioExponent := by
  have hk : (c-1)*(m:ℝ) ≤ (OptimizedFoldedPlan.ordinaryLength m-m:ℕ) := by
    have hl := (OptimizedFoldedPlan.rounded_bounds m).1
    have hcEq : OptimizedFoldedPlan.c=c := by norm_num [OptimizedFoldedPlan.c,c]
    rw [hcEq] at hl
    rw [Nat.cast_sub (OptimizedFoldedPlan.ordinaryLength_lower m)]
    linarith
  have hlog4 : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hlog : Real.log 3-Real.log 4≤0 := sub_nonpos.mpr (Real.log_le_log (by norm_num) (by norm_num))
  have hmul := mul_le_mul_of_nonpos_right hk hlog
  unfold rawRatio
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow,
    Real.log_rpow (by positivity),Real.log_pow]
  push_cast
  have he : ratioExponent*((m:ℝ)*Real.log 4)=
      2*((c-1)*(m:ℝ))*(Real.log 3-Real.log 4)+(m:ℝ)*Real.log 3 := by
    unfold ratioExponent
    field_simp
    ring
  rw [he]
  nlinarith only [hmul]

def rootVolume (m : ℕ) : ℕ :=
  (OptimizedFoldedPlan.ordinaryLength m).choose m^2*
    ResidualFamilyKeys.channelCount m (OptimizedFoldedPlan.channelLength m)*
    3^(2*(OptimizedFoldedPlan.ordinaryLength m-m)+m)

theorem rootVolume_factor (m : ℕ) : (rootVolume m:ℝ)=
    (EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m)^2*
      (ResidualFamilyKeys.channelCount m (OptimizedFoldedPlan.channelLength m):ℝ)*rawRatio m := by
  unfold rootVolume EntropyBounds.gridCount rawRatio
  push_cast
  rw [mul_comm 2 (OptimizedFoldedPlan.ordinaryLength m-m),pow_mul]
  field_simp

theorem rootExponent_identity : 2*T+Q+ratioExponent=T+Eroot := by
  unfold Eroot T CK ratioExponent
  ring

def rootConstant : ℝ := (Real.exp (Real.log 4+Real.log (c/(c-1))))^2

theorem rootVolume_bound (m : ℕ) (hm : 0< m) :
    (rootVolume m:ℝ)≤rootConstant*(m+1:ℝ)*(((4:ℝ)^m)^(T+Eroot)) := by
  have hc : 1< c := by norm_num [c]
  have hcEq : OptimizedFoldedPlan.c=c := by norm_num [OptimizedFoldedPlan.c,c]
  have hT : EntropyBounds.tileExponent c=T := by
    unfold EntropyBounds.tileExponent T CK
    rw [EntropyBounds.binEntropy_eq]
    unfold entropy RealCertificate.entropy
    ring
  have hg := (EntropyBounds.rounded_gridCount c m hc hm).2
  rw [← hcEq,← OptimizedFoldedPlan.ordinaryLength_eq,hcEq,hT] at hg
  have hg0 : 0≤EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m := by
    unfold EntropyBounds.gridCount
    positivity
  have hgSq : EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m^2≤
      (Real.exp (Real.log 4+Real.log (c/(c-1)))*((4:ℝ)^m)^T)^2 := by
    nlinarith [sq_nonneg (Real.exp (Real.log 4+Real.log (c/(c-1)))*((4:ℝ)^m)^T-
      EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m)]
  have hc0 : (0:ℝ)≤ResidualFamilyKeys.channelCount m (OptimizedFoldedPlan.channelLength m) := by positivity
  have hr0 : 0≤rawRatio m := by unfold rawRatio; positivity
  have h1 := mul_le_mul hgSq (channelCount_bound m hm) hc0 (by positivity)
  have h2 := mul_le_mul h1 (rawRatio_bound m) hr0 (by positivity)
  rw [rootVolume_factor]
  apply h2.trans_eq
  unfold rootConstant
  rw [← rootExponent_identity,
    Real.rpow_add (by positivity),Real.rpow_add (by positivity),
    show (2:ℝ)*T=T+T by ring,Real.rpow_add (by positivity)]
  ring

#print axioms channelCount_bound
#print axioms rawRatio_bound
#print axioms rootVolume_factor
#print axioms rootExponent_identity
#print axioms rootVolume_bound
end
end ThinMatrix.HalfSourceRootVolume
