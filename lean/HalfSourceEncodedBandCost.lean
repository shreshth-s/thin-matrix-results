import HalfSourceEncodedProduction
import HalfSourceAdaptiveBandCost

namespace ThinMatrix.HalfSourceEncodedBandCost
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

 theorem group_source (m : ℕ) (hm : 32 ≤ m) :
    (HalfSourceGroupVolume.groupCount m:ℝ)*(cap m:ℝ)≤
      26*HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^3*(((4:ℝ)^m)^(T+E)) := by
  have hc := HalfSourceAdaptiveBandCost.cap_completion m
  have hg := HalfSourceGroupVolume.completion_volume_bound m hm
  calc
    _ ≤(HalfSourceGroupVolume.groupCount m:ℝ)*(26*(m+1:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta))) := by gcongr
    _ =26*(m+1:ℝ)*((HalfSourceGroupVolume.groupCount m:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta))) := by ring
    _ ≤26*(m+1:ℝ)*(HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2*(((4:ℝ)^m)^(T+E))) := mul_le_mul_of_nonneg_left hg (by positivity)
    _ =_ := by ring

 theorem budget_bands (N m q : ℕ) (hm : 32 ≤ m)
    (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*(HalfSourceEncodedProduction.budget m q:ℝ)≤
      (1000000000000000000000000000*HalfSourceAdaptiveBandCost.constant)*(q:ℝ)*(N:ℝ)*(m+1:ℝ)^16*
        ((((4:ℝ)^m)^Eroot)+(((4:ℝ)^m)^E)) := by
  have hr := HalfSourceActualVolumes.roots_bands_bound N m (by omega) hfit
  have hg := HalfSourceBandVolume.transfer N m (by omega) hfit
    (26*HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^3) _ E
    (by unfold HalfSourceGroupVolume.groupConstant;positivity) (group_source m hm)
  have hL : (L m+1:ℝ)≤13*(m+1:ℝ) := by
    have hh := HalfSourceRootPolynomials.ordinary_bound m
    exact_mod_cast(show L m+1≤13*(m+1) by dsimp[L];omega)
  have hCr : 0≤HalfSourceRootVolume.rootConstant := by unfold HalfSourceRootVolume.rootConstant;positivity
  have hCg : 0≤HalfSourceGroupVolume.groupConstant := by unfold HalfSourceGroupVolume.groupConstant;positivity
  have hpoly : (m+1:ℝ)^2≤(m+1:ℝ)^4 := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) m;linarith) (by decide)
  have hr' : (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*(HalfSourceActualVolumes.roots m:ℝ)≤
      416*HalfSourceRootVolume.rootConstant*(N:ℝ)*(m+1:ℝ)^4*(((4:ℝ)^m)^Eroot) := by
    calc
      _≤32*(N:ℝ)*(13*(m+1:ℝ))*(HalfSourceRootVolume.rootConstant*(m+1:ℝ))*(((4:ℝ)^m)^Eroot) := hr.trans (by gcongr)
      _=416*HalfSourceRootVolume.rootConstant*(N:ℝ)*(m+1:ℝ)^2*(((4:ℝ)^m)^Eroot) := by ring
      _≤_ := by gcongr
  have hg' : (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
      ((HalfSourceGroupVolume.groupCount m:ℝ)*(cap m:ℝ))≤
      416*(26*HalfSourceGroupVolume.groupConstant)*(N:ℝ)*(m+1:ℝ)^4*(((4:ℝ)^m)^E) := by
    calc
      _≤32*(N:ℝ)*(13*(m+1:ℝ))*(26*HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^3)*(((4:ℝ)^m)^E) := hg.trans (by gcongr)
      _=_ := by ring
  have hsum := add_le_add hr' hg'
  have hs : (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
      ((HalfSourceActualVolumes.roots m:ℝ)+(HalfSourceGroupVolume.groupCount m:ℝ)*(cap m:ℝ))≤
      416*HalfSourceAdaptiveBandCost.constant*(N:ℝ)*(m+1:ℝ)^4*
        ((((4:ℝ)^m)^Eroot)+(((4:ℝ)^m)^E)) := by
    unfold HalfSourceAdaptiveBandCost.constant
    nlinarith only[hsum,show 0≤416*HalfSourceRootVolume.rootConstant*(N:ℝ)*(m+1:ℝ)^4*(((4:ℝ)^m)^E) by positivity,
      show 0≤416*(26*HalfSourceGroupVolume.groupConstant)*(N:ℝ)*(m+1:ℝ)^4*(((4:ℝ)^m)^Eroot) by positivity]
  have hh := mul_le_mul_of_nonneg_left hs (show 0≤1000000000000000000000000*(q:ℝ)*(m+1:ℝ)^12 by positivity)
  unfold HalfSourceEncodedProduction.budget
  push_cast
  calc
    _≤(416*1000000000000000000000000)*HalfSourceAdaptiveBandCost.constant*(q:ℝ)*(N:ℝ)*(m+1:ℝ)^16*
      ((((4:ℝ)^m)^Eroot)+(((4:ℝ)^m)^E)) := by convert hh using 1 <;> first | rfl | ring
    _≤_ := by gcongr;exact HalfSourceAdaptiveBandCost.constant_nonneg;norm_num

#print axioms group_source
#print axioms budget_bands
end
end ThinMatrix.HalfSourceEncodedBandCost
