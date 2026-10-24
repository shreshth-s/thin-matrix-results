import HalfSourceAdaptivePolynomials
import HalfSourceBandVolume

/-! Selected support padding and actual accepted channel sums convert
retained adaptive encoders into exactly the residual and dense-root charges. -/
namespace ThinMatrix.HalfSourceAdaptiveBandCost
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem cap_bound (m : ℕ) : (cap m:ℝ)≤26*(m+1:ℝ)*(((4:ℝ)^m)^zeta) := by
  have hr := (ComputableParameters.roundedPower_bounds 11 50 (4^m)
    (by norm_num) (by norm_num) (by exact Nat.one_le_pow _ _ (by decide))).2
  have hr' : (ComputableParameters.roundedPower 11 50 (4^m):ℝ)≤2*(((4:ℝ)^m)^zeta) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,zeta] using hr
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hshape : ((L m-m+1:ℕ):ℝ)≤13*(m+1:ℝ) := by exact_mod_cast (show L m-m+1≤13*(m+1) by dsimp[L];omega)
  unfold cap HalfSourceSuffixChoice.limit
  rw [Nat.cast_mul]
  calc
    _ ≤(13*(m+1:ℝ))*(2*(((4:ℝ)^m)^zeta)) := mul_le_mul hshape hr' (by positivity) (by positivity)
    _ = _ := by ring

theorem cap_completion (m : ℕ) : (cap m:ℝ)≤26*(m+1:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta)) := by
  have hexp : zeta≤(1+alpha)*zeta := by norm_num[alpha,zeta]
  have hd : 1≤(4:ℝ)^m := one_le_pow₀ (by norm_num)
  exact (cap_bound m).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hd hexp) (by positivity))

def constant : ℝ := HalfSourceRootVolume.rootConstant+26*HalfSourceGroupVolume.groupConstant

theorem constant_nonneg : 0≤constant := by unfold constant HalfSourceRootVolume.rootConstant HalfSourceGroupVolume.groupConstant;positivity

theorem volume_bands (N m : ℕ) (hm : 32≤ m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m≤N)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : keys.toList=(ResidualFamilyKeys.channels m (t m)).value) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
      ((HalfSourceActualVolumes.roots m:ℝ)+(HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ))≤
      416*constant*(N:ℝ)*(m+1:ℝ)^4*
        ((((4:ℝ)^m)^Eroot)+(((4:ℝ)^m)^E)) := by
  let B : ℝ := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  let W : ℝ := m+1
  let R : ℝ := ((4:ℝ)^m)^Eroot
  let S : ℝ := ((4:ℝ)^m)^E
  let Cr := HalfSourceRootVolume.rootConstant
  let Cg := HalfSourceGroupVolume.groupConstant
  have hW : 1≤W := by dsimp[W];have := Nat.cast_nonneg (α:=ℝ) m;linarith
  have hR : 0≤R := by dsimp[R];positivity
  have hS : 0≤S := by dsimp[S];positivity
  have hCr : 0≤Cr := by dsimp[Cr,HalfSourceRootVolume.rootConstant];positivity
  have hCg : 0≤Cg := by dsimp[Cg,HalfSourceGroupVolume.groupConstant];positivity
  have hr := HalfSourceActualVolumes.roots_bands_bound N m (by omega) hfit
  have hg := HalfSourceActualVolumes.groups_bands_bound N m hm hfit keys hk
  have hc := cap_completion m
  have hgc : B*(HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ)≤
      26*W*(32*(N:ℝ)*(L m+1:ℝ)*(Cg*W^2)*S) := by
    calc
      _ ≤B*(HalfSourceActualVolumes.groups m keys:ℝ)*(26*W*(((4:ℝ)^m)^((1+alpha)*zeta))) := by
        exact mul_le_mul_of_nonneg_left hc (by dsimp[B];positivity)
      _ =26*W*(B*(HalfSourceActualVolumes.groups m keys:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hl : (L m+1:ℝ)≤13*W := by dsimp[W];exact_mod_cast (show L m+1≤13*(m+1) by dsimp[L];omega)
  have hr' : B*(HalfSourceActualVolumes.roots m:ℝ)≤416*(N:ℝ)*Cr*W^2*R := by
    calc
      _ ≤32*(N:ℝ)*(L m+1:ℝ)*(Cr*W)*R := hr
      _ ≤32*(N:ℝ)*(13*W)*(Cr*W)*R := by gcongr
      _ = _ := by ring
  have hg' : B*(HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ)≤416*(N:ℝ)*(26*Cg)*W^4*S := by
    calc
      _ ≤26*W*(32*(N:ℝ)*(L m+1:ℝ)*(Cg*W^2)*S) := hgc
      _ ≤26*W*(32*(N:ℝ)*(13*W)*(Cg*W^2)*S) := by gcongr
      _ = _ := by ring
  have hW2 : W^2≤W^4 := pow_le_pow_right₀ hW (by decide)
  have hr'' : B*(HalfSourceActualVolumes.roots m:ℝ)≤416*(N:ℝ)*Cr*W^4*R := hr'.trans (by gcongr)
  have hcross1 := mul_nonneg (show 0≤416*(N:ℝ)*Cr*W^4 by positivity) hS
  have hcross2 := mul_nonneg (show 0≤416*(N:ℝ)*(26*Cg)*W^4 by positivity) hR
  change B*((HalfSourceActualVolumes.roots m:ℝ)+(HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ))≤416*(Cr+26*Cg)*(N:ℝ)*W^4*(R+S)
  nlinarith only [hr'',hg',hcross1,hcross2]

theorem work_bands (N m q : ℕ) (hm : 32≤ m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m≤N)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : keys.toList=(ResidualFamilyKeys.channels m (t m)).value) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
      (1000000000000000000000000*(q:ℝ)*(m+1:ℝ)^12*
        ((HalfSourceActualVolumes.roots m:ℝ)+(HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ)))≤
      (1000000000000000000000000000*constant)*(q:ℝ)*(N:ℝ)*(m+1:ℝ)^16*
        ((((4:ℝ)^m)^Eroot)+(((4:ℝ)^m)^E)) := by
  have hh := mul_le_mul_of_nonneg_left (volume_bands N m hm hfit keys hk)
    (show 0≤1000000000000000000000000*(q:ℝ)*(m+1:ℝ)^12 by positivity)
  calc
    _ ≤(416*1000000000000000000000000)*constant*(q:ℝ)*(N:ℝ)*(m+1:ℝ)^16*
      ((((4:ℝ)^m)^Eroot)+(((4:ℝ)^m)^E)) := by
      ring_nf at hh ⊢
      exact hh
    _ ≤ _ := by gcongr;exact constant_nonneg;norm_num

#print axioms cap_bound
#print axioms cap_completion
#print axioms volume_bands
#print axioms work_bands
end
end ThinMatrix.HalfSourceAdaptiveBandCost
