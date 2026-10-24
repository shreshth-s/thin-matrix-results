import HalfSourceBandVolume
import HighBoxEntropy
import BinaryCroppedHighBoxes

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace ThinMatrix.HalfSourceHighVolume
open HalfSourceParameters
noncomputable section

 theorem saving_eq : HighBoxEntropy.boxSaving c theta=G := by
  unfold HighBoxEntropy.boxSaving G entropy RealCertificate.entropy
  rw [EntropyBounds.binEntropy_eq,EntropyBounds.binEntropy_eq]

 theorem tile_eq : EntropyBounds.tileExponent c=T := by
  unfold EntropyBounds.tileExponent T CK entropy RealCertificate.entropy
  rw [EntropyBounds.binEntropy_eq]
  ring

 def gridConstant : ℝ := Real.exp (Real.log 4+Real.log (c/(c-1)))
 def boxConstant : ℝ := Real.exp (HighBoxEntropy.roundingConstant c theta)*gridConstant^2

 theorem grid_upper (m : ℕ) (hm : 0 < m) :
    EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m ≤ gridConstant*((4:ℝ)^m)^T := by
  have hh := (EntropyBounds.rounded_gridCount c m (by norm_num [c]) hm).2
  have he : c=OptimizedFoldedPlan.c := by norm_num [c,OptimizedFoldedPlan.c]
  rw [he,← OptimizedFoldedPlan.ordinaryLength_eq,← he,tile_eq] at hh
  exact hh

 theorem base_grid (m : ℕ) (hm : 0 < m) :
    (HighBaseEncoder.baseCount (OptimizedFoldedPlan.ordinaryLength m) m (OptimizedFoldedPlan.channelLength m):ℝ) ≤
      (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^4*Real.exp (HighBoxEntropy.roundingConstant c theta)*
        (EntropyBounds.gridCount (OptimizedFoldedPlan.ordinaryLength m) m)^2*((4:ℝ)^m)^(-G) := by
  have hh := HighBoxEntropy.rounded_totalCappedLeaves_polynomial c theta m
    (by norm_num [c]) (by norm_num [theta]) (by norm_num [theta]) hm
  have hc : c=OptimizedFoldedPlan.c := by norm_num [c,OptimizedFoldedPlan.c]
  have ht : theta=OptimizedFoldedPlan.theta := by norm_num [theta,OptimizedFoldedPlan.theta]
  dsimp only at hh
  rw [hc,ht,←OptimizedFoldedPlan.ordinaryLength_eq,←OptimizedFoldedPlan.channelLength_eq,←hc,←ht,saving_eq] at hh
  unfold HighBaseEncoder.baseCount
  rw [Fintype.card_congr (HighBoxDP.baseStatesEquivTotalCapped _ _ _)]
  exact hh

 theorem base_exponent (m : ℕ) (hm : 0 < m) :
    (HighBaseEncoder.baseCount (OptimizedFoldedPlan.ordinaryLength m) m (OptimizedFoldedPlan.channelLength m):ℝ) ≤
      (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^4*boxConstant*((4:ℝ)^m)^(2*T-G) := by
  have hg := grid_upper m hm
  have hsq := sq_le_sq₀ (by unfold EntropyBounds.gridCount; positivity) (by unfold gridConstant; positivity) |>.mpr hg
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^4*Real.exp (HighBoxEntropy.roundingConstant c theta) by positivity))
    (show 0 ≤ ((4:ℝ)^m)^(-G) by positivity)
  refine (base_grid m hm).trans (h.trans_eq ?_)
  have hp : ((4:ℝ)^m)^T*((4:ℝ)^m)^T*((4:ℝ)^m)^(-G)=((4:ℝ)^m)^(2*T-G) := by
    rw [←Real.rpow_add (by positivity),←Real.rpow_add (by positivity)]
    congr 1
    ring
  unfold boxConstant
  rw [mul_pow]
  calc
    _ = ((OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^4*Real.exp (HighBoxEntropy.roundingConstant c theta)*gridConstant^2)*
      (((4:ℝ)^m)^T*((4:ℝ)^m)^T*((4:ℝ)^m)^(-G)) := by ring
    _ = _ := by rw [hp]; ring

 theorem encoder_bands (N m : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      (HighBaseEncoder.baseCount (OptimizedFoldedPlan.ordinaryLength m) m (OptimizedFoldedPlan.channelLength m):ℝ) ≤
        32*N*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^5*boxConstant*((4:ℝ)^m)^Ebox := by
  have hh := HalfSourceBandVolume.transfer N m hm hfit _ _ Ebox
    (show 0 ≤ (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^4*boxConstant by unfold boxConstant gridConstant; positivity)
    (by convert base_exponent m hm using 1; unfold Ebox; ring)
  convert hh using 1; ring

 theorem pair_bands (N m : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)^2*
      (HighBaseEncoder.baseCount (OptimizedFoldedPlan.ordinaryLength m) m (OptimizedFoldedPlan.channelLength m):ℝ) ≤
        1024*N^2*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^6*boxConstant*((4:ℝ)^m)^(-G) := by
  let bands : ℝ := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m)
  let D : ℝ := (4:ℝ)^m
  let F : ℝ := (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)^4*boxConstant
  have hb := HalfSourceBandVolume.bandCount_dimension N m hm hfit
  have hb2 : (bands*D^T)^2 ≤ (32*N*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ))^2 := by
    apply (sq_le_sq₀ (by dsimp [bands,D]; positivity) (by positivity)).mpr
    exact hb
  have he : D^(2*T-G)=D^T*D^T*D^(-G) := by
    rw [←Real.rpow_add (by dsimp [D]; positivity),←Real.rpow_add (by dsimp [D]; positivity)]
    congr 1
    ring
  have hv := mul_le_mul_of_nonneg_left (base_exponent m hm) (sq_nonneg bands)
  have hs := mul_le_mul_of_nonneg_right hb2 (show 0 ≤ F*D^(-G) by dsimp [F,boxConstant,gridConstant,D]; positivity)
  change bands^2*_ ≤ _
  change bands^2*_ ≤ bands^2*(F*D^(2*T-G)) at hv
  rw [he] at hv
  dsimp only [F,D] at hs
  nlinarith only [hv,hs]

#print axioms saving_eq
#print axioms tile_eq
#print axioms grid_upper
#print axioms base_grid
#print axioms base_exponent
#print axioms encoder_bands
#print axioms pair_bands
end
end ThinMatrix.HalfSourceHighVolume
