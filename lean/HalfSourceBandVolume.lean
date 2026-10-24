import HalfSourceRootVolume
import BackendCostRefinement

/-! Convert per-band half-source volumes to their actual retained-band
cost. Good-mask density and both integer ceiling losses are charged. -/
namespace ThinMatrix.HalfSourceBandVolume
open HalfSourceParameters
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem bandCount_dimension (N m : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      (((4:ℝ)^m)^T) ≤ 32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ) := by
  let L := OptimizedFoldedPlan.ordinaryLength m
  let bands := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth L m)
  have hmL : m ≤ L := OptimizedFoldedPlan.ordinaryLength_lower m
  have hcount := BackendCostRefinement.actual_bandCount_le N L m hmL
  have hpad := TilingCosts.padding_upper N (ThinProductCosts.gridSide L m)
    (ThinProductCosts.gridSide_pos L m hmL) hfit
  have hb : bands*ThinProductCosts.gridSide L m ≤ 32*N := by
    have hx := Nat.mul_le_mul_right (ThinProductCosts.gridSide L m) hcount
    unfold TilingCosts.paddedSize at hpad
    dsimp [bands]
    nlinarith only [hx,hpad]
  have hc : 1 < c := by norm_num [c]
  have hcEq : OptimizedFoldedPlan.c=c := by norm_num [OptimizedFoldedPlan.c,c]
  have hT : EntropyBounds.tileExponent c=T := by
    unfold EntropyBounds.tileExponent T CK
    rw [EntropyBounds.binEntropy_eq]
    unfold entropy RealCertificate.entropy
    ring
  have hgrid := (EntropyBounds.rounded_gridCount c m hc hm).1
  rw [← hcEq,← OptimizedFoldedPlan.ordinaryLength_eq,hcEq,hT] at hgrid
  have hgrid' : ((4:ℝ)^m)^T≤EntropyBounds.gridCount L m*(L+1:ℝ) :=
    (div_le_iff₀ (by positivity)).mp hgrid
  have hscaled := mul_le_mul_of_nonneg_left hgrid' (Nat.cast_nonneg bands)
  have hbR : (bands:ℝ)*EntropyBounds.gridCount L m≤32*(N:ℝ) := by
    rw [← ThinProductCosts.gridSide_cast]
    exact_mod_cast hb
  change (bands:ℝ)*(((4:ℝ)^m)^T) ≤ _
  have hmul := mul_le_mul_of_nonneg_right hbR (show 0≤(L+1:ℝ) by positivity)
  calc
    _ ≤ (bands:ℝ)*(EntropyBounds.gridCount L m*(L+1:ℝ)) := hscaled
    _ = ((bands:ℝ)*EntropyBounds.gridCount L m)*(L+1:ℝ) := by ring
    _ ≤ _ := hmul

/-- Any concrete per-band counter with the displayed monomial bound loses
one geometry exponent when the retained sources are built once per band. -/
theorem transfer (N m : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N)
    (F V exponent : ℝ) (hF : 0 ≤ F) (hV : V ≤ F*(((4:ℝ)^m)^(T+exponent))) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*V ≤
      32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*F*(((4:ℝ)^m)^exponent) := by
  let bands := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m)
  have hv := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg bands)
  have hb := mul_le_mul_of_nonneg_right (bandCount_dimension N m hm hfit)
    (show 0≤F*(((4:ℝ)^m)^exponent) by positivity)
  rw [Real.rpow_add (by positivity)] at hv
  change (bands:ℝ)*V≤_
  calc
    _ ≤ (bands:ℝ)*(F*(((4:ℝ)^m)^T*((4:ℝ)^m)^exponent)) := hv
    _ = ((bands:ℝ)*((4:ℝ)^m)^T)*(F*((4:ℝ)^m)^exponent) := by ring
    _ ≤ _ := hb
    _ = _ := by ring

theorem root_cost (N m : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      HalfSourceRootVolume.rootVolume m ≤
      32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*
        (HalfSourceRootVolume.rootConstant*(m+1:ℝ))*(((4:ℝ)^m)^Eroot) :=
  transfer N m hm hfit _ _ _ (by unfold HalfSourceRootVolume.rootConstant; positivity)
    (HalfSourceRootVolume.rootVolume_bound m hm)

theorem completion_cost (N m : ℕ) (hm : 32 ≤ m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      (HalfSourceGroupVolume.groupCount m:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta)) ≤
      32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*
        (HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2)*(((4:ℝ)^m)^E) := by
  have h := transfer N m (by omega) hfit _ _ _
    (show 0≤HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2 by unfold HalfSourceGroupVolume.groupConstant; positivity)
    (HalfSourceGroupVolume.completion_volume_bound m hm)
  simpa only [mul_assoc] using h

#print axioms bandCount_dimension
#print axioms transfer
#print axioms root_cost
#print axioms completion_cost
end
end ThinMatrix.HalfSourceBandVolume
