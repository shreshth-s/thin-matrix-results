import HalfSourceRootVolume
import HalfSourceActualVolumes
import HalfSourceAdaptiveFamilyCost

/-! Empty routed rows still have constant traversal/output costs. The full
band-pair/mask/channel index space fits the box charge, so no empty-case
cost is silently dropped when the selected coefficient contraction is used. -/
namespace ThinMatrix.HalfSourceEmptyRootCost
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
noncomputable section
set_option maxHeartbeats 3000000
attribute [local irreducible] GoodMapEmbedding.goodSlots OptimizedFoldedPlan.ordinaryLength

def count (N m : ℕ) : ℕ :=
  (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m))^2*
    (GoodMapEmbedding.goodSlots (L m) m).card^2*ResidualFamilyKeys.channelCount m (t m)

theorem tile_le (m : ℕ) : ThinMatrixBackend.tileWidth (L m) m≤ThinProductCosts.gridSide (L m) m := by
  exact Nat.mul_le_mul_right _ (HalfSourceActualVolumes.good_count _ _)

theorem channel_box_weight (m : ℕ) (hm : 0 < m) :
    (ResidualFamilyKeys.channelCount m (t m):ℝ)*(((4:ℝ)^m)^G)≤
      (m+1:ℝ)*(4:ℝ)^(2*(L m-m)) := by
  have hc := HalfSourceRootVolume.channelCount_bound m hm
  have hg : Q+G≤2*(c-1) := by
    have hc : 9<c := by norm_num[c]
    linarith [QEnclosure.2,GEnclosure.2]
  have hd : 1≤(4:ℝ)^m := one_le_pow₀ (by norm_num)
  have hmL : m≤L m := OptimizedFoldedPlan.ordinaryLength_lower m
  have hL := (OptimizedFoldedPlan.rounded_bounds m).1
  have hk : (c-1)*(m:ℝ)≤((L m-m:ℕ):ℝ) := by
    rw [Nat.cast_sub hmL]
    change OptimizedFoldedPlan.c*(m:ℝ)≤(L m:ℝ) at hL
    have he : OptimizedFoldedPlan.c=c := by norm_num[OptimizedFoldedPlan.c,c]
    rw [he] at hL
    linarith
  have hpow : ((4:ℝ)^m)^(2*(c-1))≤(4:ℝ)^(2*(L m-m)) := by
    rw [←Real.rpow_natCast (4:ℝ) m,←Real.rpow_mul (by norm_num)]
    rw [←Real.rpow_natCast (4:ℝ) (2*(L m-m))]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  calc
    _ ≤((m+1:ℝ)*(((4:ℝ)^m)^Q))*(((4:ℝ)^m)^G) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ =(m+1:ℝ)*(((4:ℝ)^m)^(Q+G)) := by rw[Real.rpow_add (by positivity)];ring
    _ ≤(m+1:ℝ)*(((4:ℝ)^m)^(2*(c-1))) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem count_bound (N m : ℕ) (hm : 0 < m) (hfit : ThinProductCosts.gridSide (L m) m≤N) :
    (count N m:ℝ)≤4*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G)) := by
  let B := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  let K := (GoodMapEmbedding.goodSlots (L m) m).card
  have ht := TilingCosts.padding_upper N (ThinMatrixBackend.tileWidth (L m) m)
    (ThinMatrixBackend.tileWidth_pos _ _ (OptimizedFoldedPlan.ordinaryLength_lower m)) ((tile_le m).trans hfit)
  have htR : (B:ℝ)*(K:ℝ)*(4:ℝ)^(L m-m)≤2*(N:ℝ) := by
    change B*(K*4^(L m-m))≤2*N at ht
    exact_mod_cast (show B*K*4^(L m-m)≤2*N by nlinarith only [ht])
  have ht2 := pow_le_pow_left₀ (by positivity : 0≤(B:ℝ)*(K:ℝ)*(4:ℝ)^(L m-m)) htR 2
  have hvolume : (B:ℝ)^2*(K:ℝ)^2*(4:ℝ)^(2*(L m-m))≤4*(N:ℝ)^2 := by
    rw [show 2*(L m-m)=(L m-m)*2 by omega,pow_mul]
    nlinarith only [ht2]
  have hc := channel_box_weight m hm
  have hweighted : (count N m:ℝ)*(((4:ℝ)^m)^G)≤4*(N:ℝ)^2*(m+1:ℝ) := by
    unfold count
    push_cast
    calc
      _ =(B:ℝ)^2*(K:ℝ)^2*((ResidualFamilyKeys.channelCount m (t m):ℝ)*(((4:ℝ)^m)^G)) := by dsimp[B,K];ring
      _ ≤(B:ℝ)^2*(K:ℝ)^2*((m+1:ℝ)*(4:ℝ)^(2*(L m-m))) := by gcongr
      _ =((B:ℝ)^2*(K:ℝ)^2*(4:ℝ)^(2*(L m-m)))*(m+1:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hvolume (by positivity)
  have hh := mul_le_mul_of_nonneg_right hweighted (show 0≤((4:ℝ)^m)^(-G) by positivity)
  simpa only [mul_assoc,←Real.rpow_add (by positivity : 0<(4:ℝ)^m),add_neg_cancel,Real.rpow_zero,mul_one] using hh

#print axioms tile_le
#print axioms channel_box_weight
#print axioms count_bound
end
end ThinMatrix.HalfSourceEmptyRootCost
