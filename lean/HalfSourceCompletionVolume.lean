import HalfSourceRoutedQueryCost

/-! Count both terms of shared LOW completion over own-band sources.
The query term uses any proved stable partition of original occurrences;
the padded-group term pays each own-band/channel/window family once. -/
namespace ThinMatrix.HalfSourceCompletionVolume
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000

def queryVolume {I : Type} [Fintype I] (m : ℕ) (count : I → ℕ)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m))) : ℝ :=
  ∑ c,∑ i,(count i:ℝ)*
    (HalfSourceRoutedQueryCost.support m (CappedBitPreparation.ones (ResidualFamilyKeys.normal (keys.get c)))
      (CappedBitPreparation.ones (ResidualFamilyKeys.opposite (keys.get c))):ℝ)^beta

theorem query_partition {I : Type} [Fintype I] (m M : ℕ) (count : I → ℕ) (htotal : ∑ i,count i=M)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hm : 0 < m) : queryVolume m count keys≤26*(M:ℝ)*(m+1:ℝ)^2*(((4:ℝ)^m)^q1) := by
  have htR : (∑ i,(count i:ℝ))=(M:ℝ) := by exact_mod_cast htotal
  have hs : queryVolume m count keys≤(M:ℝ)*(ResidualFamilyKeys.channelCount m (t m):ℝ)*(cap m:ℝ)^beta := by
    unfold queryVolume
    simp_rw[←Finset.sum_mul,htR]
    have hh : (∑ c : Fin (ResidualFamilyKeys.channelCount m (t m)),(M:ℝ)*
      (HalfSourceRoutedQueryCost.support m (CappedBitPreparation.ones (ResidualFamilyKeys.normal (keys.get c)))
        (CappedBitPreparation.ones (ResidualFamilyKeys.opposite (keys.get c))):ℝ)^beta)≤
      ∑ _c : Fin (ResidualFamilyKeys.channelCount m (t m)),(M:ℝ)*(cap m:ℝ)^beta := by
      apply Finset.sum_le_sum;intro c _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num[beta])
      exact_mod_cast HalfSourceRoutedQueryCost.support_le m _ _
    simpa only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  have hh := mul_le_mul_of_nonneg_left (HalfSourceRoutedQueryCost.channel_query_bound m hm) (Nat.cast_nonneg M)
  exact hs.trans (by convert hh using 1 <;> ring)

theorem cap_power (m : ℕ) : (cap m:ℝ)^(1+alpha)≤676*(m+1:ℝ)^2*(((4:ℝ)^m)^((1+alpha)*zeta)) := by
  have hpow : 0≤1+alpha := by norm_num[alpha]
  have hpow2 : 1+alpha≤2 := by norm_num[alpha]
  have hbase : 1≤26*(m+1:ℝ) := by have := Nat.cast_nonneg (α:=ℝ) m;linarith
  have hc := Real.rpow_le_rpow (Nat.cast_nonneg (cap m)) (HalfSourceAdaptiveBandCost.cap_bound m) hpow
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul (by positivity)] at hc
  have hp : (26*(m+1:ℝ))^(1+alpha)≤(26*(m+1:ℝ))^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hbase hpow2
  calc
    _ ≤(26*(m+1:ℝ))^(1+alpha)*(((4:ℝ)^m)^(zeta*(1+alpha))) := hc
    _ ≤(26*(m+1:ℝ))^2*(((4:ℝ)^m)^(zeta*(1+alpha))) := by gcongr
    _ = _ := by rw[mul_comm zeta (1+alpha)];ring

theorem own_padding (N m : ℕ) (hm : 32≤ m)
    (hfit : ThinProductCosts.gridSide (L m) m≤N)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : keys.toList=(ResidualFamilyKeys.channels m (t m)).value) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
      (HalfSourceActualVolumes.groups m keys:ℝ)*(cap m:ℝ)^(1+alpha)≤
      (281216*HalfSourceGroupVolume.groupConstant)*(N:ℝ)*(m+1:ℝ)^5*(((4:ℝ)^m)^E) := by
  have hg := HalfSourceActualVolumes.groups_bands_bound N m hm hfit keys hk
  have hp := cap_power m
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hshape : (L m+1:ℝ)≤13*(m+1:ℝ) := by exact_mod_cast (show L m+1≤13*(m+1) by dsimp[L];omega)
  have hc : 0≤HalfSourceGroupVolume.groupConstant := by unfold HalfSourceGroupVolume.groupConstant;positivity
  calc
    _ ≤(TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
      (HalfSourceActualVolumes.groups m keys:ℝ)*(676*(m+1:ℝ)^2*(((4:ℝ)^m)^((1+alpha)*zeta))) := by gcongr
    _ =676*(m+1:ℝ)^2*((TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)*
      (HalfSourceActualVolumes.groups m keys:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta))) := by ring
    _ ≤676*(m+1:ℝ)^2*(32*(N:ℝ)*(L m+1:ℝ)*(HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2)*(((4:ℝ)^m)^E)) := mul_le_mul_of_nonneg_left hg (by positivity)
    _ ≤676*(m+1:ℝ)^2*(32*(N:ℝ)*(13*(m+1:ℝ))*(HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2)*(((4:ℝ)^m)^E)) := by gcongr
    _ = _ := by ring

def repetitions (m : ℕ) : ℕ :=
  2*HalfSourceRootFamilyCosts.multiplicity m*RetainedRootWindows.slots (L m-m)

theorem repetitions_bound (m : ℕ) : repetitions m≤212992*(m+1)^8 := by
  have hj := HalfSourceRootFamilyCosts.multiplicity_bound m
  have hs := HalfSourceAdaptiveVolume.slots_le (L m-m)
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hshape : L m-m+1≤13*(m+1) := by dsimp[L];omega
  have hr : 2*m+1≤2*(m+1) := by omega
  unfold repetitions
  calc
    _ ≤2*((64*(m+1)^3)^2*(2*m+1))*(L m-m+1) := by gcongr
    _ ≤2*((64*(m+1)^3)^2*(2*(m+1)))*(13*(m+1)) := by gcongr
    _ = _ := by ring

#print axioms query_partition
#print axioms cap_power
#print axioms own_padding
#print axioms repetitions_bound
end
end ThinMatrix.HalfSourceCompletionVolume
