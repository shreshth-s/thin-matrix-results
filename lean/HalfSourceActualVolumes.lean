import HalfSourceBandVolume

/-! Bind the entropy volumes to the actual accepted good-mask and retained
channel index loops. No all-subsets execution is introduced. -/
namespace ThinMatrix.HalfSourceActualVolumes
open HalfSourceParameters HalfSourceChannelTypes ResidualFamilyKeys CappedBitPreparation
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

 theorem good_count (L m : ℕ) : (GoodMapEmbedding.goodSlots L m).card ≤ L.choose m := by
  have h := Finset.card_le_card
    (Finset.filter_subset (fun Q => GoodSetConstruction.restrictionTest
      (GoodSetConstruction.constructGoodMaps L m).1 Q &&
      GoodSetConstruction.restrictionTest (GoodSetConstruction.constructGoodMaps L m).2 Qᶜ)
      (Finset.univ.powersetCard m))
  simpa only [GoodMapEmbedding.goodSlots,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using h

attribute [local irreducible] GoodMapEmbedding.goodSlots OptimizedFoldedPlan.ordinaryLength

def groups (m : ℕ)
    (keys : Vector (Channel m) (channelCount m (OptimizedFoldedPlan.channelLength m))) : ℕ :=
  ∑ _i : Fin (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card,
    ∑ _j : Fin (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card,
      ∑ k, groupWeight m (ones (normal (keys.get k))) (ones (opposite (keys.get k)))

theorem groups_eq (m : ℕ)
    (keys : Vector (Channel m) (channelCount m (OptimizedFoldedPlan.channelLength m))) :
    groups m keys=(GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card^2*
      (∑ k, groupWeight m (ones (normal (keys.get k))) (ones (opposite (keys.get k)))) := by
  simp only [groups,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,pow_two,mul_assoc]

theorem groups_le (m : ℕ)
    (keys : Vector (Channel m) (channelCount m (OptimizedFoldedPlan.channelLength m)))
    (hk : keys.toList=(channels m (OptimizedFoldedPlan.channelLength m)).value) :
    groups m keys≤HalfSourceGroupVolume.groupCount m := by
  rw [groups_eq,← actual_group_sum m keys hk]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (good_count _ _) 2)

def roots (m : ℕ) : ℕ :=
  ∑ _i : Fin (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card,
    ∑ _j : Fin (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card,
      ∑ _k : Fin (channelCount m (OptimizedFoldedPlan.channelLength m)),
        3^(2*(OptimizedFoldedPlan.ordinaryLength m-m)+m)

theorem roots_eq (m : ℕ) : roots m=
    (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card^2*
      channelCount m (OptimizedFoldedPlan.channelLength m)*3^(2*(OptimizedFoldedPlan.ordinaryLength m-m)+m) := by
  simp only [roots,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,pow_two,mul_assoc]

theorem roots_le (m : ℕ) : roots m≤HalfSourceRootVolume.rootVolume m := by
  rw [roots_eq]
  unfold HalfSourceRootVolume.rootVolume
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (good_count _ _) 2))

theorem groups_completion_bound (m : ℕ) (hm : 32 ≤ m)
    (keys : Vector (Channel m) (channelCount m (OptimizedFoldedPlan.channelLength m)))
    (hk : keys.toList=(channels m (OptimizedFoldedPlan.channelLength m)).value) :
    (groups m keys:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta))≤
      HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2*(((4:ℝ)^m)^(T+E)) := by
  have h : (groups m keys:ℝ)≤HalfSourceGroupVolume.groupCount m := by exact_mod_cast groups_le m keys hk
  exact (mul_le_mul_of_nonneg_right h (by positivity)).trans (HalfSourceGroupVolume.completion_volume_bound m hm)

theorem roots_bound (m : ℕ) (hm : 0 < m) :
    (roots m:ℝ)≤HalfSourceRootVolume.rootConstant*(m+1:ℝ)*(((4:ℝ)^m)^(T+Eroot)) := by
  have h : (roots m:ℝ)≤HalfSourceRootVolume.rootVolume m := by exact_mod_cast roots_le m
  exact h.trans (HalfSourceRootVolume.rootVolume_bound m hm)

theorem groups_bands_bound (N m : ℕ) (hm : 32 ≤ m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N)
    (keys : Vector (Channel m) (channelCount m (OptimizedFoldedPlan.channelLength m)))
    (hk : keys.toList=(channels m (OptimizedFoldedPlan.channelLength m)).value) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      (groups m keys:ℝ)*(((4:ℝ)^m)^((1+alpha)*zeta)) ≤
      32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*
        (HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2)*(((4:ℝ)^m)^E) := by
  have h := HalfSourceBandVolume.transfer N m (by omega) hfit _ _ _
    (show 0≤HalfSourceGroupVolume.groupConstant*(m+1:ℝ)^2 by unfold HalfSourceGroupVolume.groupConstant; positivity)
    (groups_completion_bound m hm keys hk)
  simpa only [mul_assoc] using h

theorem roots_bands_bound (N m : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      roots m ≤32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*
        (HalfSourceRootVolume.rootConstant*(m+1:ℝ))*(((4:ℝ)^m)^Eroot) :=
  HalfSourceBandVolume.transfer N m hm hfit _ _ _
    (by unfold HalfSourceRootVolume.rootConstant; positivity) (roots_bound m hm)

#print axioms good_count
#print axioms groups_eq
#print axioms groups_le
#print axioms roots_eq
#print axioms roots_le
#print axioms groups_completion_bound
#print axioms roots_bound
#print axioms groups_bands_bound
#print axioms roots_bands_bound
end
end ThinMatrix.HalfSourceActualVolumes
