import HalfSourceLowRootSum
import GraphOwnBandCompleteRate

/-! The exact support and pair-bit group counts used by actual root batches
have the already certified channel-type volume. -/
namespace ThinMatrix.HalfSourceLowTypeVolume
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

 def support (L m t : ℕ) (c : Fin (ResidualFamilyKeys.channelCount m t)) : ℕ :=
  WindowSharedCompletion.D (L-m) (GraphAdaptiveCompatibility.typeLength L m t c) (m/2)
    (GraphWindowCompatibility.counts c).1 (GraphWindowCompatibility.counts c).2
 def groups (L m t : ℕ) (c : Fin (ResidualFamilyKeys.channelCount m t)) : ℕ :=
  2^(WindowPrefixProgram.length (L-m) (GraphAdaptiveCompatibility.typeLength L m t c))*
  4^(WindowPrefixProgram.prefixLength (L-m) (GraphAdaptiveCompatibility.typeLength L m t c))

 theorem channel_keys (m t : ℕ) : (GraphWindowCompatibility.channelVector m t).toList=
    (ResidualFamilyKeys.channels m t).value := by
  simp only [GraphWindowCompatibility.channelVector,Vector.toList_mk]

 theorem counts (m t : ℕ) (c : Fin (ResidualFamilyKeys.channelCount m t)) :
    GraphWindowCompatibility.counts c=
      (CappedBitPreparation.ones (ResidualFamilyKeys.normal ((GraphWindowCompatibility.channelVector m t).get c)),
       CappedBitPreparation.ones (ResidualFamilyKeys.opposite ((GraphWindowCompatibility.channelVector m t).get c))) := by
  unfold GraphWindowCompatibility.counts
  rw [RetainedRootWindows.weights_value]
  simp only [RetainedChannelPowerset.ones_view]

 theorem support_canonical (m t : ℕ) (c : Fin (ResidualFamilyKeys.channelCount m t)) :
    support (L m) m t c=HalfSourceRoutedQueryCost.support m
      (GraphWindowCompatibility.counts c).1 (GraphWindowCompatibility.counts c).2 := by
  have hh := (HalfSourceSuffixChoice.forType_fit (L m) m
    (GraphWindowCompatibility.counts c).1 (GraphWindowCompatibility.counts c).2).1
  simp only [support,WindowSharedCompletion.D,WindowPrefixProgram.length,
    GraphAdaptiveCompatibility.typeLength,Nat.min_eq_left hh,HalfSourceRoutedQueryCost.support]

 theorem groups_canonical (m t : ℕ) (c : Fin (ResidualFamilyKeys.channelCount m t)) :
    groups (L m) m t c=HalfSourceChannelTypes.groupWeight m
      (GraphWindowCompatibility.counts c).1 (GraphWindowCompatibility.counts c).2 := by
  have hh := (HalfSourceSuffixChoice.forType_fit (L m) m
    (GraphWindowCompatibility.counts c).1 (GraphWindowCompatibility.counts c).2).1
  simp only [groups,WindowPrefixProgram.length,WindowPrefixProgram.prefixLength,
    GraphAdaptiveCompatibility.typeLength,Nat.min_eq_left hh,
    HalfSourceChannelTypes.groupWeight,HalfSourceGroupVolume.suffixLength,L,Nat.mul_comm]

 def volume (L m t S M : ℕ) : ℝ :=
   ∑ c : Fin (ResidualFamilyKeys.channelCount m t),
     ((M:ℝ)*(support L m t c:ℝ)^beta+
       (S:ℝ)*(GoodMapEmbedding.goodSlots L m).card^2*(groups L m t c:ℝ)*(support L m t c:ℝ)^(1+alpha))

 theorem canonical_volume (m S M : ℕ) : volume (L m) m (t m) S M≤
     HalfSourceCompletionVolume.queryVolume m (fun _ : Fin 1 => M) (GraphWindowCompatibility.channelVector m (t m))+
       (S:ℝ)*(HalfSourceActualVolumes.groups m (GraphWindowCompatibility.channelVector m (t m)):ℝ)*(cap m:ℝ)^(1+alpha) := by
  let keys := GraphWindowCompatibility.channelVector m (t m)
  have hquery : HalfSourceCompletionVolume.queryVolume m (fun _ : Fin 1 => M) keys=
      ∑ c : Fin (ResidualFamilyKeys.channelCount m (t m)),(M:ℝ)*(support (L m) m (t m) c:ℝ)^beta := by
    unfold HalfSourceCompletionVolume.queryVolume
    simp only [keys,Fin.sum_univ_one,support_canonical,counts]
  rw [hquery]
  unfold volume
  rw [Finset.sum_add_distrib]
  apply add_le_add_right
  have hh : (∑ c : Fin (ResidualFamilyKeys.channelCount m (t m)),
      (S:ℝ)*(GoodMapEmbedding.goodSlots (L m) m).card^2*(groups (L m) m (t m) c:ℝ)*(support (L m) m (t m) c:ℝ)^(1+alpha))≤
      ∑ c : Fin (ResidualFamilyKeys.channelCount m (t m)),
      (S:ℝ)*(GoodMapEmbedding.goodSlots (L m) m).card^2*(groups (L m) m (t m) c:ℝ)*(cap m:ℝ)^(1+alpha) := by
    apply Finset.sum_le_sum;intro c _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num[alpha])
    exact_mod_cast (show support (L m) m (t m) c≤cap m by
      rw [support_canonical];exact HalfSourceRoutedQueryCost.support_le _ _ _)
  apply hh.trans_eq
  rw [HalfSourceActualVolumes.groups_eq]
  simp_rw [groups_canonical,counts]
  simp only [←Finset.sum_mul,←Finset.mul_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_sum]
  dsimp only [L]
  ring

 theorem total (N m M B q : ℕ) (hm : 32 ≤ m)
    (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    (HalfSourceCompletionVolume.repetitions m:ℝ)*(B*((m+1)*q):ℕ)*
      volume (L m) m (t m) (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)) M≤
      HalfSourceCompletionTotal.constant*(B:ℝ)*(q:ℝ)*(m+1:ℝ)^14*
        ((M:ℝ)*(((4:ℝ)^m)^q1)+(N:ℝ)*(((4:ℝ)^m)^E)) := by
  have h := canonical_volume m (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)) M
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans
    (HalfSourceCompletionTotal.total_rate N m M B q hm hfit (fun _ : Fin 1 => M)
      (by simp) (GraphWindowCompatibility.channelVector m (t m)) (channel_keys _ _))

#print axioms channel_keys
#print axioms counts
#print axioms support_canonical
#print axioms groups_canonical
#print axioms canonical_volume
#print axioms total
end
end ThinMatrix.HalfSourceLowTypeVolume
