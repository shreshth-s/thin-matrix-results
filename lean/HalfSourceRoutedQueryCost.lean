import HalfSourceAdaptiveBandCost
import GraphOwnRoutingTotals

/-! Price the actual routed occurrences across all retained channels. Each
physical occurrence enters only its own band/masks; duplicate occurrences
remain distinct. The result gives the LOW q1 term with full cyclic columns. -/
namespace ThinMatrix.HalfSourceRoutedQueryCost
open HalfSourceParameters HalfSourceAdaptiveFamilyCost GraphOwnRequestRouter GoodMapEmbedding
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local irreducible] GoodMapEmbedding.goodSlots OptimizedFoldedPlan.ordinaryLength

def support (m cn co : ℕ) : ℕ :=
  CappedSubsetList.count (HalfSourceSuffixChoice.forType (L m) m cn co)
    (WindowPrefixProgram.cap (L m-m) (HalfSourceSuffixChoice.forType (L m) m cn co) (m/2) cn co)

theorem support_le (m cn co : ℕ) : support m cn co≤cap m :=
  (HalfSourceSuffixChoice.forType_fit (L m) m cn co).2

theorem cap_query_bound (m : ℕ) : (cap m:ℝ)^beta≤26*(m+1:ℝ)*(((4:ℝ)^m)^(beta*zeta)) := by
  have hbeta : 0≤beta := by norm_num[beta]
  have hb1 : beta≤1 := by norm_num[beta]
  have hbase : 1≤26*(m+1:ℝ) := by have := Nat.cast_nonneg (α:=ℝ) m;linarith
  have hc := Real.rpow_le_rpow (Nat.cast_nonneg (cap m)) (HalfSourceAdaptiveBandCost.cap_bound m) hbeta
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul (by positivity)] at hc
  have hl : (26*(m+1:ℝ))^beta≤26*(m+1:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hb1
  exact hc.trans (by rw[mul_comm zeta beta];gcongr)

theorem channel_query_bound (m : ℕ) (hm : 0 < m) :
    (ResidualFamilyKeys.channelCount m (t m):ℝ)*(cap m:ℝ)^beta≤
      26*(m+1:ℝ)^2*(((4:ℝ)^m)^q1) := by
  have hh := mul_le_mul (HalfSourceRootVolume.channelCount_bound m hm) (cap_query_bound m)
    (by positivity) (by positivity)
  calc
    _ ≤((m+1:ℝ)*(((4:ℝ)^m)^Q))*(26*(m+1:ℝ)*(((4:ℝ)^m)^(beta*zeta))) := hh
    _ = _ := by unfold q1;rw[Real.rpow_add (by positivity)];ring

variable {S m C M : ℕ}

def queryVolume (right : Bool) (requests : Vector (GraphCompletionRequests.Physical (L m) m C) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m))) : ℝ :=
  ∑ c,∑ a : Fin S,∑ normal : Fin (goodSlots (L m) m).card,
    ∑ b : Fin S,∑ opposite : Fin (goodSlots (L m) m).card,
      ((ids (run right requests hb).value a b normal opposite).value.length:ℝ)*
        (support m (CappedBitPreparation.ones (ResidualFamilyKeys.normal (keys.get c)))
          (CappedBitPreparation.ones (ResidualFamilyKeys.opposite (keys.get c))):ℝ)^beta

theorem routed_volume (right : Bool) (requests : Vector (GraphCompletionRequests.Physical (L m) m C) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hm : 0 < m) : queryVolume right requests hb keys≤26*(M:ℝ)*(m+1:ℝ)^2*(((4:ℝ)^m)^q1) := by
  have ht := GraphOwnRoutingTotals.total_selected right requests hb
  have htR : (∑ a : Fin S,∑ normal : Fin (goodSlots (L m) m).card,
      ∑ b : Fin S,∑ opposite : Fin (goodSlots (L m) m).card,
      ((ids (run right requests hb).value a b normal opposite).value.length:ℝ))=(M:ℝ) := by exact_mod_cast ht
  have hs : queryVolume right requests hb keys≤
      (M:ℝ)*(ResidualFamilyKeys.channelCount m (t m):ℝ)*(cap m:ℝ)^beta := by
    unfold queryVolume
    simp_rw [←Finset.sum_mul,htR]
    have hh : (∑ c : Fin (ResidualFamilyKeys.channelCount m (t m)),
      (M:ℝ)*(support m (CappedBitPreparation.ones (ResidualFamilyKeys.normal (keys.get c)))
        (CappedBitPreparation.ones (ResidualFamilyKeys.opposite (keys.get c))):ℝ)^beta)≤
      ∑ _c : Fin (ResidualFamilyKeys.channelCount m (t m)),(M:ℝ)*(cap m:ℝ)^beta := by
      apply Finset.sum_le_sum;intro c _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num[beta])
      exact_mod_cast support_le m _ _
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  have hc := mul_le_mul_of_nonneg_left (channel_query_bound m hm) (Nat.cast_nonneg M)
  exact hs.trans (by convert hc using 1 <;> ring)

theorem physical_columns (n B q : ℕ) (right : Bool)
    (requests : Vector (GraphCompletionRequests.Physical (L m) m q) (FoldedBackendExecution.windowQuerySize n))
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hm : 0 < m) : queryVolume right requests hb keys*(B*((m+1)*q):ℕ)≤
      78*(n:ℝ)^2*(B:ℝ)*(q:ℝ)*(m+1:ℝ)^3*(((4:ℝ)^m)^q1) := by
  have hh := mul_le_mul_of_nonneg_right (routed_volume right requests hb keys hm)
    (Nat.cast_nonneg (B*((m+1)*q)))
  unfold FoldedBackendExecution.windowQuerySize at hh
  push_cast at hh ⊢
  exact hh.trans_eq (by ring)

#print axioms support_le
#print axioms cap_query_bound
#print axioms channel_query_bound
#print axioms routed_volume
#print axioms physical_columns
end
end ThinMatrix.HalfSourceRoutedQueryCost
