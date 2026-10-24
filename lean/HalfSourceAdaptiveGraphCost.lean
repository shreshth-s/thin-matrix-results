import HalfSourceAdaptivePolynomials

/-! All actual adaptive root encoders, with both sides, every translated
source pair and every degree run. Channel compatibility and row magnitudes
are semantic invariants; no running-time domination premise is assumed. -/
namespace ThinMatrix.HalfSourceAdaptiveGraphCost
open HalfSourceAdaptiveFamilyCost HalfSourceRootFamilyCosts
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local irreducible] GoodMapEmbedding.goodSlots OptimizedFoldedPlan.ordinaryLength

variable {m C : ℕ}

def Channels (roots : GraphResidualFamilies.Roots (L m) m C (t m))
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m))) : Prop :=
  ∀ u v run i j c,
    ((((((roots.get u).get v).get run).1.get i).get j).get c).channel=keys.get c ∧
    ((((((roots.get u).get v).get run).2.get i).get j).get c).channel=keys.get c

def volume (m : ℕ) (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m))) : ℕ :=
  HalfSourceActualVolumes.roots m+HalfSourceActualVolumes.groups m keys*cap m

theorem volume_pos (hm0 : 0 < m)
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m))) : 1≤volume m keys := by
  have hh := scaffold_absorbed hm0
  unfold volume
  omega

theorem family_price (hm0 : 0 < m) (hm : m≤L m-m)
    (roots : RetainedResidualFamily.Family (L m) m C (t m))
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : ∀ i j c, ((((roots.get i).get j).get c).channel)=keys.get c)
    (A : ℕ) (hC : 1≤C) :
    GraphAdaptivePrefixCosts.familyBitBudget hm (cap m) roots A+
      GraphAdaptivePrefixCosts.familyControlBudget hm (cap m) roots≤
      C*(unit (L m-m) m (cap m) A+120)*volume m keys := by
  have hb := family_budget hm roots keys hk A hC
  have hs := scaffold_absorbed hm0
  have hscale := Nat.mul_le_mul_right (120*HalfSourceActualVolumes.roots m) hC
  have hnonneg := Nat.zero_le (120*C*HalfSourceActualVolumes.groups m keys*cap m)
  unfold volume
  nlinarith

theorem graph_price (hm0 : 0 < m) (hm : m≤L m-m)
    (roots : GraphResidualFamilies.Roots (L m) m C (t m))
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : Channels roots keys) (A : ℕ) (hC : 1≤C) :
    GraphAdaptivePrefixCosts.bitBudget hm (cap m) roots A+
      GraphAdaptivePrefixCosts.controlBudget hm (cap m) roots≤
      130*HalfSourceRootFamilyCosts.multiplicity m*C*(unit (L m-m) m (cap m) A+120)*volume m keys := by
  let F := C*(unit (L m-m) m (cap m) A+120)*volume m keys
  let J := ExactHalfSourcePlan.J m
  let r := 2*m+1
  have hF : 1≤F := one_le_mul (one_le_mul hC (by omega)) (volume_pos hm0 keys)
  have hJ : 1≤J := ExactHalfCroppedEmbedding.shifts_nonempty m
  have hr : 1≤r := by dsimp[r];omega
  have hs : (∑ u,∑ v,∑ run,
    (GraphAdaptivePrefixCosts.familyBitBudget hm (cap m) ((((roots.get u).get v).get run).1) A+
      GraphAdaptivePrefixCosts.familyControlBudget hm (cap m) ((((roots.get u).get v).get run).1)+
      GraphAdaptivePrefixCosts.familyBitBudget hm (cap m) ((((roots.get u).get v).get run).2) A+
      GraphAdaptivePrefixCosts.familyControlBudget hm (cap m) ((((roots.get u).get v).get run).2)))≤J^2*r*(2*F) := by
    have hh : (∑ u,∑ v,∑ run,
      (GraphAdaptivePrefixCosts.familyBitBudget hm (cap m) ((((roots.get u).get v).get run).1) A+
        GraphAdaptivePrefixCosts.familyControlBudget hm (cap m) ((((roots.get u).get v).get run).1)+
        GraphAdaptivePrefixCosts.familyBitBudget hm (cap m) ((((roots.get u).get v).get run).2) A+
        GraphAdaptivePrefixCosts.familyControlBudget hm (cap m) ((((roots.get u).get v).get run).2)))≤
        ∑ _u : Fin J,∑ _v : Fin J,∑ _run : Fin r,2*F := by
      apply Finset.sum_le_sum; intro u _
      apply Finset.sum_le_sum; intro v _
      apply Finset.sum_le_sum; intro run _
      have hl := family_price hm0 hm ((((roots.get u).get v).get run).1) keys (fun i j c => (hk u v run i j c).1) A hC
      have hr' := family_price hm0 hm ((((roots.get u).get v).get run).2) keys (fun i j c => (hk u v run i j c).2) A hC
      change _≤F at hl
      change _≤F at hr'
      omega
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,pow_two,mul_assoc] using hh
  have h0 : 1≤J^2*r*F := one_le_mul (one_le_mul (Nat.one_le_pow 2 J hJ) hr) hF
  have h1 : J≤J^2*r*F := by
    have hh : 1≤J*r*F := one_le_mul (one_le_mul hJ hr) hF
    nlinarith only [Nat.mul_le_mul_left J hh]
  have h2 : J^2≤J^2*r*F := by
    have hh : 1≤r*F := one_le_mul hr hF
    nlinarith only [Nat.mul_le_mul_left (J^2) hh]
  have h3 : J^2*r≤J^2*r*F := Nat.le_mul_of_pos_right _ hF
  unfold GraphAdaptivePrefixCosts.bitBudget GraphAdaptivePrefixCosts.controlBudget
  rw [scaffold]
  simp_rw [Finset.sum_add_distrib] at hs ⊢
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  change _≤130*(J^2*r)*C*(unit (L m-m) m (cap m) A+120)*volume m keys
  have heq : 130*(J^2*r)*C*(unit (L m-m) m (cap m) A+120)*volume m keys=130*(J^2*r*F) := by dsimp[F];ring
  rw [heq]
  dsimp only [J,r] at *
  nlinarith only [hs,h0,h1,h2,h3]

theorem graph_polynomial (hm0 : 0 < m) (hm : m≤L m-m)
    (roots : GraphResidualFamilies.Roots (L m) m C (t m))
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : Channels roots keys) (hC : 1≤C) :
    GraphAdaptivePrefixCosts.bitBudget hm (cap m) roots (2^(L m+4*m))+
      GraphAdaptivePrefixCosts.controlBudget hm (cap m) roots≤
      1000000000000000000000000*C*(m+1)^12*volume m keys := by
  have hb := graph_price hm0 hm roots keys hk (2^(L m+4*m)) hC
  have hu := HalfSourceAdaptivePolynomials.canonical_unit m
  have hj := multiplicity_bound m
  have hr : 2*m+1≤2*(m+1) := by omega
  calc
    _ ≤130*((64*(m+1)^3)^2*(2*m+1))*C*(10000000000000000*(m+1)^5)*volume m keys := by
      exact hb.trans (by gcongr)
    _ ≤130*((64*(m+1)^3)^2*(2*(m+1)))*C*(10000000000000000*(m+1)^5)*volume m keys := by gcongr
    _ = (130*64^2*2*10000000000000000)*C*(m+1)^12*volume m keys := by ring
    _ ≤ _ := by gcongr;norm_num

theorem execute_work (hm0 : 0 < m) (hm : m≤L m-m)
    (roots : GraphResidualFamilies.Roots (L m) m C (t m))
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hk : Channels roots keys) (hC : 1≤C)
    (ha : GraphRootWindows.RootBound roots (2^(L m+4*m))) :
    (GraphAdaptivePrefix.execute hm (cap m) roots).bitSteps+
      (GraphAdaptivePrefix.execute hm (cap m) roots).control≤
      1000000000000000000000000*C*(m+1)^12*volume m keys :=
  (Nat.add_le_add (GraphAdaptivePrefixCosts.execute_bits hm (cap m) roots _ ha)
    (GraphAdaptivePrefixCosts.execute_control hm (cap m) roots)).trans (graph_polynomial hm0 hm roots keys hk hC)

#print axioms volume_pos
#print axioms family_price
#print axioms graph_price
#print axioms graph_polynomial
#print axioms execute_work
end
end ThinMatrix.HalfSourceAdaptiveGraphCost
