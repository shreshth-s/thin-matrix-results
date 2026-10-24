import HalfSourceAdaptiveWidths
import HalfSourceActualVolumes
import HalfSourceRootFamilyCosts

set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace ThinMatrix.HalfSourceAdaptiveFamilyCost
open HalfSourceAdaptiveVolume HalfSourcePrefixVolume
open scoped BigOperators

 def width (k A : ℕ) : ℕ := 3*k+A.size+1
 def unit (k m cap A : ℕ) : ℕ :=
  denseBitUnit k m cap (width k A)+HalfSourceAdaptiveControl.denseUnit k m cap+
    (k+1)*(m+1)*(110000*(width k A+1)^3)

 theorem entry_budget {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (hcap : 0 < cap)
    (root : RetainedResidualFamily.Entry L m C) (A : ℕ) (hC : 1 ≤ C) :
    GraphAdaptivePrefixCosts.entryBitBudget hm cap root A+
      GraphAdaptivePrefixCosts.entryControlBudget hm cap root ≤
        C*(3^(2*(L-m))+entryGroups (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value) root)*
          unit (L-m) m cap A := by
  let k := L-m
  let ell := GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value
  let E := entryGroups ell root
  have hb := HalfSourceAdaptiveVolume.entry_bits hm cap root A (width k A) hC (by unfold width; omega)
  have hc := HalfSourceAdaptiveControl.entry_control hm cap hcap root hC
  have hp : WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell ≤ width k A := by
    rw [WindowPrefixProgram.dimension]
    unfold width
    omega
  have hbu := bitUnit_polynomial (WindowPrefixProgram.prefixLength k ell) (WindowPrefixProgram.length k ell) (width k A) hp
  have hcu := controlUnit_polynomial (WindowPrefixProgram.prefixLength k ell) (WindowPrefixProgram.length k ell) (width k A) hp
  have hbu' := Nat.mul_le_mul_left (C*RetainedRootWindows.slots k*(m+1)*E) hbu
  have hcu' := Nat.mul_le_mul_left (C*RetainedRootWindows.slots k*(m+1)*E) hcu
  have hs := Nat.mul_le_mul_right (C*(m+1)*E*(110000*(width k A+1)^3)) (slots_le k)
  have hd0 := Nat.zero_le (C*3^(2*k)*((k+1)*(m+1)*(110000*(width k A+1)^3)))
  have he0 := Nat.zero_le (C*E*(denseBitUnit k m cap (width k A)+HalfSourceAdaptiveControl.denseUnit k m cap))
  unfold unit
  dsimp only [k,ell,E] at *
  nlinarith

 theorem entry_work {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (hcap : 0 < cap)
    (root : RetainedResidualFamily.Entry L m C) (A : ℕ) (hC : 1 ≤ C)
    (hA : ResidualWindowSource.BoundRows root A) :
    (GraphAdaptivePrefix.entry hm cap root).bitSteps+(GraphAdaptivePrefix.entry hm cap root).control ≤
        C*(3^(2*(L-m))+entryGroups (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value) root)*
          unit (L-m) m cap A :=
  (Nat.add_le_add (GraphAdaptivePrefixCosts.entry_bits hm cap root A hA)
    (GraphAdaptivePrefixCosts.entry_control hm cap root)).trans (entry_budget hm cap hcap root A hC)

 theorem scaffold (G H : ℕ) (f : Fin G → Fin G → Fin H → ℕ) :
    GraphPrefixProgram.sumControl (fun i => GraphPrefixProgram.sumControl (fun j => GraphPrefixProgram.sumControl (f i j)))=
      (∑ i,∑ j,∑ c,f i j c)+32*G^2*H+40*G^2+40*G+8 := by
  simp only [GraphPrefixProgram.sumControl,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

variable {m C : ℕ}
 abbrev L (m : ℕ) := OptimizedFoldedPlan.ordinaryLength m
 abbrev t (m : ℕ) := OptimizedFoldedPlan.channelLength m
 abbrev cap (m : ℕ) := HalfSourceSuffixChoice.limit m (L m-m)

 theorem canonical_entry (hm : m ≤ L m-m) (root : RetainedResidualFamily.Entry (L m) m C)
    (A : ℕ) (hC : 1 ≤ C) :
    GraphAdaptivePrefixCosts.entryBitBudget hm (cap m) root A+
      GraphAdaptivePrefixCosts.entryControlBudget hm (cap m) root ≤
        C*unit (L m-m) m (cap m) A*
          (3^(2*(L m-m)+m)+HalfSourceChannelTypes.groupWeight m
            (RetainedRootWindows.weights root.channel).value.1 (RetainedRootWindows.weights root.channel).value.2*cap m) := by
  have hb := entry_budget hm (cap m) (HalfSourceSuffixChoice.limit_pos _ _) root A hC
  have hg := HalfSourceAdaptiveWidths.selected_groups hm root
  have hp : 3^(2*(L m-m)) ≤ 3^(2*(L m-m)+m) := Nat.pow_le_pow_right (by omega) (by omega)
  have hh := Nat.mul_le_mul_right (C*unit (L m-m) m (cap m) A) (Nat.add_le_add hp hg)
  dsimp only [cap,L] at *
  nlinarith

 theorem family_budget (hm : m ≤ L m-m) (roots : RetainedResidualFamily.Family (L m) m C (t m))
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hkeys : ∀ i j c,((((roots.get i).get j).get c).channel)=keys.get c)
    (A : ℕ) (hC : 1 ≤ C) :
    GraphAdaptivePrefixCosts.familyBitBudget hm (cap m) roots A+
      GraphAdaptivePrefixCosts.familyControlBudget hm (cap m) roots ≤
        C*unit (L m-m) m (cap m) A*(HalfSourceActualVolumes.roots m+HalfSourceActualVolumes.groups m keys*cap m)+
          32*(GoodMapEmbedding.goodSlots (L m) m).card^2*ResidualFamilyKeys.channelCount m (t m)+
            40*(GoodMapEmbedding.goodSlots (L m) m).card^2+40*(GoodMapEmbedding.goodSlots (L m) m).card+8 := by
  have hs : (∑ i,∑ j,∑ c,(GraphAdaptivePrefixCosts.entryBitBudget hm (cap m) (((roots.get i).get j).get c) A+
      GraphAdaptivePrefixCosts.entryControlBudget hm (cap m) (((roots.get i).get j).get c))) ≤
    ∑ i : Fin (GoodMapEmbedding.goodSlots (L m) m).card,
      ∑ j : Fin (GoodMapEmbedding.goodSlots (L m) m).card,
        ∑ c : Fin (ResidualFamilyKeys.channelCount m (t m)),
          C*unit (L m-m) m (cap m) A*(3^(2*(L m-m)+m)+HalfSourceChannelTypes.groupWeight m
            (CappedBitPreparation.ones (ResidualFamilyKeys.normal (keys.get c)))
            (CappedBitPreparation.ones (ResidualFamilyKeys.opposite (keys.get c)))*cap m) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro c _
    have hh := canonical_entry hm (((roots.get i).get j).get c) A hC
    rw [hkeys i j c,RetainedRootWindows.weights_value] at hh
    simpa only [RetainedChannelPowerset.ones_view] using hh
  simp_rw [Finset.sum_add_distrib] at hs
  simp_rw [mul_add,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul] at hs
  unfold GraphAdaptivePrefixCosts.familyBitBudget GraphAdaptivePrefixCosts.familyControlBudget
  rw [scaffold]
  unfold HalfSourceActualVolumes.roots HalfSourceActualVolumes.groups
  dsimp only [L,t] at *
  nlinarith only [hs]

theorem scaffold_absorbed (hm : 0 < m) :
    32*(GoodMapEmbedding.goodSlots (L m) m).card^2*ResidualFamilyKeys.channelCount m (t m)+
      40*(GoodMapEmbedding.goodSlots (L m) m).card^2+40*(GoodMapEmbedding.goodSlots (L m) m).card+8 ≤
        120*HalfSourceActualVolumes.roots m := by
  let G := (GoodMapEmbedding.goodSlots (L m) m).card
  let H := ResidualFamilyKeys.channelCount m (t m)
  have hG : 1 ≤ G := by
    have hc := Nat.choose_pos (OptimizedFoldedPlan.ordinaryLength_lower m)
    have hd := GoodMapEmbedding.goodSlots_density (OptimizedFoldedPlan.ordinaryLength m) m
    dsimp only [G,L]
    omega
  have hH : 1 ≤ H := HalfSourceRootFamilyCosts.channel_positive m hm
  have hZ : 1 ≤ 3^(2*(L m-m)+m) := Nat.one_le_pow _ _ (by omega)
  have h1 := Nat.mul_le_mul_left (G^2*H) hZ
  have h2 := Nat.mul_le_mul_left (G^2) hH
  have h3 : G ≤ G^2 := by nlinarith
  rw [HalfSourceActualVolumes.roots_eq]
  change 32*G^2*H+40*G^2+40*G+8 ≤ 120*(G^2*H*3^(2*(L m-m)+m))
  nlinarith

theorem family_work (hm0 : 0 < m) (hm : m ≤ L m-m)
    (roots : RetainedResidualFamily.Family (L m) m C (t m))
    (keys : Vector (ResidualFamilyKeys.Channel m) (ResidualFamilyKeys.channelCount m (t m)))
    (hkeys : ∀ i j c,((((roots.get i).get j).get c).channel)=keys.get c)
    (A : ℕ) (hC : 1 ≤ C) (hA : GraphRootWindows.FamilyBound roots A) :
    (GraphAdaptivePrefix.family hm (cap m) roots).bitSteps+
      (GraphAdaptivePrefix.family hm (cap m) roots).control ≤
        C*(unit (L m-m) m (cap m) A+120)*(HalfSourceActualVolumes.roots m+HalfSourceActualVolumes.groups m keys*cap m) := by
  have hb := Nat.add_le_add (GraphAdaptivePrefixCosts.family_bits hm (cap m) roots A hA)
    (GraphAdaptivePrefixCosts.family_control hm (cap m) roots)
  have hf := family_budget hm roots keys hkeys A hC
  have hs := scaffold_absorbed hm0
  have hscale := Nat.mul_le_mul_right (120*HalfSourceActualVolumes.roots m) hC
  have hnonneg := Nat.zero_le (120*C*HalfSourceActualVolumes.groups m keys*cap m)
  nlinarith

#print axioms scaffold_absorbed
#print axioms family_work
#print axioms entry_budget
#print axioms entry_work
#print axioms scaffold
#print axioms canonical_entry
#print axioms family_budget
end ThinMatrix.HalfSourceAdaptiveFamilyCost
