import HalfSourceGroupVolume
import RetainedChannelPowerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Reindex the actual retained channel keys by their two physical-half
weights. These are equalities about the existing key enumeration; no
powerset is constructed by the executable algorithm. -/
namespace ThinMatrix.HalfSourceChannelTypes
open ResidualFamilyKeys CappedBitPreparation
open scoped BigOperators
set_option maxHeartbeats 4000000

noncomputable section

theorem sum_split_support {R : Type*} [AddCommMonoid R] {m t : ℕ}
    (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value)
    (f : Finset (Fin m) → Finset (Fin m) → R) :
    (∑ i, f (support (normal (keys.get i))) (support (opposite (keys.get i))))=
      ∑ p ∈ ((Finset.univ : Finset (Fin m)).powerset.product Finset.univ.powerset).filter
        (fun p => p.1.card+p.2.card<t), f p.1 p.2 := by
  classical
  apply Finset.sum_bij (fun i _ => (support (normal (keys.get i)),support (opposite (keys.get i))))
  · intro i _
    simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_powerset,Finset.subset_univ,true_and]
    rw [support_card,support_card,← ones_join,join_split]
    exact (channels_mem m t _).mp (RetainedChannelPowerset.get_mem keys hk i)
  · intro i _ j _ he
    have hn := support_injective (congrArg Prod.fst he)
    have ho := support_injective (congrArg Prod.snd he)
    apply RetainedChannelPowerset.get_injective keys hk
    rw [← join_split (keys.get i),hn,ho,join_split]
  · intro p hp
    have hlt : p.1.card+p.2.card<t := (Finset.mem_filter.mp hp).2
    let c := fromSupport p.1 ++ fromSupport p.2
    have hc : c∈keys.toList := by
      rw [hk,channels_mem]
      dsimp [c]
      rw [ones_join,← support_card,← support_card,support_fromSupport,support_fromSupport]
      exact hlt
    obtain ⟨i,hi,he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hc)
    refine ⟨⟨i,hi⟩,Finset.mem_univ _,?_⟩
    simp only [Vector.get_eq_getElem,he,c,(split_join _ _).1,(split_join _ _).2,support_fromSupport]
  · intro i _
    rfl

theorem powerset_card_sum {R : Type*} [Semiring R] {α : Type*}
    (s : Finset α) (f : ℕ → R) :
    (∑ C ∈ s.powerset, f C.card)=∑ j ∈ Finset.range (s.card+1), (s.card.choose j:R)*f j := by
  rw [Finset.sum_powerset]
  simp_rw [Finset.sum_powersetCard,nsmul_eq_mul]

/-- The exact multiplicity of an ordered type is choose(m,cn)choose(m,co).
The guard is strict, matching the retained channel constructor. -/
theorem sum_types {R : Type*} [Semiring R] {m t : ℕ}
    (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value) (f : ℕ → ℕ → R) :
    (∑ i, f (ones (normal (keys.get i))) (ones (opposite (keys.get i))))=
      ∑ cn ∈ Finset.range (m+1), ∑ co ∈ Finset.range (m+1),
        if cn+co<t then (m.choose cn:R)*(m.choose co:R)*f cn co else 0 := by
  classical
  simp_rw [← support_card]
  rw [sum_split_support keys hk (fun A B => f A.card B.card),Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  change (∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
    (fun cn => ∑ B ∈ (Finset.univ : Finset (Fin m)).powerset,
      if cn+B.card<t then f cn B.card else 0) A.card)=_
  rw [powerset_card_sum (Finset.univ : Finset (Fin m))
    (fun cn => ∑ B ∈ (Finset.univ : Finset (Fin m)).powerset,
      if cn+B.card<t then f cn B.card else 0)]
  simp only [Finset.card_univ,Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro cn _
  rw [powerset_card_sum (Finset.univ : Finset (Fin m))
    (fun co => if cn+co<t then f cn co else 0)]
  simp only [Finset.card_univ,Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro co _
  split_ifs <;> simp [mul_assoc]

def groupWeight (m cn co : ℕ) : ℕ :=
  4^(2*(OptimizedFoldedPlan.ordinaryLength m-m)-HalfSourceGroupVolume.suffixLength m cn co)*
    2^(HalfSourceGroupVolume.suffixLength m cn co)

/-- The real channel-key loop has exactly the group count whose entropy
bound was certified, for each good-mask pair. -/
theorem actual_group_sum (m : ℕ)
    (keys : Vector (Channel m) (channelCount m (OptimizedFoldedPlan.channelLength m)))
    (hk : keys.toList=(channels m (OptimizedFoldedPlan.channelLength m)).value) :
    (OptimizedFoldedPlan.ordinaryLength m).choose m^2*
      (∑ i, groupWeight m (ones (normal (keys.get i))) (ones (opposite (keys.get i))))=
      HalfSourceGroupVolume.groupCount m := by
  rw [sum_types keys hk]
  unfold HalfSourceGroupVolume.groupCount HalfSourceGroupVolume.typeGroups groupWeight
  simp only [mul_assoc,Nat.cast_id]

#print axioms sum_split_support
#print axioms powerset_card_sum
#print axioms sum_types
#print axioms actual_group_sum
end
end ThinMatrix.HalfSourceChannelTypes
