import GraphRootFamilyProducts

set_option autoImplicit false

/-! Exact reindexing of the actual strict retained channel enumeration.
This is a proof about existing keys; it executes no powerset construction. -/
namespace ThinMatrix.RetainedChannelPowerset
open ResidualFamilyKeys CappedBitPreparation
open scoped BigOperators

theorem ones_view {n : ℕ} (c : Vector Bool n) : CappedBitPreparation.ones c=WalshEmbedding.ones c.get := by
  rw [← support_card]
  rfl

theorem joint_card {m : ℕ} (c : Channel m) :
    (support c).card=WalshEmbedding.ones (normal c).get+WalshEmbedding.ones (opposite c).get := by
  rw [support_card,← ones_view,← ones_view,← ones_join,join_split]

theorem get_mem {m t : ℕ} (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value) (i : Fin (channelCount m t)) :
    keys.get i∈(channels m t).value := by
  rw [← hk]
  exact List.mem_iff_get.mpr ⟨⟨i.val,by simp⟩,rfl⟩

theorem get_injective {m t : ℕ} (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value) : Function.Injective keys.get := by
  intro i j he
  have hn : keys.toList.Nodup := by rw [hk]; exact channels_nodup m t
  have hf := hn.injective_get (show keys.toList.get ⟨i.val,by simp⟩=keys.toList.get ⟨j.val,by simp⟩ from he)
  exact Fin.ext (congrArg (fun i : Fin keys.toList.length => i.val) hf)

theorem sum_support {R : Type*} [AddCommMonoid R] {m t : ℕ}
    (keys : Vector (Channel m) (channelCount m t)) (hk : keys.toList=(channels m t).value)
    (f : Finset (Fin (m+m)) → R) :
    (∑ i, f (support (keys.get i)))=
      ∑ C∈(Finset.univ : Finset (Fin (m+m))).powerset.filter (fun C => C.card<t), f C := by
  classical
  apply Finset.sum_bij (fun i _ => support (keys.get i))
  · intro i _
    simp only [Finset.mem_filter,Finset.mem_powerset,Finset.subset_univ,true_and,support_card]
    exact (channels_mem m t _).mp (get_mem keys hk i)
  · intro i _ j _ he
    exact get_injective keys hk (support_injective he)
  · intro C hc
    have hc' : C.card<t := (Finset.mem_filter.mp hc).2
    have hm : fromSupport C∈keys.toList := by
      rw [hk,channels_mem,← support_card,support_fromSupport]
      exact hc'
    obtain ⟨i,hi,he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hm)
    exact ⟨⟨i,hi⟩,Finset.mem_univ _,by simp only [Vector.get_eq_getElem,he,support_fromSupport]⟩
  · intro i _
    rfl

#print axioms ones_view
#print axioms joint_card
#print axioms get_mem
#print axioms get_injective
#print axioms sum_support
end ThinMatrix.RetainedChannelPowerset
