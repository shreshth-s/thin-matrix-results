import HalfSourceLowCollectionCosts
import HalfSourceCompletionTotal
import GraphOwnBandTypeRate

/-! Exact counting of the real LOW child programs. The right-half channel
lookup is a permutation, so both orientations pay the same channel sum. -/
namespace ThinMatrix.HalfSourceLowRootSum
open scoped BigOperators
open ExactHalfSourcePlan ResidualFamilyKeys
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
noncomputable section
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 theorem transpose_sum (keys : Vector (Channel p.m) (channelCount p.m p.t))
    (hk : keys.toList=(channels p.m p.t).value)
    (v : Fin (channelCount p.m p.t) → ℝ) :
    (∑ c,v (ResidualChannelTranspose.locate keys c).value)=∑ c,v c := by
  exact Equiv.sum_comp ((⟨(fun i => (ResidualChannelTranspose.locate keys i).value), (fun i => (ResidualChannelTranspose.locate keys i).value), ResidualChannelTranspose.locate_involutive keys hk, ResidualChannelTranspose.locate_involutive keys hk⟩ : Fin (channelCount p.m p.t) ≃ Fin (channelCount p.m p.t))) v

 theorem sum_children (keys : Vector (Channel p.m) (channelCount p.m p.t))
    (hk : keys.toList=(channels p.m p.t).value)
    (roots : GraphOwnLowProgram.RootFamily f p) (price : ℕ)
    (v : Fin (channelCount p.m p.t) → ℝ)
    (hv : ∀ u v' run c side,
      ((roots u v' run c side).bitSteps+price*(roots u v' run c side).control:ℝ)≤v c) :
    (∑ s,(HalfSourceLowCollectionCosts.rootWork f p keys roots price s:ℝ))≤
      2*(HalfSourceRootFamilyCosts.multiplicity p.m:ℝ)*(∑ c,v c) := by
  have each (s : Fin (GraphOwnLowCollection.T f p)) :
      (HalfSourceLowCollectionCosts.rootWork f p keys roots price s:ℝ)≤
        v (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).2).2+
        v (ResidualChannelTranspose.locate keys
          (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).2).2).value := by
    unfold HalfSourceLowCollectionCosts.rootWork
    push_cast
    exact add_le_add (hv _ _ _ _ false) (hv _ _ _ _ true)
  apply (Finset.sum_le_sum (fun s (_ : s∈Finset.univ) => each s)).trans_eq
  change (∑ s : Fin (J p.m*(J p.m*((2*p.m+1)*channelCount p.m p.t))), _)=_
  rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply]
  simp_rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply]
  simp_rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply,Finset.sum_add_distrib]
  rw [transpose_sum f p keys hk v]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold HalfSourceRootFamilyCosts.multiplicity
  push_cast
  ring

#print axioms transpose_sum
#print axioms sum_children
end
end ThinMatrix.HalfSourceLowRootSum
