import GraphOwnBandRouter

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThinMatrix.GraphOwnBandRoutingTotals
open scoped BigOperators
open GoodMapEmbedding GraphOwnBandRouter
variable {S L m C M : ℕ}

theorem total_selected (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    (∑ a : Fin S,∑ normal : Fin (goodSlots L m).card,∑ opposite : Fin (goodSlots L m).card,
      (ids (run right requests hb).value a normal opposite).value.length)=M := by
  simp only [ids,run,FiniteRequestRouter.ids_value]
  have hh := FiniteRequestRouter.group_total (keys right requests hb).value
  unfold count at hh
  rw [← Equiv.sum_comp finProdFinEquiv] at hh
  simp only [Fintype.sum_prod_type] at hh
  simp_rw [← Equiv.sum_comp finProdFinEquiv] at hh
  simp only [Fintype.sum_prod_type] at hh
  exact hh

#print axioms total_selected
end ThinMatrix.GraphOwnBandRoutingTotals
