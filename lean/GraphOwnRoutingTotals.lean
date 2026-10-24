import GraphOwnRequestRouter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The complete root routing traverses each request once. The two physical
orientations have identical stable occurrence lists after exchanging their
normal/opposite mask indices, allowing paired LOW factors to be joined without
an all-pairs search or expansion of unmatched requests. -/
namespace ThinMatrix.GraphOwnRoutingTotals
open scoped BigOperators
open GoodMapEmbedding GraphOwnRequestRouter
variable {S L m C M : ℕ}

theorem total_selected (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    (∑ a : Fin S, ∑ normal : Fin (goodSlots L m).card,
      ∑ b : Fin S, ∑ opposite : Fin (goodSlots L m).card,
      (ids (run right requests hb).value a b normal opposite).value.length)=M := by
  simp only [ids,run,FiniteRequestRouter.ids_value]
  have hh := FiniteRequestRouter.group_total (keys right requests hb).value
  unfold count at hh
  rw [← Equiv.sum_comp finProdFinEquiv] at hh
  simp only [Fintype.sum_prod_type] at hh
  simp_rw [← Equiv.sum_comp finProdFinEquiv] at hh
  simp only [Fintype.sum_prod_type] at hh
  exact hh

theorem transpose_ids (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (a b : Fin S) (normal opposite : Fin (goodSlots L m).card) :
    (ids (run false requests hb).value a b normal opposite).value=
      (ids (run true requests hb).value a b opposite normal).value := by
  simp only [ids,run,FiniteRequestRouter.ids_value,FiniteRequestRouter.selected]
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,keys,Vector.get_ofFn]
  rw [key_eq_iff,key_eq_iff]
  simp only [RootRequestSelection.accepts,RootRequestSelection.ranks,Bool.false_eq_true,↓reduceIte,
    decide_eq_true_eq]
  tauto

#print axioms total_selected
#print axioms transpose_ids
end ThinMatrix.GraphOwnRoutingTotals
