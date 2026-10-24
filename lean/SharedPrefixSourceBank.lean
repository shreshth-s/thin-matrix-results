import RoutedPrefixBatch

set_option autoImplicit false

/-! Retain source completion matrices separately from request routing.
The matrix/key bank is constructed once for a compatible source family and
can be reused for every opposite band. Routing references those retained
arrays and charges only the new request trie and fixed record construction. -/
namespace ThinMatrix.SharedPrefixSourceBank
open BinaryGroupedCoordinates BinaryGroupedPreparation CappedBitPreparation
variable {P ell r C B : ℕ}

structure Prepared (P ell r C B : ℕ) where
  sources : Vector (CappedPrefixProgram.Prepared P ell r C) B
  banks : PrefixBlockBatch.Banks P ell r C B
  keys : Vector (Key ell) (CappedSubsetList.count ell r)
  pairs : Vector (Key ell) (2^ell)

def prepare (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B) : Run (Prepared P ell r C B) :=
  let banks := PrefixBlockBatch.prepare xs
  let keys := GroupedPreparation.storeKeys ell r
  let pairs := GroupedPreparation.storePairs ell
  ⟨⟨xs,banks.value,keys.value,pairs.value⟩,banks.bitSteps,banks.control+keys.work+pairs.work+12⟩

def route (stored : Prepared P ell r C B) (requests : Array (Vector (Fin 4) (P+ell))) :
    Run (RoutedPrefixBatch.Prepared P ell r C B requests.size) :=
  let routing := PrefixRequestRouting.run requests
  ⟨⟨stored.sources,stored.banks,stored.keys,stored.pairs,routing.value⟩,
    routing.bitSteps,routing.control+16⟩

theorem route_value (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (route (prepare xs).value requests).value=(RoutedPrefixBatch.prepare xs requests).value := rfl

theorem route_bits (stored : Prepared P ell r C B) (requests : Array (Vector (Fin 4) (P+ell))) :
    (route stored requests).bitSteps=0 := (PrefixRequestRouting.run_cost requests).1

theorem route_control (stored : Prepared P ell r C B) (requests : Array (Vector (Fin 4) (P+ell))) :
    (route stored requests).control≤
      12*2^(P+(P+ell))+requests.size*(16*(P+(P+ell)+1)^2+64*(P+ell+1)+36)+36 := by
  have h := (PrefixRequestRouting.run_cost requests).2
  simp only [route]
  omega

theorem prepare_bits (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H : ℕ) (hx : ∀ b pair, PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H) :
    (prepare xs).bitSteps≤B*(2^ell*PrefixCompletionMatrices.bitBudget P (CappedSubsetList.count ell r) C H) :=
  PrefixBlockBatch.prepare_bits xs H hx

theorem prepare_control (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B) :
    (prepare xs).control≤
      B*(2^ell*(PrefixCompletionMatrices.controlBudget P (CappedSubsetList.count ell r) C+32)+40)+
      GroupedPreparation.keyBudget ell r+GroupedPreparation.keyBudget ell ell+28 := by
  have hb := PrefixBlockBatch.prepare_control xs
  have hk := GroupedPreparation.storeKeys_work ell r
  have hp := GroupedPreparation.storePairs_work ell
  simp only [prepare]
  omega

theorem combined_bits (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (prepare xs).bitSteps+(route (prepare xs).value requests).bitSteps=
      (RoutedPrefixBatch.prepare xs requests).bitSteps := by
  simp only [prepare,route,RoutedPrefixBatch.prepare]

theorem combined_control (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (prepare xs).control+(route (prepare xs).value requests).control=
      (RoutedPrefixBatch.prepare xs requests).control+12 := by
  simp only [prepare,route,RoutedPrefixBatch.prepare]
  omega

#print axioms route_value
#print axioms route_bits
#print axioms route_control
#print axioms prepare_bits
#print axioms prepare_control
#print axioms combined_bits
#print axioms combined_control
end ThinMatrix.SharedPrefixSourceBank
