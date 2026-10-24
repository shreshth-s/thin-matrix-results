import SharedFullyPrefixSchedule
import RoutedPrefixScatter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Complete addressed shared-setup schedule with restoration to original
occurrence order. IndexedRowScatter's Vector.set is interpreted in the same
bounded indexed-write counter model as the existing program. These counters
do not assert Lean runtime reference uniqueness or copy-on-write costs. -/
namespace ThinMatrix.SharedFullyPrefixScatter
open BinaryCell BinaryGroupedCoordinates
open RectangularBatch (Scheme)
open GroupedPreparation (keyVector pairKeys)
open RoutedPrefixScatter (collect)
variable {P ell r C B A Z : ℕ}

def execute (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) : Run (Vector (Vector Cell (B*C)) requests.size) :=
  let batches := SharedFullyPrefixSchedule.execute scheme hD hA hZ hfirst hlast requests stored
  let rows := collect batches.value
  let blank := Vector.replicate (B*C) zero
  let initial := Vector.replicate requests.size blank
  let out := IndexedRowScatter.run rows.value initial
  ⟨out.value,batches.bitSteps+rows.bitSteps+out.bitSteps,
    batches.control+rows.control+out.control+32*(requests.size+B*C+1)⟩

theorem execute_value_eq (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).value=
      (RoutedPrefixScatter.execute scheme hD hA hZ hfirst hlast requests stored).value := by
  simp only [execute,RoutedPrefixScatter.execute,SharedFullyPrefixSchedule.execute_value_eq]

theorem correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (hk : ∀ b,(xs.get b).grouped.keys=keyVector ell r)
    (hp : ∀ b,(xs.get b).grouped.pairs=pairKeys ell)
    (requests : Array (Vector (Fin 4) (P+ell))) (j : Fin requests.size) (b : Fin B) (c : Fin C) :
    view (((execute scheme hD hA hZ hfirst hlast requests (RoutedPrefixBatch.prepare xs requests).value).value.get j).get
      (PrefixBlockBatch.column b c))=
      view ((PrefixCompletionProgram.row (xs.get b) (PrefixCompletionMatrices.prepare (xs.get b)).value
        requests[j.val]).value.output.get c) := by
  rw [execute_value_eq]
  exact RoutedPrefixScatter.correct scheme hv hD hA hZ hfirst hlast xs hk hp requests j b c

theorem bits (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).bitSteps=
      (SharedFullyPrefixSchedule.execute scheme hD hA hZ hfirst hlast requests stored).bitSteps := by
  simp only [execute,IndexedRowScatter.bits,collect,add_zero]

theorem control (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (execute scheme hD hA hZ hfirst hlast requests (RoutedPrefixBatch.prepare xs requests).value).control=
      (SharedFullyPrefixSchedule.execute scheme hD hA hZ hfirst hlast requests
        (RoutedPrefixBatch.prepare xs requests).value).control+
      128*requests.size+32*(2^ell)*(4^P+1)+32*(B*C)+52 := by
  have hn : (collect (SharedFullyPrefixSchedule.execute scheme hD hA hZ hfirst hlast requests
      (RoutedPrefixBatch.prepare xs requests).value).value).value.length=requests.size := by
    rw [SharedFullyPrefixSchedule.execute_value_eq]
    exact RoutedPrefixScatter.output_count scheme hD hA hZ hfirst hlast xs requests
  simp only [collect] at hn
  simp only [execute,IndexedRowScatter.control,collect]
  rw [hn]
  ring

#print axioms execute_value_eq
#print axioms correct
#print axioms bits
#print axioms control
end ThinMatrix.SharedFullyPrefixScatter
