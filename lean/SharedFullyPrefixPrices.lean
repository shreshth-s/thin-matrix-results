import SharedFullyPrefixWork
import FullyRetainedRootBatch

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace ThinMatrix.SharedFullyPrefixPrices
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open RectangularBatch (Scheme)
open SharedFullyPrefixWork
variable {P ell r C B A Z : ℕ}

theorem price_le {α : Type} (out : Run α) (price : ℕ) :
    out.bitSteps+price*out.control≤(price+1)*(out.bitSteps+out.control) := by nlinarith

theorem schedule_price_volume (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hf : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hl : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H W price : ℕ) (hH : 1≤H) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) (hfit : Z≤B*C)
    (hW : ∀ pair i,SharedFullyAddressedBatch.AddressFits
      (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (PrefixBatchSchedule.digits i)).value.length
      (CappedSubsetList.count ell r) (B*C) A Z W) :
    ((SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests (RoutedPrefixBatch.prepare xs requests).value).bitSteps+
      price*(SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests (RoutedPrefixBatch.prepare xs requests).value).control)*A*Z≤
      (price+1)*(((SharedMatrixSetup.prepare scheme hD hf hl).bitSteps+scheduleControl P ell+
        requests.size*requestUnit (CappedSubsetList.count ell r) (B*C) ell W+
        (2^ell*4^P)*groupUnit (CappedSubsetList.count ell r) B (B*C) A P ell W)*A*Z+
      2*(requests.size+(2^ell*4^P)*A)*(B*C)*
        SharedAddressedCWCosts.workCost scheme (SharedMatrixSetup.prepare scheme hD hf hl).value.depth H) := by
  have hh := SharedFullyPrefixWork.total_work_volume scheme hD hA hZ hf hl xs H W hH hx requests hfit hW
  have hp := Nat.mul_le_mul_right Z (Nat.mul_le_mul_right A
    (price_le (SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests
      (RoutedPrefixBatch.prepare xs requests).value) price))
  have hb := Nat.mul_le_mul_left (price+1) hh
  nlinarith

/-- Exact non-child indexed controls in the retained sum of all windows. -/
def rootExtra (W M Q : ℕ) := 32*W+M*(W*(40*Q+40)+3*Q+44)+3*M+28

theorem root_control_budget {W : ℕ} (f : Fin W → ℕ) (M Q : ℕ) :
    RootProductCollection.controlBudget f M Q=(∑ s,f s)+rootExtra W M Q := by
  simp only [RootProductCollection.controlBudget,GraphPrefixProgram.sumControl,rootExtra,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem root_price {α β : Type} {W M Q : ℕ} (shape : Vector β W)
    (child : Fin W → Run α) (get : α → Fin M → Vector Cell Q) (H price : ℕ)
    (ha : ∀ s i c,(view ((get (child s).value i).get c)).natAbs≤H) :
    (RootProductCollection.execute shape child get).bitSteps+
      price*(RootProductCollection.execute shape child get).control≤
      (∑ s,((child s).bitSteps+price*(child s).control))+
      M*(W*(Q*BackendScalarBits.backendScalarUnit (W*H).size))+
      price*rootExtra W M Q := by
  have hb := RootProductCollection.execute_bits shape child get H (fun s => (child s).bitSteps) ha (fun _ => le_refl _)
  have hc := RootProductCollection.execute_control shape child get (fun s => (child s).control) (fun _ => le_refl _)
  rw [root_control_budget] at hc
  have hp := Nat.mul_le_mul_left price hc
  simp only [RootProductCollection.bitBudget] at hb
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  nlinarith

#print axioms price_le
#print axioms schedule_price_volume
#print axioms root_control_budget
#print axioms root_price
end ThinMatrix.SharedFullyPrefixPrices
