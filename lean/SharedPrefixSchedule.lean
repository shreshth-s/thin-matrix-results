import SharedPrefixSetup
import PrefixBatchSchedule

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Complete prefix/pair schedule with one binary size selection and actual
binary outer addresses. All chunk/address sums retain the per-group padding
allowance and sum original occurrence counts exactly once. Prefix decoding
and indexed table/scatter controls retain their explicit bounded-index model. -/
namespace ThinMatrix.SharedPrefixSchedule
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open RectangularBatch (Scheme)
open PrefixBatchSchedule (digits decode)
open CompactBlocks (blockCount)
variable {P ell r C B A Z : ℕ}

def execute (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    Run (Vector (Vector (RoutedPrefixBatch.Result requests.size (B*C)) (4^P)) (2^ell)) :=
  let shape := SharedMatrixSetup.prepare scheme hD hfirst hlast
  let allDigits := tabulate (Vector.replicate (4^P) ()) (fun i => decode i)
  let out := tabulate stored.pairs (fun pair =>
    tabulate allDigits.value (fun i =>
      SharedPrefixSetup.group scheme shape.value hA hZ requests stored pair (allDigits.value.get i)))
  ⟨out.value,shape.bitSteps+allDigits.bitSteps+out.bitSteps,allDigits.control+out.control+12⟩

@[simp] theorem execute_get (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) (pair : Fin (2^ell)) (i : Fin (4^P)) :
    ((execute scheme hD hA hZ hfirst hlast requests stored).value.get pair).get i=
      (SharedPrefixSetup.group scheme (SharedMatrixSetup.prepare scheme hD hfirst hlast).value hA hZ
        requests stored pair (digits i)).value := by
  simp only [execute,tabulate_get,decode]

theorem execute_value_eq (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).value=
      (PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests stored).value := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hh : ((execute scheme hD hA hZ hfirst hlast requests stored).value.get ⟨i,hi⟩).get ⟨j,hj⟩=
      ((PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests stored).value.get ⟨i,hi⟩).get ⟨j,hj⟩ := by
    rw [execute_get,PrefixBatchSchedule.execute_get,SharedPrefixSetup.group_value_eq]
  simpa only [Vector.get_eq_getElem] using hh

theorem execute_bits (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).bitSteps=
      (SharedMatrixSetup.prepare scheme hD hfirst hlast).bitSteps+
      ∑ pair : Fin (2^ell),∑ i : Fin (4^P),
        (SharedPrefixSetup.group scheme (SharedMatrixSetup.prepare scheme hD hfirst hlast).value hA hZ
          requests stored pair (digits i)).bitSteps := by
  simp only [execute,tabulate_bits_eq,tabulate_get,decode,Finset.sum_const_zero,add_zero]

theorem execute_control (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).control=
      (∑ pair : Fin (2^ell),∑ i : Fin (4^P),
        (SharedPrefixSetup.group scheme (SharedMatrixSetup.prepare scheme hD hfirst hlast).value hA hZ
          requests stored pair (digits i)).control)+
      4^P*(64*(P+1)^3+32)+2^ell*(32*(4^P)+40)+28 := by
  simp only [execute,tabulate_control_eq,tabulate_get,decode,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem chunk_rows (N A : ℕ) : blockCount N A*A≤N+A := by
  rw [blockCount,Nat.ceilDiv_eq_add_pred_div]
  exact (Nat.div_mul_le_self _ _).trans (by omega)

theorem address_sum_bound (M D Q W : ℕ) (f : Fin (2^ell) → Fin (4^P) → ℕ)
    (hsum : (∑ p,∑ i,f p i)=M) (hfit : Z≤Q) :
    (∑ p,∑ i,SharedAddressedBatch.addressBudget (f p i) D Q A Z W)≤
      ((M+(2^ell*4^P)*A)*D+2*(2^ell*4^P)*Q*D)*(8260*(W+1)^2)+M*Q*(8464*(W+1)^2) := by
  have hp : blockCount Q Z*Z≤2*Q := (chunk_rows Q Z).trans (by omega)
  calc
    _ ≤ ∑ p,∑ i,(((f p i+A)*D+2*Q*D)*(8260*(W+1)^2)+f p i*Q*(8464*(W+1)^2)) := by
      apply Finset.sum_le_sum; intro p _
      apply Finset.sum_le_sum; intro i _
      unfold SharedAddressedBatch.addressBudget
      have hl := Nat.mul_le_mul_right D (chunk_rows (f p i) A)
      have hr := Nat.mul_le_mul_right D hp
      have hr' : blockCount Q Z*D*Z≤2*Q*D := by
        calc
          _ = (blockCount Q Z*Z)*D := by ring
          _ ≤ _ := hr
      exact Nat.add_le_add_right (Nat.mul_le_mul_right (8260*(W+1)^2) (Nat.add_le_add hl hr'))
        (f p i*Q*(8464*(W+1)^2))
    _ = _ := by
      simp only [add_mul,Finset.sum_add_distrib,←Finset.sum_mul,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,hsum]
      ring

def addressBudget (M D Q A P ell W : ℕ) :=
  ((M+(2^ell*4^P)*A)*D+2*(2^ell*4^P)*Q*D)*(8260*(W+1)^2)+M*Q*(8464*(W+1)^2)

theorem address_fits_smaller (n M D Q A Z : ℕ) (hA : 0<A) (hn : n≤M) :
    SharedAddressedBatch.AddressFits n D Q A Z (SharedAddressedBatch.addressSpan M D Q A Z).size := by
  have hglobal := SharedAddressedBatch.address_fits M D Q A Z
  have hc : blockCount n A≤blockCount M A := by
    apply (ceilDiv_le_iff_le_mul hA).mpr
    simpa only [Nat.mul_comm] using hn.trans (CompactBlocks.block_fit M A hA)
  constructor
  · exact (Nat.size_le_size hn).trans hglobal.rows
  · exact hglobal.middle
  · exact hglobal.columns
  · exact hglobal.chunkRows
  · exact hglobal.chunkColumns
  · exact (Nat.size_le_size hc).trans hglobal.rowChunks
  · exact hglobal.columnChunks
  · exact (Nat.size_le_size (Nat.mul_le_mul_right A hc)).trans hglobal.paddedRows
  · exact hglobal.paddedColumns

theorem uniform_address_fit (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) (hA : 0<A)
    (pair : Fin (2^ell)) (i : Fin (4^P)) :
    SharedAddressedBatch.AddressFits
      (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length
      (CappedSubsetList.count ell r) (B*C) A Z
      (SharedAddressedBatch.addressSpan requests.size (CappedSubsetList.count ell r) (B*C) A Z).size := by
  apply address_fits_smaller _ _ _ _ _ _ hA
  rw [RoutedPrefixBatch.ids_value]
  unfold PrefixRequestRouting.selected
  exact (List.length_filter_le _ _).trans (by simp)

theorem total_bits_volume (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H W : ℕ) (hH : 1≤H) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) (hfit : Z≤B*C)
    (hW : ∀ pair i,SharedAddressedBatch.AddressFits
      (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length
      (CappedSubsetList.count ell r) (B*C) A Z W) :
    (execute scheme hD hA hZ hfirst hlast requests (RoutedPrefixBatch.prepare xs requests).value).bitSteps*A*Z≤
      ((SharedMatrixSetup.prepare scheme hD hfirst hlast).bitSteps+
        addressBudget requests.size (CappedSubsetList.count ell r) (B*C) A P ell W)*A*Z+
      2*(requests.size+(2^ell*4^P)*A)*(B*C)*
        BinaryRecursiveCost.bits scheme.base (SharedMatrixSetup.prepare scheme hD hfirst hlast).value.depth H := by
  let f := fun pair i => (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length
  let S := BinaryRecursiveCost.bits scheme.base (SharedMatrixSetup.prepare scheme hD hfirst hlast).value.depth H
  have hf : (∑ pair,∑ i,f pair i)=requests.size := PrefixBatchSchedule.ids_total xs requests
  have hadd := address_sum_bound requests.size (CappedSubsetList.count ell r) (B*C) W f hf hfit (A:=A)
  have htotal := PrefixBatchSchedule.total_fit xs requests hA hZ hfit
  have hgroups : (∑ pair,∑ i,(SharedPrefixSetup.group scheme (SharedMatrixSetup.prepare scheme hD hfirst hlast).value hA hZ
      requests (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).bitSteps)≤
      (∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z)*S+
        addressBudget requests.size (CappedSubsetList.count ell r) (B*C) A P ell W := by
    calc
      _ ≤ ∑ pair,∑ i,(blockCount (f pair i) A*blockCount (B*C) Z*S+
          SharedAddressedBatch.addressBudget (f pair i) (CappedSubsetList.count ell r) (B*C) A Z W) := by
        apply Finset.sum_le_sum; intro pair _
        apply Finset.sum_le_sum; intro i _
        exact SharedPrefixSetup.group_bits scheme _ hA hZ xs H W hH hx requests pair (digits i) (hW pair i)
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib,←Finset.sum_mul]
        exact Nat.add_le_add_left hadd _
  have hscaled := Nat.mul_le_mul_right Z (Nat.mul_le_mul_right A hgroups)
  have hvolume := Nat.mul_le_mul_right S htotal
  have hid : (∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z)*A*Z=
      ∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z*A*Z := by
    simp only [Finset.sum_mul]
  rw [execute_bits]
  change (_+_)*A*Z≤(_+_)*A*Z+_*S
  have hvolume' : (∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z)*A*Z*S≤
      2*(requests.size+(2^ell*4^P)*A)*(B*C)*S := by
    rw [hid]
    exact hvolume
  nlinarith

#print axioms execute_get
#print axioms execute_value_eq
#print axioms execute_bits
#print axioms execute_control
#print axioms chunk_rows
#print axioms address_sum_bound
#print axioms address_fits_smaller
#print axioms uniform_address_fit
#print axioms total_bits_volume
end ThinMatrix.SharedPrefixSchedule
