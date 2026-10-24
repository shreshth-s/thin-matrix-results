import RoutedPrefixBatch
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! All compatible prefix/pair batches are executed once. Request counts sum
to the original occurrence count; padded row costs therefore pay one row
allowance per group, rather than all requests once per group. -/
namespace ThinMatrix.PrefixBatchSchedule
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open CappedBitPreparation (Key)
open GroupedPreparation (keyVector pairKeys)
open RectangularBatch (Scheme)
variable {P ell r C B A Z : ℕ}

def digits (i : Fin (4^P)) : Vector (Fin 4) P := Vector.ofFn (finFunctionFinEquiv.symm i)
def rank (v : Vector (Fin 4) P) : Fin (4^P) := finFunctionFinEquiv v.get

@[simp] theorem digits_rank (v : Vector (Fin 4) P) : digits (rank v)=v := by
  apply Vector.ext
  intro i hi
  simp [digits,rank,Vector.get_eq_getElem]

@[simp] theorem rank_digits (i : Fin (4^P)) : rank (digits i)=i := by
  unfold rank digits
  have hh : (Vector.ofFn (finFunctionFinEquiv.symm i)).get=finFunctionFinEquiv.symm i := by
    funext j; exact Vector.get_ofFn _ _
  rw [hh,Equiv.apply_symm_apply]

theorem digits_eq_iff (v : Vector (Fin 4) P) (i : Fin (4^P)) : v=digits i ↔ rank v=i := by
  constructor
  · intro h; rw [h,rank_digits]
  · intro h; rw [←h,digits_rank]

theorem pair_eq_iff (v : Key ell) (i : Fin (2^ell)) :
    v=(pairKeys ell).get i ↔ (PrefixRequestKey.locate (pairKeys ell) v).value=i := by
  constructor
  · intro h; rw [h,RoutedPrefixBatch.pair_locate]
  · intro h; rw [←h,PrefixRequestKey.locate_get _ rfl]

theorem filter_length {X : Type} (p : X → Bool) (xs : List X) :
    (xs.filter p).length=(xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih,Nat.add_comm]

theorem selected_length (requests : Array (Vector (Fin 4) (P+ell)))
    (pair : Fin (2^ell)) (i : Fin (4^P)) :
    (PrefixRequestRouting.selected requests (digits i) ((pairKeys ell).get pair)).length=
      ∑ j : Fin requests.size, if rank (PrefixRequestKey.prefixPart requests[j.val])=i ∧
        (PrefixRequestKey.locate (pairKeys ell) (PrefixRequestKey.pairPart requests[j.val])).value=pair then 1 else 0 := by
  unfold PrefixRequestRouting.selected
  rw [filter_length]
  change (List.map _ (List.ofFn (fun j : Fin requests.size => j))).sum=_
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,decide_eq_true_eq,digits_eq_iff,pair_eq_iff]

theorem selected_total (requests : Array (Vector (Fin 4) (P+ell))) :
    (∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
      (PrefixRequestRouting.selected requests (digits i) ((pairKeys ell).get pair)).length)=requests.size := by
  simp only [selected_length]
  conv_lhs => arg 2; ext pair; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have one (j : Fin requests.size) :
      (∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
        if rank (PrefixRequestKey.prefixPart requests[j.val])=i ∧
          (PrefixRequestKey.locate (pairKeys ell) (PrefixRequestKey.pairPart requests[j.val])).value=pair
          then 1 else 0)=1 := by
    simp only [ite_and]
    simp
  simp only [one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

theorem ids_total (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
      (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length)=requests.size := by
  simp only [RoutedPrefixBatch.ids_value]
  exact selected_total requests

/-- Prefix indices are decoded by explicit quotient/remainder. This charge
includes every fixed-base power and every copied digit; binary-address costs
remain a separate implementation refinement. -/
def decode (i : Fin (4^P)) : Run (Vector (Fin 4) P) :=
  ⟨digits i,0,64*(P+1)^3⟩

def execute (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    Run (Vector (Vector (RoutedPrefixBatch.Result requests.size (B*C)) (4^P)) (2^ell)) :=
  let allDigits := tabulate (Vector.replicate (4^P) ()) (fun i => decode i)
  let out := tabulate stored.pairs (fun pair =>
    tabulate allDigits.value (fun i =>
      RoutedPrefixBatch.group scheme hD hA hZ hfirst hlast requests stored pair (allDigits.value.get i)))
  ⟨out.value,allDigits.bitSteps+out.bitSteps,allDigits.control+out.control+8⟩

@[simp] theorem execute_get (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) (pair : Fin (2^ell)) (i : Fin (4^P)) :
    ((execute scheme hD hA hZ hfirst hlast requests stored).value.get pair).get i=
      (RoutedPrefixBatch.group scheme hD hA hZ hfirst hlast requests stored pair (digits i)).value := by
  simp only [execute,tabulate_get,decode]

theorem execute_bits (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).bitSteps=
      ∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
        (RoutedPrefixBatch.group scheme hD hA hZ hfirst hlast requests stored pair (digits i)).bitSteps := by
  simp only [execute,tabulate_bits_eq,tabulate_get,decode,Finset.sum_const_zero,zero_add]

theorem execute_control (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).control=
      (∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
        (RoutedPrefixBatch.group scheme hD hA hZ hfirst hlast requests stored pair (digits i)).control)+
      4^P*(64*(P+1)^3+32)+2^ell*(32*(4^P)+40)+24 := by
  simp only [execute,tabulate_control_eq,tabulate_get,decode,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

/-- Aggregate padded chunk volume, using only actual B*C independent columns.
The row-padding overhead is A per group, not the original request count. -/
theorem total_fit (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) (hA : 0<A) (hZ : 0<Z) (hfit : Z≤B*C) :
    (∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
      CompactBlocks.blockCount (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length A*
      CompactBlocks.blockCount (B*C) Z*A*Z)≤2*(requests.size+(2^ell*4^P)*A)*(B*C) := by
  calc
    _ ≤ ∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
        2*((RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length+A)*(B*C) := by
      apply Finset.sum_le_sum; intro pair _
      apply Finset.sum_le_sum; intro i _
      exact PrefixBlockBatch.independent_fit _ _ _ _ _ hA hZ hfit
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,ids_total]
      ring

theorem total_bits_volume (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H : ℕ) (hH : 1≤H) (hx : ∀ b pair, PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) (hfit : Z≤B*C) :
    (execute scheme hD hA hZ hfirst hlast requests (RoutedPrefixBatch.prepare xs requests).value).bitSteps*A*Z≤
      2*(requests.size+(2^ell*4^P)*A)*(B*C)*RectangularBatch.scalarBudget scheme (CappedSubsetList.count ell r) H := by
  rw [execute_bits,Finset.sum_mul,Finset.sum_mul]
  calc
    _ ≤ ∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
        (CompactBlocks.blockCount (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length A*
          CompactBlocks.blockCount (B*C) Z*A*Z)*RectangularBatch.scalarBudget scheme (CappedSubsetList.count ell r) H := by
      apply Finset.sum_le_sum; intro pair _
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_le_sum; intro i _
      have hh := Nat.mul_le_mul_right Z (Nat.mul_le_mul_right A
        (RoutedPrefixBatch.group_bits scheme hD hA hZ hfirst hlast xs H hH hx requests pair (digits i)))
      convert hh using 1 <;> first | rfl | ring
    _ = (∑ pair : Fin (2^ell), ∑ i : Fin (4^P),
        CompactBlocks.blockCount (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (digits i)).value.length A*
          CompactBlocks.blockCount (B*C) Z*A*Z)*RectangularBatch.scalarBudget scheme (CappedSubsetList.count ell r) H := by
      simp only [Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (total_fit xs requests hA hZ hfit)

#print axioms digits_rank
#print axioms rank_digits
#print axioms digits_eq_iff
#print axioms pair_eq_iff
#print axioms selected_length
#print axioms selected_total
#print axioms ids_total
#print axioms execute_get
#print axioms execute_bits
#print axioms execute_control
#print axioms total_fit
#print axioms total_bits_volume
end ThinMatrix.PrefixBatchSchedule
