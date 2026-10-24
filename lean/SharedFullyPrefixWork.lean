import SharedFullyPrefixSchedule
import SharedAddressedCWCosts

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Closed indexed work ledger for the complete shared prefix schedule.
The formula includes matrix selectors, data copying, routing, padded chunks,
binary recursive products, decoded prefixes, and the single shape setup. -/
namespace ThinMatrix.SharedFullyPrefixWork
open scoped BigOperators
open BinaryCell BinaryRecursiveDot
open RecursiveTable (Table read)
open RectangularBatch (Scheme)
open SharedFullyPrefixSetup
open CompactBlocks (blockCount)
variable {D C A Z P ell r B : ℕ}

def matrixExtra (N D Q : ℕ) := 40*(N*D+D*Q+N*Q)+32*N+40

def completeExtra (N D B Q P ell : ℕ) :=
  N*(D*(26*ell+24)+20)+B*(16*(P+1)^2+40)+D*(44*Q+40)+40

def groupExtra (N P ell : ℕ) := N*(16*ell+16)+16*(P+(P+ell)+1)^2+32*(P+ell+1)+16

def extra (N D B Q A Z P ell W : ℕ) :=
  SharedFullyAddressedBatch.addressBudget N D Q A Z W+
  SharedAddressedCWCosts.outerControl N D Q A Z+
  matrixExtra N D Q+completeExtra N D B Q P ell+groupExtra N P ell

theorem matrix_work (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A Z)
    (hA : 0<A) (hZ : 0<Z) (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D)
    (H W : ℕ) (hH : 1≤H) (hW : SharedFullyAddressedBatch.AddressFits M.size D C A Z W)
    (hX : ∀ i j,(view ((X.get i).get j)).natAbs≤H) :
    (matrix scheme shape hA hZ M X).bitSteps+(matrix scheme shape hA hZ M X).control≤
      blockCount M.size A*blockCount C Z*SharedAddressedCWCosts.workCost scheme shape.depth H+
      SharedFullyAddressedBatch.addressBudget M.size D C A Z W+
      SharedAddressedCWCosts.outerControl M.size D C A Z+matrixExtra M.size D C := by
  have hl : BinaryRetainedBounds.Bounded (SharedGroupedCompletion.selectors M).value H := by
    intro i
    simp only [SharedGroupedCompletion.selectors,tabulate_read]
    split_ifs
    · simpa using hH
    · simp
  have hr : BinaryRetainedBounds.Bounded (SharedGroupedCompletion.data X).value H := by
    intro i
    simpa only [SharedGroupedCompletion.data,tabulate_read] using hX i.1 i.2
  have hh := SharedAddressedCWCosts.run_work scheme shape hA hZ H W hH hW _ _ hl hr
  have hb : (matrix scheme shape hA hZ M X).bitSteps=
      (SharedFullyAddressedBatch.run scheme shape hA hZ (SharedGroupedCompletion.selectors M).value
        (SharedGroupedCompletion.data X).value).bitSteps := by
    simp only [matrix,SharedGroupedCompletion.selectors,SharedGroupedCompletion.data,SharedGroupedCompletion.rows,
      tabulate_bits,Finset.sum_const_zero,zero_add,add_zero]
  rw [hb,matrix_control]
  unfold matrixExtra
  omega

theorem complete_work (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z) (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (keys : Vector (CappedBitPreparation.Key ell) (CappedSubsetList.count ell r))
    (H W : ℕ) (hH : 1≤H) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) (requests : Array (CappedBitPreparation.Key ell))
    (hW : SharedFullyAddressedBatch.AddressFits requests.size (CappedSubsetList.count ell r) (B*C) A Z W) :
    (complete scheme shape hA hZ keys (PrefixBlockBatch.prepare xs).value pair digits requests).bitSteps+
    (complete scheme shape hA hZ keys (PrefixBlockBatch.prepare xs).value pair digits requests).control≤
      blockCount requests.size A*blockCount (B*C) Z*SharedAddressedCWCosts.workCost scheme shape.depth H+
      SharedFullyAddressedBatch.addressBudget requests.size (CappedSubsetList.count ell r) (B*C) A Z W+
      SharedAddressedCWCosts.outerControl requests.size (CappedSubsetList.count ell r) (B*C) A Z+
      matrixExtra requests.size (CappedSubsetList.count ell r) (B*C)+
      completeExtra requests.size (CappedSubsetList.count ell r) B (B*C) P ell := by
  have hh := matrix_work scheme shape hA hZ (GroupedPreparation.selectors keys requests).value
    (PrefixBlockBatch.data (PrefixBlockBatch.prepare xs).value pair digits).value H W hH
    (by simpa only [GroupedPreparation.selectors_size] using hW) (PrefixBlockBatch.data_bound xs H hx pair digits)
  simp only [GroupedPreparation.selectors_size] at hh
  have hc := complete_control scheme shape hA hZ keys (PrefixBlockBatch.prepare xs).value pair digits requests
  have hb : (complete scheme shape hA hZ keys (PrefixBlockBatch.prepare xs).value pair digits requests).bitSteps=
      (matrix scheme shape hA hZ (GroupedPreparation.selectors keys requests).value
        (PrefixBlockBatch.data (PrefixBlockBatch.prepare xs).value pair digits).value).bitSteps := by
    simp only [complete,PrefixBlockBatch.data_bits,zero_add]
  rw [hb]
  unfold completeExtra
  omega

theorem group_work (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z) (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H W : ℕ) (hH : 1≤H) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (hW : SharedFullyAddressedBatch.AddressFits (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value.length
      (CappedSubsetList.count ell r) (B*C) A Z W) :
    (group scheme shape hA hZ requests (RoutedPrefixBatch.prepare xs requests).value pair digits).bitSteps+
    (group scheme shape hA hZ requests (RoutedPrefixBatch.prepare xs requests).value pair digits).control≤
      blockCount (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value.length A*
      blockCount (B*C) Z*SharedAddressedCWCosts.workCost scheme shape.depth H+
      extra (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value.length
        (CappedSubsetList.count ell r) B (B*C) A Z P ell W := by
  have hh := complete_work scheme shape hA hZ xs (GroupedPreparation.keyVector ell r) H W hH hx pair digits
    (RoutedPrefixBatch.actives requests (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value).value
    (by simpa only [RoutedPrefixBatch.actives_size] using hW)
  have hc := group_control scheme shape hA hZ requests (RoutedPrefixBatch.prepare xs requests).value pair digits
  simp only [RoutedPrefixBatch.prepare,GroupedPreparation.storeKeys_value] at hc
  simp only [RoutedPrefixBatch.actives_size] at hh
  have hb : (group scheme shape hA hZ requests (RoutedPrefixBatch.prepare xs requests).value pair digits).bitSteps=
      (complete scheme shape hA hZ (GroupedPreparation.keyVector ell r) (PrefixBlockBatch.prepare xs).value pair digits
        (RoutedPrefixBatch.actives requests (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value).value).bitSteps := by
    simp only [group,RoutedPrefixBatch.prepare,GroupedPreparation.storeKeys_value,
      RoutedPrefixBatch.ids,BooleanRequestRouter.read_bits,zero_add]
  rw [hb]
  unfold extra groupExtra
  simp only [RoutedPrefixBatch.prepare,GroupedPreparation.storeKeys_value] at hh hc ⊢
  omega

/-- The number of stored cells per group bounds all outer chunk traversal,
with the required padded-row allowance retained. -/
theorem outer_control (N D Q A Z : ℕ) (hA : 0<A) (hZ : 0<Z) (hfit : Z≤Q) :
    SharedAddressedCWCosts.outerControl N D Q A Z≤
      56*((N+A)*D+2*Q*D)+40*(N+Q)+88*N*Q+48 := by
  have hr : blockCount N A≤N := (ceilDiv_le_iff_le_mul hA).mpr (Nat.le_mul_of_pos_left _ hA)
  have hc : blockCount Q Z≤Q := (ceilDiv_le_iff_le_mul hZ).mpr (Nat.le_mul_of_pos_left _ hZ)
  have hprod := Nat.mul_le_mul hr hc
  have hrows := SharedFullyPrefixSchedule.chunk_rows N A
  have hcols := (SharedFullyPrefixSchedule.chunk_rows Q Z).trans (show Q+Z≤2*Q by omega)
  unfold SharedAddressedCWCosts.outerControl
  nlinarith [Nat.mul_le_mul_right (56*D) hrows,Nat.mul_le_mul_right (56*D) hcols]

def requestUnit (D Q ell W : ℕ) :=
  D*(8260*(W+1)^2)+Q*(8464*(W+1)^2)+56*D+40+88*Q+
  40*(D+Q)+32+(D*(26*ell+24)+20)+(16*ell+16)

def groupUnit (D B Q A P ell W : ℕ) :=
  (A*D+2*Q*D)*(8260*(W+1)^2)+56*(A*D+2*Q*D)+40*Q+48+
  40*D*Q+40+B*(16*(P+1)^2+40)+D*(44*Q+40)+40+
  16*(P+(P+ell)+1)^2+32*(P+ell+1)+16

theorem extra_bound (N D B Q A Z P ell W : ℕ) (hA : 0<A) (hZ : 0<Z) (hfit : Z≤Q) :
    extra N D B Q A Z P ell W≤N*requestUnit D Q ell W+groupUnit D B Q A P ell W := by
  have hc := outer_control N D Q A Z hA hZ hfit
  have hr := SharedFullyPrefixSchedule.chunk_rows N A
  have hz := (SharedFullyPrefixSchedule.chunk_rows Q Z).trans (show Q+Z≤2*Q by omega)
  have haddr : SharedFullyAddressedBatch.addressBudget N D Q A Z W≤
      ((N+A)*D+2*Q*D)*(8260*(W+1)^2)+N*Q*(8464*(W+1)^2) := by
    unfold SharedFullyAddressedBatch.addressBudget
    have hh : blockCount N A*A*D+blockCount Q Z*D*Z≤(N+A)*D+2*Q*D := by
      nlinarith [Nat.mul_le_mul_right D hr,Nat.mul_le_mul_right D hz]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hh) _
  unfold extra matrixExtra completeExtra groupExtra requestUnit groupUnit
  nlinarith

def scheduleControl (P ell : ℕ) := 4^P*(64*(P+1)^3+32)+2^ell*(32*(4^P)+40)+28

theorem total_work_volume (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hf : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hl : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H W : ℕ) (hH : 1≤H) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) (hfit : Z≤B*C)
    (hW : ∀ pair i,SharedFullyAddressedBatch.AddressFits
      (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (PrefixBatchSchedule.digits i)).value.length
      (CappedSubsetList.count ell r) (B*C) A Z W) :
    ((SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests (RoutedPrefixBatch.prepare xs requests).value).bitSteps+
      (SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests (RoutedPrefixBatch.prepare xs requests).value).control)*A*Z≤
      ((SharedMatrixSetup.prepare scheme hD hf hl).bitSteps+scheduleControl P ell+
        requests.size*requestUnit (CappedSubsetList.count ell r) (B*C) ell W+
        (2^ell*4^P)*groupUnit (CappedSubsetList.count ell r) B (B*C) A P ell W)*A*Z+
      2*(requests.size+(2^ell*4^P)*A)*(B*C)*
        SharedAddressedCWCosts.workCost scheme (SharedMatrixSetup.prepare scheme hD hf hl).value.depth H := by
  let f := fun pair i => (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (PrefixBatchSchedule.digits i)).value.length
  let S := SharedAddressedCWCosts.workCost scheme (SharedMatrixSetup.prepare scheme hD hf hl).value.depth H
  have hsum : (∑ pair,∑ i,f pair i)=requests.size := PrefixBatchSchedule.ids_total xs requests
  have hextra : (∑ pair,∑ i,extra (f pair i) (CappedSubsetList.count ell r) B (B*C) A Z P ell W)≤
      requests.size*requestUnit (CappedSubsetList.count ell r) (B*C) ell W+
      (2^ell*4^P)*groupUnit (CappedSubsetList.count ell r) B (B*C) A P ell W := by
    calc
      _≤∑ pair,∑ i,(f pair i*requestUnit (CappedSubsetList.count ell r) (B*C) ell W+
        groupUnit (CappedSubsetList.count ell r) B (B*C) A P ell W) := by
        apply Finset.sum_le_sum;intro pair _
        apply Finset.sum_le_sum;intro i _
        exact extra_bound _ _ _ _ _ _ _ _ _ hA hZ hfit
      _=_ := by simp only [Finset.sum_add_distrib,←Finset.sum_mul,hsum,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hgroups := Finset.sum_le_sum (fun pair (_ : pair∈Finset.univ) =>
    Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
      group_work scheme (SharedMatrixSetup.prepare scheme hD hf hl).value hA hZ xs H W hH hx requests pair
        (PrefixBatchSchedule.digits i) (hW pair i)))
  have hscaled := Nat.mul_le_mul_right Z (Nat.mul_le_mul_right A hgroups)
  have htotal := PrefixBatchSchedule.total_fit xs requests hA hZ hfit
  have hvol := Nat.mul_le_mul_right S htotal
  have hid : (∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z)*A*Z=
      ∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z*A*Z := by simp only [Finset.sum_mul]
  have hvol' : (∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z)*S*A*Z≤
      2*(requests.size+(2^ell*4^P)*A)*(B*C)*S := by
    have hh : (∑ pair,∑ i,blockCount (f pair i) A*blockCount (B*C) Z)*A*Z*S≤2*(requests.size+(2^ell*4^P)*A)*(B*C)*S := by rw [hid];exact hvol
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  simp only [Finset.sum_add_distrib,←Finset.sum_mul] at hscaled hvol'
  rw [SharedFullyPrefixSchedule.execute_bits,SharedFullyPrefixSchedule.execute_control]
  have hextra' := Nat.mul_le_mul_right Z (Nat.mul_le_mul_right A hextra)
  dsimp only [S,f] at hscaled hvol' hextra'
  unfold scheduleControl
  nlinarith

#print axioms matrix_work
#print axioms complete_work
#print axioms group_work
#print axioms outer_control
#print axioms extra_bound
#print axioms total_work_volume
end ThinMatrix.SharedFullyPrefixWork
