import SharedFullyAddressedBatch
import RoutedPrefixBatch

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Production prefix-group adapter consuming a shared, already charged
matrix shape. Complete coefficients and original request indices remain
unchanged. The adapter calls the binary-addressed chunk implementation. -/
namespace ThinMatrix.SharedFullyPrefixSetup
open scoped BigOperators
open BinaryCell BinaryRecursiveDot
open RecursiveTable (Table read)
open RectangularBatch (Scheme)
open CappedBitPreparation (Key)
variable {D C A Z P ell r B : ℕ}

def matrix (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A Z)
    (hA : 0<A) (hZ : 0<Z) (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) :=
  let left := SharedGroupedCompletion.selectors M
  let right := SharedGroupedCompletion.data X
  let product := SharedFullyAddressedBatch.run scheme shape hA hZ left.value right.value
  let out := SharedGroupedCompletion.rows product.value
  (⟨out.value,left.bitSteps+right.bitSteps+product.bitSteps+out.bitSteps,
    left.control+right.control+product.control+out.control+16⟩ : Run (Array (Vector Cell C)))

@[simp] theorem matrix_size (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A Z)
    (hA : 0<A) (hZ : 0<Z) (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) :
    (matrix scheme shape hA hZ M X).value.size=M.size := by
  simp only [matrix,SharedGroupedCompletion.rows,Array.size_ofFn]

theorem matrix_value_eq (scheme : Scheme) (hD : 0<D) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤D^scheme.num) (hlast : Z≤D^scheme.z)
    (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) :
    (matrix scheme (SharedMatrixSetup.prepare scheme hD hfirst hlast).value hA hZ M X).value=
      (SharedGroupedCompletion.complete scheme hD hA hZ hfirst hlast M X).value := by
  simp only [matrix,SharedGroupedCompletion.complete,SharedFullyAddressedBatch.run_value_eq,
    SharedMatrixSetup.run_value_eq]

theorem matrix_bits (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A Z)
    (hA : 0<A) (hZ : 0<Z) (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D)
    (H W : ℕ) (hH : 1≤H) (hW : SharedFullyAddressedBatch.AddressFits M.size D C A Z W)
    (hX : ∀ i j,(view ((X.get i).get j)).natAbs≤H) :
    (matrix scheme shape hA hZ M X).bitSteps≤
      CompactBlocks.blockCount M.size A*CompactBlocks.blockCount C Z*
        SharedFullyAddressedBatch.productCost scheme shape.depth H+SharedFullyAddressedBatch.addressBudget M.size D C A Z W := by
  have hl : BinaryRetainedBounds.Bounded (SharedGroupedCompletion.selectors M).value H := by
    intro i
    simp only [SharedGroupedCompletion.selectors,tabulate_read]
    split_ifs
    · simpa using hH
    · simp
  have hr : BinaryRetainedBounds.Bounded (SharedGroupedCompletion.data X).value H := by
    intro i
    simpa only [SharedGroupedCompletion.data,tabulate_read] using hX i.1 i.2
  have hh := SharedFullyAddressedBatch.run_bits scheme shape hA hZ H W hH hW _ _ hl hr
  simpa only [matrix,SharedGroupedCompletion.selectors,SharedGroupedCompletion.data,SharedGroupedCompletion.rows,
    tabulate_bits,Finset.sum_const_zero,zero_add,add_zero] using hh

theorem matrix_control (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A Z)
    (hA : 0<A) (hZ : 0<Z) (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) :
    (matrix scheme shape hA hZ M X).control=
      (SharedFullyAddressedBatch.run scheme shape hA hZ
        (SharedGroupedCompletion.selectors M).value (SharedGroupedCompletion.data X).value).control+
      40*(M.size*D+D*C+M.size*C)+32*M.size+40 := by
  simp only [matrix,SharedGroupedCompletion.selectors,SharedGroupedCompletion.data,SharedGroupedCompletion.rows,
    tabulate_control,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul,
    PaddedMatrix.matrix,RecursiveTable.prod,RecursiveTable.fin]
  ring

def complete (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (banks : PrefixBlockBatch.Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (requests : Array (Key ell)) : Run (Array (Vector Cell (B*C))) :=
  let masks := GroupedPreparation.selectors keys requests
  let source := PrefixBlockBatch.data banks pair digits
  let out := matrix scheme shape hA hZ masks.value source.value
  ⟨out.value,source.bitSteps+out.bitSteps,masks.work+source.control+out.control+12⟩

@[simp] theorem complete_size (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (banks : PrefixBlockBatch.Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (requests : Array (Key ell)) :
    (complete scheme shape hA hZ keys banks pair digits requests).value.size=requests.size := by
  simp only [complete,matrix_size,GroupedPreparation.selectors_size]

theorem complete_value_eq (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (banks : PrefixBlockBatch.Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (requests : Array (Key ell)) :
    (complete scheme (SharedMatrixSetup.prepare scheme hD hfirst hlast).value hA hZ keys banks pair digits requests).value=
      (PrefixBlockBatch.complete scheme hD hA hZ hfirst hlast keys banks pair digits requests).value := by
  simp only [complete,PrefixBlockBatch.complete,matrix_value_eq]

theorem complete_bits (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (H W : ℕ) (hH : 1≤H) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) (requests : Array (Key ell))
    (hW : SharedFullyAddressedBatch.AddressFits requests.size (CappedSubsetList.count ell r) (B*C) A Z W) :
    (complete scheme shape hA hZ keys (PrefixBlockBatch.prepare xs).value pair digits requests).bitSteps≤
      CompactBlocks.blockCount requests.size A*CompactBlocks.blockCount (B*C) Z*
        SharedFullyAddressedBatch.productCost scheme shape.depth H+
        SharedFullyAddressedBatch.addressBudget requests.size (CappedSubsetList.count ell r) (B*C) A Z W := by
  have hh := matrix_bits scheme shape hA hZ (GroupedPreparation.selectors keys requests).value
    (PrefixBlockBatch.data (PrefixBlockBatch.prepare xs).value pair digits).value H W hH
    (by simpa only [GroupedPreparation.selectors_size] using hW) (PrefixBlockBatch.data_bound xs H hx pair digits)
  simpa only [complete,PrefixBlockBatch.data_bits,zero_add,GroupedPreparation.selectors_size] using hh

theorem complete_control (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (banks : PrefixBlockBatch.Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (requests : Array (Key ell)) :
    (complete scheme shape hA hZ keys banks pair digits requests).control≤
      (matrix scheme shape hA hZ (GroupedPreparation.selectors keys requests).value
        (PrefixBlockBatch.data banks pair digits).value).control+
      requests.size*(CappedSubsetList.count ell r*(26*ell+24)+20)+
      B*(16*(P+1)^2+40)+CappedSubsetList.count ell r*(44*(B*C)+40)+40 := by
  have hh := GroupedPreparation.selectors_work keys requests
  simp only [complete,PrefixBlockBatch.data_control]
  omega

def group (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) : Run (RoutedPrefixBatch.Result requests.size (B*C)) :=
  let selected := RoutedPrefixBatch.ids stored pair digits
  let masks := RoutedPrefixBatch.actives requests selected.value
  let out := complete scheme shape hA hZ stored.keys stored.banks pair digits masks.value
  ⟨⟨selected.value,out.value,by simp [out,masks]⟩,
    selected.bitSteps+out.bitSteps,selected.control+masks.work+out.control+12⟩

theorem group_value_eq (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (group scheme (SharedMatrixSetup.prepare scheme hD hfirst hlast).value hA hZ requests stored pair digits).value=
      (RoutedPrefixBatch.group scheme hD hA hZ hfirst hlast requests stored pair digits).value := by
  simp only [group,RoutedPrefixBatch.group,complete_value_eq]

theorem group_bits (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H W : ℕ) (hH : 1≤H) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (hW : SharedFullyAddressedBatch.AddressFits (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value.length
      (CappedSubsetList.count ell r) (B*C) A Z W) :
    (group scheme shape hA hZ requests (RoutedPrefixBatch.prepare xs requests).value pair digits).bitSteps≤
      CompactBlocks.blockCount (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value.length A*
        CompactBlocks.blockCount (B*C) Z*SharedFullyAddressedBatch.productCost scheme shape.depth H+
        SharedFullyAddressedBatch.addressBudget (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value.length
          (CappedSubsetList.count ell r) (B*C) A Z W := by
  have hh := complete_bits scheme shape hA hZ xs (GroupedPreparation.keyVector ell r) H W hH hx pair digits
    (RoutedPrefixBatch.actives requests (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair digits).value).value
    (by simpa only [RoutedPrefixBatch.actives_size] using hW)
  simpa only [group,RoutedPrefixBatch.prepare,GroupedPreparation.storeKeys_value,RoutedPrefixBatch.actives_size,
    RoutedPrefixBatch.ids,BooleanRequestRouter.read_bits,zero_add] using hh

theorem group_control (scheme : Scheme)
    (shape : SharedMatrixSetup.Shape scheme (CappedSubsetList.count ell r) A Z)
    (hA : 0<A) (hZ : 0<Z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (group scheme shape hA hZ requests stored pair digits).control≤
      (complete scheme shape hA hZ stored.keys stored.banks pair digits
        (RoutedPrefixBatch.actives requests (RoutedPrefixBatch.ids stored pair digits).value).value).control+
      (RoutedPrefixBatch.ids stored pair digits).value.length*(16*ell+16)+
      16*(P+(P+ell)+1)^2+32*(P+ell+1)+16 := by
  have hh := RoutedPrefixBatch.ids_control stored pair digits
  simp only [group,RoutedPrefixBatch.actives]
  omega

#print axioms matrix_size
#print axioms matrix_value_eq
#print axioms matrix_bits
#print axioms matrix_control
#print axioms complete_size
#print axioms complete_value_eq
#print axioms complete_bits
#print axioms complete_control
#print axioms group_value_eq
#print axioms group_bits
#print axioms group_control
end ThinMatrix.SharedFullyPrefixSetup
