import PrefixRequestKey
import BinaryGroupedCompletion

set_option autoImplicit false

/-! Concrete elementary completion from retained prefix cells. The matrix bank
is copied once; requests, including duplicates, each retain their decomposed
key, selector row and complete coefficient output. Tree selection is charged
quadratically for the generated suffix closures. Control is indexed work, not
binary address execution. No fast rectangular algorithm is assumed. -/
namespace ThinMatrix.PrefixCompletionProgram
open BinaryCell BinaryGroupedCoordinates CappedBitPreparation GroupedPreparation
open scoped BigOperators

structure Completed (P ell r C : ℕ) where
  labels : Vector (Fin 4) (P+ell)
  key : PrefixRequestKey.Request P ell
  selector : Vector Bool (CappedSubsetList.count ell r)
  output : Vector Cell C

def row {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (matrices : PrefixCompletionMatrices.Prepared P ell r C)
    (labels : Vector (Fin 4) (P+ell)) : Run (Completed P ell r C) :=
  let key := PrefixRequestKey.make xs.grouped.pairs labels
  let selector := selectorRow xs.grouped.keys key.value.active
  let matrix := PrefixCompletionMatrices.read (matrices.get key.value.pair) key.value.prefixDigits.get
  let out := BinaryGroupedCompletion.runRow selector.value matrix
  ⟨⟨labels,key.value,selector.value,out.value⟩,out.bitSteps,
    key.work+selector.work+out.control+16*(P+1)^2+24⟩

def rowBitBudget (ell r C A : ℕ) : ℕ :=
  CappedSubsetList.count ell r*(C*BackendScalarBits.backendScalarUnit (CappedSubsetList.count ell r*A).size)
def rowControlBudget (P ell r C : ℕ) : ℕ := PrefixRequestKey.makeBudget P ell+
  (CappedSubsetList.count ell r*(26*ell+24)+4)+
  (CappedSubsetList.count ell r*(40*C+24)+3*C+4)+16*(P+1)^2+24

theorem row_value {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (labels : Vector (Fin 4) (P+ell)) (c : Fin C) :
    view ((row xs (PrefixCompletionMatrices.prepare xs).value labels).value.output.get c)=
      CappedPrefixProgram.query xs (PrefixRequestKey.make xs.grouped.pairs labels).value.pair
        (PrefixRequestKey.make xs.grouped.pairs labels).value.prefixDigits.get
        (support (PrefixRequestKey.make xs.grouped.pairs labels).value.active) c := by
  simp only [row,BinaryGroupedCompletion.runRow_view,selectorRow_get,PrefixCompletionMatrices.prepare_get,
    CappedPrefixProgram.query,decide_eq_true_eq]

theorem row_bits {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (xs.traces.get p) A)
    (labels : Vector (Fin 4) (P+ell)) :
    (row xs (PrefixCompletionMatrices.prepare xs).value labels).bitSteps≤rowBitBudget ell r C A := by
  apply BinaryGroupedCompletion.runRow_bits A _ _ _ (le_refl _)
  intro j c
  rw [PrefixCompletionMatrices.prepare_get]
  exact ha _ _ _ _

theorem row_control {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (matrices : PrefixCompletionMatrices.Prepared P ell r C) (labels : Vector (Fin 4) (P+ell)) :
    (row xs matrices labels).control≤rowControlBudget P ell r C := by
  have hs := selectorRow_work xs.grouped.keys (PrefixRequestKey.make xs.grouped.pairs labels).value.active
  have ho := BinaryGroupedCompletion.runRow_control
    (selectorRow xs.grouped.keys (PrefixRequestKey.make xs.grouped.pairs labels).value.active).value
    (PrefixCompletionMatrices.read (matrices.get (PrefixRequestKey.make xs.grouped.pairs labels).value.pair)
      (PrefixRequestKey.make xs.grouped.pairs labels).value.prefixDigits.get)
  simp only [row,rowControlBudget,PrefixRequestKey.make_work]
  omega

structure Prepared (P ell r C : ℕ) where
  source : CappedPrefixProgram.Prepared P ell r C
  matrices : PrefixCompletionMatrices.Prepared P ell r C
  requests : Array (Completed P ell r C)

def execute {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (requests : Array (Vector (Fin 4) (P+ell))) : Run (Prepared P ell r C) :=
  let matrices := PrefixCompletionMatrices.prepare xs
  let out := BinaryGroupedPreparation.mapArray (row xs matrices.value) requests
  ⟨⟨xs,matrices.value,out.value⟩,matrices.bitSteps+out.bitSteps,matrices.control+out.control+8⟩

@[simp] theorem execute_size {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (requests : Array (Vector (Fin 4) (P+ell))) : (execute xs requests).value.requests.size=requests.size := by
  simp [execute]

theorem execute_get {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (requests : Array (Vector (Fin 4) (P+ell))) (i : ℕ) (hi : i<requests.size) :
    (execute xs requests).value.requests[i]'(by simpa using hi)=
      (row xs (PrefixCompletionMatrices.prepare xs).value requests[i]).value :=
  BinaryGroupedPreparation.mapArray_get _ _ i hi

theorem execute_value {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (requests : Array (Vector (Fin 4) (P+ell))) (i : ℕ) (hi : i<requests.size) (c : Fin C) :
    view (((execute xs requests).value.requests[i]'(by simpa using hi)).output.get c)=
      CappedPrefixProgram.query xs (PrefixRequestKey.make xs.grouped.pairs requests[i]).value.pair
        (PrefixRequestKey.make xs.grouped.pairs requests[i]).value.prefixDigits.get
        (support (PrefixRequestKey.make xs.grouped.pairs requests[i]).value.active) c := by
  rw [execute_get]
  exact row_value _ _ _

theorem execute_labels {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (requests : Array (Vector (Fin 4) (P+ell))) (i : ℕ) (hi : i<requests.size) :
    ((execute xs requests).value.requests[i]'(by simpa using hi)).labels=requests[i] := by
  rw [execute_get]; rfl

def outputCells {P ell r C : ℕ} (xs : Prepared P ell r C) : ℕ :=
  (xs.requests.toList.map (fun row => row.output.toArray.size)).sum

def selectorCells {P ell r C : ℕ} (xs : Prepared P ell r C) : ℕ :=
  (xs.requests.toList.map (fun row => row.selector.toArray.size)).sum

theorem execute_cells {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    outputCells (execute xs requests).value=requests.size*C ∧
    selectorCells (execute xs requests).value=requests.size*CappedSubsetList.count ell r := by
  simp [outputCells,selectorCells]


def bitBudget (P ell r C A M : ℕ) : ℕ := 2^ell*PrefixCompletionMatrices.bitBudget P (CappedSubsetList.count ell r) C A+
  M*rowBitBudget ell r C A
def controlBudget (P ell r C M : ℕ) : ℕ := 2^ell*(PrefixCompletionMatrices.controlBudget P (CappedSubsetList.count ell r) C+32)+8+
  (M*(rowControlBudget P ell r C+32)+8)+8

theorem execute_bits {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (xs.traces.get p) A)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (execute xs requests).bitSteps≤bitBudget P ell r C A requests.size :=
  Nat.add_le_add (PrefixCompletionMatrices.prepare_bits xs A ha)
    (BinaryGroupedPreparation.mapArray_bits _ _ (fun labels _ => row_bits xs A ha labels))

theorem execute_control {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (execute xs requests).control≤controlBudget P ell r C requests.size := by
  exact Nat.add_le_add_right (Nat.add_le_add (PrefixCompletionMatrices.prepare_control xs)
    (BinaryGroupedPreparation.mapArray_control _ _ (fun labels _ => row_control xs _ labels))) 8

theorem execute_tensor {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C)
    (hs : ∀ w c, r<(CroppedGroupedSuffix.rare (fun i => w (Fin.natAdd P i))).card → OppositeWindowLayer.value X w c=0)
    (requests : Array (Vector (Fin 4) (P+ell))) (i : ℕ) (hi : i<requests.size) (c : Fin C) :
    view (((execute (CappedPrefixProgram.execute r X).value requests).value.requests[i]'(by simpa using hi)).output.get c)=
      EncoderCorrectness.tensorSum (fun _ : Fin (P+ell) => 3)
        (fun j => BinaryPrefixContraction.form (requests[i].get j)) (fun w => OppositeWindowLayer.value X w c) := by
  rw [execute_value,CappedPrefixProgram.query_exact r X hs]
  have hp : (CappedPrefixProgram.execute r X).value.grouped.pairs=pairKeys ell := by
    simp only [CappedPrefixProgram.execute,RetainedCappedGroups.prepare,storePairs_value]
  rw [PrefixRequestKey.make_forms _ hp]

#print axioms execute_labels
#print axioms execute_cells
#print axioms row_value
#print axioms row_bits
#print axioms row_control
#print axioms execute_size
#print axioms execute_get
#print axioms execute_value
#print axioms execute_bits
#print axioms execute_control
#print axioms execute_tensor
end ThinMatrix.PrefixCompletionProgram
