import SharedPrefixSourceBank
import SharedAddressedStorage
import FullyRetainedRootBatch

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Retained source-bank and whole-window layout counts. Scalar tree cells
are read from the actual nested vectors; metadata, routers, output rows and
all simultaneous addressed product trees are included in explicit majorants.
These are layout certificates in the bounded indexed-array model. -/
namespace ThinMatrix.SharedPrefixStorage
open scoped BigOperators
open BinaryCell
variable {P ell r C B : ℕ}

def groupedCells (xs : CappedPrefixProgram.Prepared P ell r C) :=
  ∑ pair,∑ key,PrefixCellTree.cells ((xs.grouped.groups.get pair).get key)
def traceCells (xs : CappedPrefixProgram.Prepared P ell r C) :=
  ∑ pair,∑ key,RetainedPrefixEncoder.cells ((xs.traces.get pair).get key)
def matrixCells (xs : PrefixCompletionMatrices.Prepared P ell r C) :=
  ∑ pair,PrefixCompletionMatrices.cells (xs.get pair)

theorem grouped_cells (xs : CappedPrefixProgram.Prepared P ell r C) :
    groupedCells xs=2^ell*CappedSubsetList.count ell r*3^P*C := by
  simp only [groupedCells,PrefixCellTree.cells_eq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]
  ring

theorem trace_cells (xs : CappedPrefixProgram.Prepared P ell r C) :
    traceCells xs≤2^ell*CappedSubsetList.count ell r*(P+1)*4^P*C := by
  calc
    _≤∑ _pair : Fin (2^ell),∑ _key : Fin (CappedSubsetList.count ell r),(P+1)*4^P*C := by
      apply Finset.sum_le_sum;intro pair _
      apply Finset.sum_le_sum;intro key _
      exact RetainedPrefixEncoder.cells_bound _
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul];ring

theorem matrix_cells (xs : PrefixCompletionMatrices.Prepared P ell r C) :
    matrixCells xs=2^ell*4^P*CappedSubsetList.count ell r*C := by
  simp only [matrixCells,PrefixCompletionMatrices.cells_eq,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

/-- Counts every retained scalar tree in the actual prepared bank. Aliased
source arrays are counted repeatedly, giving a valid conservative layout. -/
def bankScalars (stored : SharedPrefixSourceBank.Prepared P ell r C B) :=
  (∑ b,(groupedCells (stored.sources.get b)+traceCells (stored.sources.get b)))+
    ∑ b,matrixCells (stored.banks.get b)

theorem bank_scalars (stored : SharedPrefixSourceBank.Prepared P ell r C B) :
    bankScalars stored≤B*2^ell*CappedSubsetList.count ell r*3^P*C+
      B*2^ell*CappedSubsetList.count ell r*(P+1)*4^P*C+
      B*2^ell*4^P*CappedSubsetList.count ell r*C := by
  have ht := Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => trace_cells (stored.sources.get b))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at ht
  unfold bankScalars
  simp only [Finset.sum_add_distrib,grouped_cells,matrix_cells,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  nlinarith

/-- Original source arrays and key/pair vectors, in addition to retained
prefix traces and completion matrices. -/
def bankCells (stored : SharedPrefixSourceBank.Prepared P ell r C B) :=
  bankScalars stored+B*C*3^(P+ell)+(B+1)*(CappedSubsetList.count ell r+2^ell)*(ell+1)

/-- A closed size-only source-bank majorant, retaining every representation. -/
def bankBudget (P ell D B C : ℕ) :=
  B*2^ell*D*3^P*C+B*2^ell*D*(P+1)*4^P*C+B*2^ell*4^P*D*C+
    B*C*3^(P+ell)+(B+1)*(D+2^ell)*(ell+1)

theorem bank_cells (stored : SharedPrefixSourceBank.Prepared P ell r C B) :
    bankCells stored≤bankBudget P ell (CappedSubsetList.count ell r) B C := by
  have hh := bank_scalars stored
  unfold bankCells bankBudget
  omega

/-- All pair/prefix groups retain their entire batch workspaces. The second
summand covers request labels, router nodes, masks, selected lists, source
matrix copies, scattered outputs and vector record headers. -/
def windowBudget (P ell M D Q A Z R : ℕ) :=
  (2^ell*4^P)*(BinaryAddressedStorage.batchCells M D Q A Z R+
    64*(M+1)*(D+1)*(Q+1)*(P+ell+1))+
  64*(2^ell*4^P+1)*(M+1)*(Q+1)*(P+ell+1)

/-- Retain every window bank and child execution, plus the per-request
window reference table, selection masks and accumulated output rows. -/
def rootBudget (windows P ell M D B C A Z R : ℕ) :=
  windows*(bankBudget P ell D B C+windowBudget P ell M D (B*C) A Z R)+
    64*(windows+1)*(M+1)*(B*C+1)*(P+ell+1)

/-- Exact dimensions of the stored child outputs of the production root
execution, including every coefficient column and every window. -/
theorem root_child_cells {k total cn co A Z W : ℕ}
    (scheme : RectangularBatch.Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hf : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hl : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (banks : Vector (FullyRetainedRootBatch.Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :
    (((FullyRetainedRootBatch.execute scheme hD hA hZ hf hl banks layouts labels).value.children.value.toList.map
      (fun rows => (rows.toList.map (fun row => row.toList.length)).sum)).sum)=W*labels.size*(B*C) := by
  simp only [Vector.length_toList,List.map_const',List.sum_replicate,smul_eq_mul]
  ring

/-- Reference rows and output vectors retained by the actual accumulated
root result have their full window and coefficient dimensions. -/
theorem root_output_cells {k total cn co A Z W : ℕ}
    (scheme : RectangularBatch.Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hf : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hl : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (banks : Vector (FullyRetainedRootBatch.Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :
    (((FullyRetainedRootBatch.execute scheme hD hA hZ hf hl banks layouts labels).value.rows.value.toList.map
      (fun row => row.output.toList.length)).sum)=labels.size*(B*C) := by
  simp only [Vector.length_toList,List.map_const',List.sum_replicate,smul_eq_mul]

#print axioms grouped_cells
#print axioms trace_cells
#print axioms matrix_cells
#print axioms bank_scalars
#print axioms bank_cells
#print axioms root_child_cells
#print axioms root_output_cells
end ThinMatrix.SharedPrefixStorage
