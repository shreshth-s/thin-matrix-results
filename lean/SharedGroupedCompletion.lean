import RectangularBatch
import BinaryPreparedGroupedProgram

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Retained selectors/data feed the actual recursive rectangular program.
All cyclic/formal columns and every request-list occurrence are preserved.
The production graph scheduler still needs to route compatible requests to
this adapter and prove its rounded batch sizes and global cost. -/
namespace ThinMatrix.SharedGroupedCompletion
open scoped BigOperators
open BinaryCell BinaryRecursiveDot
open RecursiveTable (Table read)
open RectangularBatch (Scheme)

variable {D C A P : ℕ}

def selectors (M : Array (Vector Bool D)) : Run (Table (PaddedMatrix.matrix M.size D) Cell) :=
  tabulate (PaddedMatrix.matrix M.size D) (fun i =>
    ⟨if (M[i.1.val]).get i.2 then BinaryModularCell.one else zero,0,8⟩)

def data (X : Vector (Vector Cell C) D) : Run (Table (PaddedMatrix.matrix D C) Cell) :=
  tabulate (PaddedMatrix.matrix D C) (fun i => ⟨(X.get i.1).get i.2,0,8⟩)

def rows {N : ℕ} (x : Table (PaddedMatrix.matrix N C) Cell) : Run (Array (Vector Cell C)) :=
  ⟨Array.ofFn (fun i : Fin N => Vector.ofFn (fun j => read x (i,j))),0,40*N*C+32*N+8⟩

def complete (s : Scheme) (hD : 0 < D) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : P ≤ D^s.z)
    (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) : Run (Array (Vector Cell C)) :=
  let left := selectors M
  let right := data X
  let product := RectangularBatch.run s hD hA hP hfirst hlast left.value right.value
  let out := rows product.value
  ⟨out.value,left.bitSteps+right.bitSteps+product.bitSteps+out.bitSteps,
    left.control+right.control+product.control+out.control+16⟩

@[simp] theorem complete_size (s : Scheme) (hD : 0 < D) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : P ≤ D^s.z)
    (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) :
    (complete s hD hA hP hfirst hlast M X).value.size=M.size := by simp [complete,rows]

theorem complete_correct (s : Scheme) (hv : s.Valid) (hD : 0 < D) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : P ≤ D^s.z)
    (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) (i : Fin M.size) (j : Fin C) :
    view (((complete s hD hA hP hfirst hlast M X).value[i.val]'(by simp)).get j)=
      ∑ k : Fin D, if (M[i.val]).get k then view ((X.get k).get j) else 0 := by
  simp only [complete,rows,Array.getElem_ofFn,Vector.get_ofFn]
  rw [RectangularBatch.run_correct s hv]
  simp only [selectors,data,tabulate_read]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem complete_bits (s : Scheme) (hD : 0 < D) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : P ≤ D^s.z)
    (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D)
    (H : ℕ) (hH : 1 ≤ H) (hX : ∀ i j, (view ((X.get i).get j)).natAbs ≤ H) :
    (complete s hD hA hP hfirst hlast M X).bitSteps ≤
      CompactBlocks.blockCount M.size A*CompactBlocks.blockCount C P*RectangularBatch.scalarBudget s D H := by
  have hl : BinaryRetainedBounds.Bounded (selectors M).value H := by
    intro i
    simp only [selectors,tabulate_read]
    split_ifs
    · simpa using hH
    · simp
  have hr : BinaryRetainedBounds.Bounded (data X).value H := by
    intro i
    simpa only [data,tabulate_read] using hX i.1 i.2
  have hh := RectangularBatch.run_bits s hD hA hP hfirst hlast H hH _ _ hl hr
  simpa only [complete,selectors,data,rows,tabulate_bits,Finset.sum_const_zero,zero_add,add_zero] using hh

theorem complete_control (s : Scheme) (hD : 0 < D) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : P ≤ D^s.z)
    (M : Array (Vector Bool D)) (X : Vector (Vector Cell C) D) :
    (complete s hD hA hP hfirst hlast M X).control=
      (RectangularBatch.run s hD hA hP hfirst hlast (selectors M).value (data X).value).control+
      40*(M.size*D+D*C+M.size*C)+32*M.size+40 := by
  simp only [complete,selectors,data,rows,tabulate_control,Finset.sum_const,Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,smul_eq_mul,PaddedMatrix.matrix,RecursiveTable.prod,RecursiveTable.fin]
  ring

open GroupedPreparation (Prepared)
open CappedBitPreparation (Key)

variable {n r : ℕ}

def runGroup (s : Scheme) (hD : 0 < CappedSubsetList.count n r) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ (CappedSubsetList.count n r)^s.num)
    (hlast : P ≤ (CappedSubsetList.count n r)^s.z)
    (stored : Prepared n r C Cell) (p : Fin (2^n)) (requests : Array (Key n)) :
    Run (Array (Vector Cell C)) :=
  let masks := GroupedPreparation.selectors stored.keys requests
  let out := complete s hD hA hP hfirst hlast masks.value (stored.groups.get p)
  ⟨out.value,out.bitSteps,masks.work+out.control+8⟩

@[simp] theorem runGroup_size (s : Scheme) (hD : 0 < CappedSubsetList.count n r) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ (CappedSubsetList.count n r)^s.num)
    (hlast : P ≤ (CappedSubsetList.count n r)^s.z)
    (stored : Prepared n r C Cell) (p : Fin (2^n)) (requests : Array (Key n)) :
    (runGroup s hD hA hP hfirst hlast stored p requests).value.size=requests.size := by
  simp [runGroup,GroupedPreparation.selectors_size]

/-- Pointwise agreement with the old elementary completion, with original
request indices and complete data columns. No request deduplication occurs. -/
theorem runGroup_agrees (s : Scheme) (hv : s.Valid)
    (hD : 0 < CappedSubsetList.count n r) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ (CappedSubsetList.count n r)^s.num)
    (hlast : P ≤ (CappedSubsetList.count n r)^s.z)
    (stored : Prepared n r C Cell) (p : Fin (2^n)) (requests : Array (Key n))
    (i : Fin requests.size) (j : Fin C) :
    view (((runGroup s hD hA hP hfirst hlast stored p requests).value[i.val]'(by simp)).get j)=
      view (((BinaryPreparedGroupedProgram.runGroup stored p requests).value[i.val]'(by simp)).get j) := by
  have hh := complete_correct s hv hD hA hP hfirst hlast
    (GroupedPreparation.selectors stored.keys requests).value (stored.groups.get p)
    ⟨i.val,by simpa only [GroupedPreparation.selectors_size] using i.isLt⟩ j
  have he := BinaryGroupedCompletion.runMatrix_get (GroupedPreparation.selectors stored.keys requests).value
    (stored.groups.get p) i.val (by simpa only [GroupedPreparation.selectors_size] using i.isLt) j
  exact hh.trans he.symm

theorem runGroup_bits (s : Scheme)
    (hD : 0 < CappedSubsetList.count n r) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ (CappedSubsetList.count n r)^s.num)
    (hlast : P ≤ (CappedSubsetList.count n r)^s.z)
    (H : ℕ) (hH : 1 ≤ H) (X : StoredGroupedCompletion.Source n C ℤ)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ H)
    (p : Fin (2^n)) (requests : Array (Key n)) :
    (runGroup s hD hA hP hfirst hlast (BinaryGroupedPreparation.prepare r X).value p requests).bitSteps ≤
      CompactBlocks.blockCount requests.size A*CompactBlocks.blockCount C P*
        RectangularBatch.scalarBudget s (CappedSubsetList.count n r) H := by
  have hh := complete_bits s hD hA hP hfirst hlast
    (GroupedPreparation.selectors (BinaryGroupedPreparation.prepare r X).value.keys requests).value
    ((BinaryGroupedPreparation.prepare r X).value.groups.get p) H hH
    (BinaryGroupedPreparation.prepare_abs H r X hX p)
  simpa only [runGroup,GroupedPreparation.selectors_size] using hh

/-- Output storage is the entire request-by-column array, including repeated
requests and every formal-degree/cyclic-residue slot supplied by the caller. -/
theorem output_cells (s : Scheme)
    (hD : 0 < CappedSubsetList.count n r) (hA : 0 < A) (hP : 0 < P)
    (hfirst : (A-1)^s.den ≤ (CappedSubsetList.count n r)^s.num)
    (hlast : P ≤ (CappedSubsetList.count n r)^s.z)
    (stored : Prepared n r C Cell) (p : Fin (2^n)) (requests : Array (Key n)) :
    ((runGroup s hD hA hP hfirst hlast stored p requests).value.toList.map (fun row => row.toList.length)).sum =
      requests.size*C := by
  simp only [Vector.length_toList,List.map_const',List.sum_replicate,smul_eq_mul,Array.length_toList,runGroup_size]

#print axioms complete_size
#print axioms complete_correct
#print axioms complete_bits
#print axioms complete_control
#print axioms runGroup_size
#print axioms runGroup_agrees
#print axioms runGroup_bits
#print axioms output_cells
end ThinMatrix.SharedGroupedCompletion
