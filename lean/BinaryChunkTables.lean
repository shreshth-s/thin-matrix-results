import BinaryChunkAddress

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Binary-addressed chunk formation and output restoration. The binary
guard, joined addresses and quotient/remainder outputs are used for the
actual lookup. Retained table reads/writes have separate indexed controls. -/
namespace ThinMatrix.BinaryChunkTables
open scoped BigOperators
open BinaryCell BinaryRecursiveDot BinaryChunkAddress
open RecursiveTable (Table read)
open CompactBlocks (blockCount index blockOf slotOf)
variable {N D P A C : ℕ}

theorem original_lt {n h : ℕ} (b : Fin (blockCount n h)) (s : Fin h) :
    (original b s).value<blockCount n h*h := by
  rw [original_value]
  dsimp only [index]
  have hh : 0<h := Nat.zero_lt_of_lt s.isLt
  have hb := Nat.mul_le_mul_right h (Nat.succ_le_iff.mpr b.isLt)
  nlinarith [s.isLt]

def leftEntry (x : Table (PaddedMatrix.matrix N D) Cell)
    (b : Fin (blockCount N A)) (i : Fin A×Fin D) : Run Cell :=
  let address := original b i.1
  let active := less address.value N
  if ha : active.value=true then
    let entry := matrixRead x ⟨address.value,(less_true _ _).mp ha⟩ i.2
    ⟨entry.value,address.bitSteps+active.bitSteps+entry.bitSteps,24⟩
  else ⟨zero,address.bitSteps+active.bitSteps,16⟩

theorem leftEntry_value (x : Table (PaddedMatrix.matrix N D) Cell)
    (b : Fin (blockCount N A)) (i : Fin A×Fin D) :
    (leftEntry x b i).value=read (RectangularBatch.leftChunk x b).value i := by
  simp only [leftEntry,RectangularBatch.leftChunk,tabulate_read]
  split_ifs with ha hb hb
  · rw [matrixRead_value]
    apply congrArg (fun k : Fin N => read x (k,i.2))
    exact Fin.ext (original_value _ _)
  · exact False.elim (hb (by simpa only [original_value] using (less_true _ _).mp ha))
  · exact False.elim (ha ((less_true _ _).mpr (by simpa only [original_value] using hb)))
  · rfl

theorem leftEntry_bits (x : Table (PaddedMatrix.matrix N D) Cell)
    (b : Fin (blockCount N A)) (i : Fin A×Fin D) (W : ℕ)
    (hA : A.size≤W) (hb : (blockCount N A).size≤W) (hpad : (blockCount N A*A).size≤W)
    (hN : N.size≤W) (hD : D.size≤W) :
    (leftEntry x b i).bitSteps≤8260*(W+1)^2 := by
  have ho := original_bits b i.1 W hA hb
  have hl := less_bits (original b i.1).value N W
    ((Nat.size_le_size (original_lt b i.1).le).trans hpad) hN
  dsimp only [leftEntry]
  split_ifs with ha
  · have hr := matrixRead_bits x ⟨(original b i.1).value,(less_true _ _).mp ha⟩ i.2 W hN hD
    dsimp only
    omega
  · dsimp only
    omega

def left (x : Table (PaddedMatrix.matrix N D) Cell) (b : Fin (blockCount N A)) :=
  tabulate (PaddedMatrix.matrix A D) (leftEntry x b)

theorem left_value (x : Table (PaddedMatrix.matrix N D) Cell) (b : Fin (blockCount N A)) :
    (left x b).value=(RectangularBatch.leftChunk x b).value := by
  apply Vector.ext
  intro i hi
  have hh : read (left x b).value ((PaddedMatrix.matrix A D).index.symm ⟨i,hi⟩)=
      read (RectangularBatch.leftChunk x b).value ((PaddedMatrix.matrix A D).index.symm ⟨i,hi⟩) := by
    rw [left,tabulate_read,leftEntry_value]
  simpa only [RecursiveTable.read,Equiv.apply_symm_apply,Vector.get_eq_getElem] using hh

theorem left_bits (x : Table (PaddedMatrix.matrix N D) Cell) (b : Fin (blockCount N A)) (W : ℕ)
    (hA : A.size≤W) (hb : (blockCount N A).size≤W) (hpad : (blockCount N A*A).size≤W)
    (hN : N.size≤W) (hD : D.size≤W) :
    (left x b).bitSteps≤A*D*(8260*(W+1)^2) := by
  rw [left,tabulate_bits]
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => leftEntry_bits x b i W hA hb hpad hN hD)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] using hh

theorem left_control (x : Table (PaddedMatrix.matrix N D) Cell) (b : Fin (blockCount N A)) :
    (left x b).control≤56*A*D+8 := by
  have he (i : Fin A×Fin D) : (leftEntry x b i).control≤24 := by
    dsimp only [leftEntry]
    split_ifs <;> dsimp only <;> omega
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => he i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] at hs
  rw [left,tabulate_control]
  change _+32*(A*D)+8≤_
  nlinarith

def rightEntry (y : Table (PaddedMatrix.matrix D P) Cell)
    (b : Fin (blockCount P C)) (i : Fin D×Fin C) : Run Cell :=
  let address := original b i.2
  let active := less address.value P
  if ha : active.value=true then
    let entry := matrixRead y i.1 ⟨address.value,(less_true _ _).mp ha⟩
    ⟨entry.value,address.bitSteps+active.bitSteps+entry.bitSteps,24⟩
  else ⟨zero,address.bitSteps+active.bitSteps,16⟩

theorem rightEntry_value (y : Table (PaddedMatrix.matrix D P) Cell)
    (b : Fin (blockCount P C)) (i : Fin D×Fin C) :
    (rightEntry y b i).value=read (RectangularBatch.rightChunk y b).value i := by
  simp only [rightEntry,RectangularBatch.rightChunk,tabulate_read]
  split_ifs with ha hb hb
  · rw [matrixRead_value]
    apply congrArg (fun k : Fin P => read y (i.1,k))
    exact Fin.ext (original_value _ _)
  · exact False.elim (hb (by simpa only [original_value] using (less_true _ _).mp ha))
  · exact False.elim (ha ((less_true _ _).mpr (by simpa only [original_value] using hb)))
  · rfl

theorem rightEntry_bits (y : Table (PaddedMatrix.matrix D P) Cell)
    (b : Fin (blockCount P C)) (i : Fin D×Fin C) (W : ℕ)
    (hC : C.size≤W) (hb : (blockCount P C).size≤W) (hpad : (blockCount P C*C).size≤W)
    (hP : P.size≤W) (hD : D.size≤W) :
    (rightEntry y b i).bitSteps≤8260*(W+1)^2 := by
  have ho := original_bits b i.2 W hC hb
  have hl := less_bits (original b i.2).value P W
    ((Nat.size_le_size (original_lt b i.2).le).trans hpad) hP
  dsimp only [rightEntry]
  split_ifs with ha
  · have hr := matrixRead_bits y i.1 ⟨(original b i.2).value,(less_true _ _).mp ha⟩ W hD hP
    dsimp only
    omega
  · dsimp only
    omega

def right (y : Table (PaddedMatrix.matrix D P) Cell) (b : Fin (blockCount P C)) :=
  tabulate (PaddedMatrix.matrix D C) (rightEntry y b)

theorem right_value (y : Table (PaddedMatrix.matrix D P) Cell) (b : Fin (blockCount P C)) :
    (right y b).value=(RectangularBatch.rightChunk y b).value := by
  apply Vector.ext
  intro i hi
  have hh : read (right y b).value ((PaddedMatrix.matrix D C).index.symm ⟨i,hi⟩)=
      read (RectangularBatch.rightChunk y b).value ((PaddedMatrix.matrix D C).index.symm ⟨i,hi⟩) := by
    rw [right,tabulate_read,rightEntry_value]
  simpa only [RecursiveTable.read,Equiv.apply_symm_apply,Vector.get_eq_getElem] using hh

theorem right_bits (y : Table (PaddedMatrix.matrix D P) Cell) (b : Fin (blockCount P C)) (W : ℕ)
    (hC : C.size≤W) (hb : (blockCount P C).size≤W) (hpad : (blockCount P C*C).size≤W)
    (hP : P.size≤W) (hD : D.size≤W) :
    (right y b).bitSteps≤D*C*(8260*(W+1)^2) := by
  rw [right,tabulate_bits]
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => rightEntry_bits y b i W hC hb hpad hP hD)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] using hh

theorem right_control (y : Table (PaddedMatrix.matrix D P) Cell) (b : Fin (blockCount P C)) :
    (right y b).control≤56*D*C+8 := by
  have he (i : Fin D×Fin C) : (rightEntry y b i).control≤24 := by
    dsimp only [rightEntry]
    split_ifs <;> dsimp only <;> omega
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => he i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] at hs
  rw [right,tabulate_control]
  change _+32*(D*C)+8≤_
  nlinarith

def restore (hA : 0<A) (hC : 0<C)
    (products : Table (PaddedMatrix.matrix (blockCount N A) (blockCount P C))
      (Table (PaddedMatrix.matrix A C) Cell)) (i : Fin N×Fin P) : Run Cell :=
  let row := locate hA i.1
  let col := locate hC i.2
  let tile := matrixRead products row.value.1 col.value.1
  let value := matrixRead tile.value row.value.2 col.value.2
  ⟨value.value,row.bitSteps+col.bitSteps+tile.bitSteps+value.bitSteps,24⟩

theorem restore_value (hA : 0<A) (hC : 0<C)
    (products : Table (PaddedMatrix.matrix (blockCount N A) (blockCount P C))
      (Table (PaddedMatrix.matrix A C) Cell)) (i : Fin N×Fin P) :
    (restore hA hC products i).value=
      read (read products (blockOf hA i.1,blockOf hC i.2)) (slotOf hA i.1,slotOf hC i.2) := by
  simp only [restore,matrixRead_value,locate_value]

theorem restore_bits (hA : 0<A) (hC : 0<C)
    (products : Table (PaddedMatrix.matrix (blockCount N A) (blockCount P C))
      (Table (PaddedMatrix.matrix A C) Cell)) (i : Fin N×Fin P) (W : ℕ)
    (hAw : A.size≤W) (hCw : C.size≤W) (hN : N.size≤W) (hP : P.size≤W)
    (hbcN : (blockCount N A).size≤W) (hbcP : (blockCount P C).size≤W) :
    (restore hA hC products i).bitSteps≤8464*(W+1)^2 := by
  have hr := locate_bits hA i.1 W hAw hN
  have hc := locate_bits hC i.2 W hCw hP
  have ht := matrixRead_bits products (locate hA i.1).value.1 (locate hC i.2).value.1 W hbcN hbcP
  have hv := matrixRead_bits (matrixRead products (locate hA i.1).value.1 (locate hC i.2).value.1).value
    (locate hA i.1).value.2 (locate hC i.2).value.2 W hAw hCw
  simp only [restore]
  omega

#print axioms original_lt
#print axioms leftEntry_value
#print axioms leftEntry_bits
#print axioms left_value
#print axioms left_bits
#print axioms left_control
#print axioms rightEntry_value
#print axioms rightEntry_bits
#print axioms right_value
#print axioms right_bits
#print axioms right_control
#print axioms restore_value
#print axioms restore_bits
end ThinMatrix.BinaryChunkTables
