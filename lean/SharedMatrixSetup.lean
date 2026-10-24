import RectangularBatch

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! One charged size selection shared by every compatible rectangular
product. The selected depth is stored in the executable shape, and all
products consume that stored depth. This avoids redoing binary padding
selection for each chunk or request group. -/
namespace ThinMatrix.SharedMatrixSetup
open scoped BigOperators
open RecursiveTable (Table fin prod read)
open BinaryCell BinaryRecursiveDot
open RectangularBatch (Scheme)
open CompactBlocks (blockCount blockOf slotOf)

structure Shape (s : Scheme) (D A C : ℕ) where
  depth : ℕ
  first_fit : A≤ s.a^depth
  middle_fit : D≤ s.q^depth
  last_fit : C≤ s.c^depth

def prepare (s : Scheme) {D A C : ℕ} (hD : 0<D)
    (hfirst : (A-1)^s.den≤D^s.num) (hlast : C≤D^s.z) : Result (Shape s D A C) :=
  let shape := BinaryMatrixSetup.select s.q D
  let hf := BinaryMatrixSetup.selected_fits s.a s.q s.c D A C s.num s.den s.z
    s.hq hD s.hnum s.hden s.aspect s.inner hfirst hlast
  ⟨⟨shape.value.2,hf.1,hf.2.1,hf.2.2⟩,shape.operations+4⟩

theorem prepare_depth (s : Scheme) {D A C : ℕ} (hD : 0<D)
    (hfirst : (A-1)^s.den≤D^s.num) (hlast : C≤D^s.z) :
    (prepare s hD hfirst hlast).value.depth=(BinaryMatrixSetup.select s.q D).value.2 := rfl

theorem prepare_bits (s : Scheme) {D A C : ℕ} (hD : 0<D)
    (hfirst : (A-1)^s.den≤D^s.num) (hlast : C≤D^s.z) :
    (prepare s hD hfirst hlast).bitSteps≤1400*(D.size+3)*(s.q.size+D.size+6)^2+4 :=
  Nat.add_le_add_right (BinaryMatrixSetup.select_bits s.q D s.hq hD) 4

variable {N D P A C : ℕ}

def product (s : Scheme) (shape : Shape s D A C)
    (x : Table (PaddedMatrix.matrix A D) Cell) (y : Table (PaddedMatrix.matrix D C) Cell) :=
  PaddedMatrix.execute (fin s.a) (fin s.q) (fin s.c) s.ht s.base shape.depth
    shape.first_fit shape.last_fit x y

theorem product_correct (s : Scheme) (hs : s.Valid) (shape : Shape s D A C)
    (x : Table (PaddedMatrix.matrix A D) Cell) (y : Table (PaddedMatrix.matrix D C) Cell)
    (i : Fin A×Fin C) :
    view (read (product s shape x y).value i)=
      ∑ j : Fin D,view (read x (i.1,j))*view (read y (j,i.2)) :=
  PaddedMatrix.execute_correct (fin s.a) (fin s.q) (fin s.c) s.ht s.base hs shape.depth
    shape.first_fit shape.middle_fit shape.last_fit x y i

def run (s : Scheme) (shape : Shape s D A C) (hA : 0<A) (hC : 0<C)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    Run (Table (PaddedMatrix.matrix N P) Cell) :=
  let left := tabulate (fin (blockCount N A)) (RectangularBatch.leftChunk x)
  let right := tabulate (fin (blockCount P C)) (RectangularBatch.rightChunk y)
  let products := tabulate (prod (fin (blockCount N A)) (fin (blockCount P C))) (fun b =>
    product s shape (read left.value b.1) (read right.value b.2))
  let out := tabulate (PaddedMatrix.matrix N P) (fun i =>
    ⟨read (read products.value (blockOf hA i.1,blockOf hC i.2))
      (slotOf hA i.1,slotOf hC i.2),0,16⟩)
  ⟨out.value,left.bitSteps+right.bitSteps+products.bitSteps+out.bitSteps,
    left.control+right.control+products.control+out.control+16⟩

theorem run_correct (s : Scheme) (hs : s.Valid) (shape : Shape s D A C) (hA : 0<A) (hC : 0<C)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (i : Fin N×Fin P) :
    view (read (run s shape hA hC x y).value i)=
      ∑ j : Fin D,view (read x (i.1,j))*view (read y (j,i.2)) := by
  simp only [run,tabulate_read]
  rw [product_correct s hs]
  simp only [RectangularBatch.leftChunk_read _ hA,RectangularBatch.rightChunk_read _ hC]

theorem run_value_eq (s : Scheme) (hD : 0<D) (hA : 0<A) (hC : 0<C)
    (hfirst : (A-1)^s.den≤D^s.num) (hlast : C≤D^s.z)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    (run s (prepare s hD hfirst hlast).value hA hC x y).value=
      (RectangularBatch.run s hD hA hC hfirst hlast x y).value := by
  apply Vector.ext
  intro i hi
  let ij := (PaddedMatrix.matrix N P).index.symm ⟨i,hi⟩
  have hh : RecursiveTable.read (run s (prepare s hD hfirst hlast).value hA hC x y).value ij =
      RecursiveTable.read (RectangularBatch.run s hD hA hC hfirst hlast x y).value ij := by
    simp only [run,RectangularBatch.run,tabulate_read,product,prepare,BinaryMatrixSetup.execute]
  simpa only [RecursiveTable.read,ij,Equiv.apply_symm_apply,Vector.get_eq_getElem] using hh

theorem run_bits (s : Scheme) (shape : Shape s D A C) (hA : 0<A) (hC : 0<C)
    (H : ℕ) (hH : 1≤H)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (run s shape hA hC x y).bitSteps≤
      blockCount N A*blockCount P C*BinaryRecursiveCost.bits s.base shape.depth H := by
  have hl (i : Fin (blockCount N A)) : (RectangularBatch.leftChunk x i).bitSteps=0 := by
    rw [RectangularBatch.leftChunk,tabulate_bits]
    apply Finset.sum_eq_zero; intro a _; split_ifs <;> rfl
  have hr (j : Fin (blockCount P C)) : (RectangularBatch.rightChunk y j).bitSteps=0 := by
    rw [RectangularBatch.rightChunk,tabulate_bits]
    apply Finset.sum_eq_zero; intro a _; split_ifs <;> rfl
  have hc (ij : Fin (blockCount N A)×Fin (blockCount P C)) :=
    PaddedMatrix.execute_bits (fin s.a) (fin s.q) (fin s.c) s.ht s.base shape.depth H
      shape.first_fit shape.last_fit hH _ _
      (RectangularBatch.leftChunk_bound x H hx ij.1) (RectangularBatch.rightChunk_bound y H hy ij.2)
  simp only [run,tabulate_bits,tabulate_read,hl,hr,Finset.sum_const_zero,zero_add,add_zero]
  have hh := Finset.sum_le_sum (fun ij (_ : ij∈Finset.univ) => hc ij)
  simpa only [product,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] using hh

theorem run_control (s : Scheme) (shape : Shape s D A C) (hA : 0<A) (hC : 0<C)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    (run s shape hA hC x y).control=
      (∑ i : Fin (blockCount N A),∑ j : Fin (blockCount P C),
        (product s shape (RectangularBatch.leftChunk x i).value (RectangularBatch.rightChunk y j).value).control)+
      blockCount N A*(40*A*D+40)+blockCount P C*(40*D*C+40)+
      32*blockCount N A*blockCount P C+48*N*P+48 := by
  simp only [run,tabulate_control,RectangularBatch.leftChunk_control,RectangularBatch.rightChunk_control,
    tabulate_read,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul,
    Fintype.sum_prod_type,PaddedMatrix.matrix,prod,fin]
  ring

#print axioms prepare_depth
#print axioms prepare_bits
#print axioms product_correct
#print axioms run_correct
#print axioms run_value_eq
#print axioms run_bits
#print axioms run_control
end ThinMatrix.SharedMatrixSetup
