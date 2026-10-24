import SharedAddressedBatch
import BinaryAddressedMatrix

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Shared-depth rectangular batching with actual binary chunk addresses.
The selected setup is retained across all products, chunks are copied once,
and every output is restored through binary quotient/remainder and joined
addresses. Recursive products use the addressed ordinary-matrix backend. Indexed controls
remain the explicit bounded-array model, separate from literal compiler costs. -/
namespace ThinMatrix.SharedFullyAddressedBatch
open scoped BigOperators
open RecursiveTable (Table fin prod read)
open BinaryCell BinaryRecursiveDot
open RectangularBatch (Scheme)
open CompactBlocks (blockCount blockOf slotOf)
variable {N D P A C : ℕ}

abbrev AddressFits := SharedAddressedBatch.AddressFits
abbrev addressSpan := SharedAddressedBatch.addressSpan
abbrev address_fits := SharedAddressedBatch.address_fits

def growth (s : Scheme) := max ((s.r+s.t-1)/s.t) (max 1 (max (s.a*s.q) (max (s.q*s.c) (s.c*s.a))))

theorem growth_properties (s : Scheme) :
    1≤growth s ∧ (s.r+s.t-1)/s.t≤growth s ∧ s.a*s.q≤growth s ∧ s.q*s.c≤growth s ∧ s.c*s.a≤growth s := by
  unfold growth
  exact ⟨(le_max_left _ _).trans (le_max_right _ _),le_max_left _ _,
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩

theorem middle_pos (s : Scheme) : 0<s.q := by have hh:=s.hq;omega

theorem first_pos (s : Scheme) : 0<s.a := by
  by_contra h
  have hz : s.a=0 := by omega
  have hh := s.aspect
  rw [hz,zero_pow (Nat.ne_zero_of_lt s.hden)] at hh
  have hp := pow_pos (middle_pos s) s.num
  omega

theorem last_pos (s : Scheme) : 0<s.c := by
  rw [s.inner]
  exact pow_pos (middle_pos s) s.z

def product (s : Scheme) (shape : SharedMatrixSetup.Shape s D A C)
    (x : Table (PaddedMatrix.matrix A D) Cell) (y : Table (PaddedMatrix.matrix D C) Cell) :=
  BinaryAddressedMatrix.execute (first_pos s) (middle_pos s) (last_pos s) s.ht s.base shape.depth shape.first_fit shape.last_fit x y

def productCost (s : Scheme) (k H : ℕ) :=
  BinaryAddressedMatrix.constant s.base*(k+H.size+2)^5*(growth s)^k

theorem product_value (s : Scheme) (shape : SharedMatrixSetup.Shape s D A C)
    (x : Table (PaddedMatrix.matrix A D) Cell) (y : Table (PaddedMatrix.matrix D C) Cell) :
    (product s shape x y).value=(SharedMatrixSetup.product s shape x y).value := by
  simp only [product,BinaryAddressedMatrix.execute_value,SharedMatrixSetup.product]

theorem product_bits (s : Scheme) (shape : SharedMatrixSetup.Shape s D A C)
    (H : ℕ) (hH : 1≤H) (x : Table (PaddedMatrix.matrix A D) Cell) (y : Table (PaddedMatrix.matrix D C) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (product s shape x y).bitSteps≤productCost s shape.depth H := by
  have hg := growth_properties s
  exact BinaryAddressedMatrix.execute_bits (first_pos s) (middle_pos s) (last_pos s) s.ht s.base
    (growth s) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 shape.depth H hH
    shape.first_fit shape.middle_fit shape.last_fit x y hx hy

def run (s : Scheme) (shape : SharedMatrixSetup.Shape s D A C) (hA : 0<A) (hC : 0<C)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    Run (Table (PaddedMatrix.matrix N P) Cell) :=
  let left := tabulate (fin (blockCount N A)) (BinaryChunkTables.left x)
  let right := tabulate (fin (blockCount P C)) (BinaryChunkTables.right y)
  let products := tabulate (prod (fin (blockCount N A)) (fin (blockCount P C))) (fun b =>
    product s shape (read left.value b.1) (read right.value b.2))
  let out := tabulate (PaddedMatrix.matrix N P) (BinaryChunkTables.restore hA hC products.value)
  ⟨out.value,left.bitSteps+right.bitSteps+products.bitSteps+out.bitSteps,
    left.control+right.control+products.control+out.control+16⟩

theorem run_value_eq (s : Scheme) (shape : SharedMatrixSetup.Shape s D A C) (hA : 0<A) (hC : 0<C)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    (run s shape hA hC x y).value=(SharedMatrixSetup.run s shape hA hC x y).value := by
  apply Vector.ext
  intro i hi
  have hh : read (run s shape hA hC x y).value ((PaddedMatrix.matrix N P).index.symm ⟨i,hi⟩)=
      read (SharedMatrixSetup.run s shape hA hC x y).value ((PaddedMatrix.matrix N P).index.symm ⟨i,hi⟩) := by
    simp only [run,SharedMatrixSetup.run,tabulate_read,BinaryChunkTables.restore_value,
      BinaryChunkTables.left_value,BinaryChunkTables.right_value]
    simp only [PaddedMatrix.matrix,tabulate_read,product_value]
  simpa only [RecursiveTable.read,Equiv.apply_symm_apply,Vector.get_eq_getElem] using hh

theorem run_correct (s : Scheme) (hs : s.Valid) (shape : SharedMatrixSetup.Shape s D A C)
    (hA : 0<A) (hC : 0<C)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (i : Fin N×Fin P) :
    view (read (run s shape hA hC x y).value i)=
      ∑ j : Fin D,view (read x (i.1,j))*view (read y (j,i.2)) := by
  rw [run_value_eq]
  exact SharedMatrixSetup.run_correct s hs shape hA hC x y i

def addressBudget (N D P A C W : ℕ) :=
  (blockCount N A*A*D+blockCount P C*D*C)*(8260*(W+1)^2)+N*P*(8464*(W+1)^2)

theorem run_bits (s : Scheme) (shape : SharedMatrixSetup.Shape s D A C) (hA : 0<A) (hC : 0<C)
    (H W : ℕ) (hH : 1≤H) (hW : AddressFits N D P A C W)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (run s shape hA hC x y).bitSteps≤
      blockCount N A*blockCount P C*productCost s shape.depth H+
        addressBudget N D P A C W := by
  let left := tabulate (fin (blockCount N A)) (BinaryChunkTables.left x)
  let right := tabulate (fin (blockCount P C)) (BinaryChunkTables.right y)
  let products := tabulate (prod (fin (blockCount N A)) (fin (blockCount P C))) (fun b =>
    product s shape (read left.value b.1) (read right.value b.2))
  have hl : left.bitSteps≤blockCount N A*(A*D*(8260*(W+1)^2)) := by
    dsimp only [left]
    rw [tabulate_bits]
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
      BinaryChunkTables.left_bits x i W hW.chunkRows hW.rowChunks hW.paddedRows hW.rows hW.middle)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hh
  have hr : right.bitSteps≤blockCount P C*(D*C*(8260*(W+1)^2)) := by
    dsimp only [right]
    rw [tabulate_bits]
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
      BinaryChunkTables.right_bits y i W hW.chunkColumns hW.columnChunks hW.paddedColumns hW.columns hW.middle)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hh
  have hp : products.bitSteps≤blockCount N A*blockCount P C*productCost s shape.depth H := by
    dsimp only [products]
    rw [tabulate_bits]
    have hc (ij : Fin (blockCount N A)×Fin (blockCount P C)) :=
      product_bits s shape H hH _ _
        (RectangularBatch.leftChunk_bound x H hx ij.1) (RectangularBatch.rightChunk_bound y H hy ij.2)
    have hh := Finset.sum_le_sum (fun ij (_ : ij∈Finset.univ) => hc ij)
    simpa only [left,right,tabulate_read,BinaryChunkTables.left_value,BinaryChunkTables.right_value,
      Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] using hh
  have ho : (tabulate (PaddedMatrix.matrix N P) (BinaryChunkTables.restore hA hC products.value)).bitSteps≤
      N*P*(8464*(W+1)^2) := by
    rw [tabulate_bits]
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
      BinaryChunkTables.restore_bits hA hC products.value i W hW.chunkRows hW.chunkColumns
        hW.rows hW.columns hW.rowChunks hW.columnChunks)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] using hh
  change left.bitSteps+right.bitSteps+products.bitSteps+_≤_
  dsimp only [addressBudget]
  nlinarith

theorem run_control (s : Scheme) (shape : SharedMatrixSetup.Shape s D A C) (hA : 0<A) (hC : 0<C)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    (run s shape hA hC x y).control≤
      (∑ i : Fin (blockCount N A),∑ j : Fin (blockCount P C),
        (product s shape (RectangularBatch.leftChunk x i).value
          (RectangularBatch.rightChunk y j).value).control)+
      blockCount N A*(56*A*D+40)+blockCount P C*(56*D*C+40)+
      32*blockCount N A*blockCount P C+56*N*P+48 := by
  have hl := Finset.sum_le_sum (fun (i : Fin (blockCount N A)) (_ : i∈Finset.univ) => BinaryChunkTables.left_control x i)
  have hr := Finset.sum_le_sum (fun (i : Fin (blockCount P C)) (_ : i∈Finset.univ) => BinaryChunkTables.right_control y i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hl hr
  simp only [run,tabulate_control,tabulate_read,BinaryChunkTables.left_value,BinaryChunkTables.right_value,
    BinaryChunkTables.restore,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul,
    Fintype.sum_prod_type,PaddedMatrix.matrix,prod,fin]
  nlinarith

/-- Retained cells in the explicit outer banks and complete product grid.
This excludes the separate recursive working storage inside one product. -/
def outerCells (N D P A C : ℕ) :=
  blockCount N A*A*D+blockCount P C*D*C+blockCount N A*blockCount P C*A*C+N*P

theorem retained_chunk_cells (x : Table (PaddedMatrix.matrix N D) Cell)
    (y : Table (PaddedMatrix.matrix D P) Cell) :
    ((tabulate (fin (blockCount N A)) (BinaryChunkTables.left x)).value.toList.map
      (fun row => row.toList.length)).sum+
    ((tabulate (fin (blockCount P C)) (BinaryChunkTables.right y)).value.toList.map
      (fun row => row.toList.length)).sum=
      blockCount N A*A*D+blockCount P C*D*C := by
  simp only [Vector.length_toList,List.map_const',List.sum_replicate,smul_eq_mul,
    PaddedMatrix.matrix,prod,fin]
  ring

theorem retained_product_cells
    (products : Table (PaddedMatrix.matrix (blockCount N A) (blockCount P C))
      (Table (PaddedMatrix.matrix A C) Cell)) :
    (products.toList.map (fun row => row.toList.length)).sum=blockCount N A*blockCount P C*A*C := by
  simp only [Vector.length_toList,List.map_const',List.sum_replicate,smul_eq_mul,
    PaddedMatrix.matrix,prod,fin]
  ring

theorem address_budget_by_outer_cells (N D P A C W : ℕ) :
    addressBudget N D P A C W≤outerCells N D P A C*(8464*(W+1)^2) := by
  unfold addressBudget outerCells
  have hh := Nat.mul_le_mul_left (blockCount N A*A*D+blockCount P C*D*C)
    (show 8260*(W+1)^2≤8464*(W+1)^2 by omega)
  apply (Nat.add_le_add_right hh (N*P*(8464*(W+1)^2))).trans
  rw [←Nat.add_mul]
  apply Nat.mul_le_mul_right
  omega

#print axioms growth_properties
#print axioms product_value
#print axioms product_bits
#print axioms run_value_eq
#print axioms run_correct
#print axioms run_bits
#print axioms run_control
#print axioms retained_chunk_cells
#print axioms retained_product_cells
#print axioms address_budget_by_outer_cells
end ThinMatrix.SharedFullyAddressedBatch
