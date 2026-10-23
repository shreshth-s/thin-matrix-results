import CWBinaryScalarBound
import CompactBlocks

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Compatible row/column chunks for shared rectangular completion. Input
chunks are retained once outside the Cartesian product of chunk indices.
Every short final chunk is padded and every original output is restored in
order. This is a matrix-level adapter, not yet graph request routing or its
independent geometric batch-fit theorem. -/
namespace ThinMatrix.RectangularBatch
open scoped BigOperators
open RecursiveTable (Table fin prod read)
open BinaryCell BinaryRecursiveDot
open CompactBlocks (blockCount index blockOf slotOf index_recovery)

structure Scheme where
  a : ℕ
  q : ℕ
  c : ℕ
  num : ℕ
  den : ℕ
  z : ℕ
  r : ℕ
  t : ℕ
  hq : 2 ≤ q
  hnum : 0 < num
  hden : 0 < den
  ht : 0 < t
  aspect : a^den=q^num
  inner : c=q^z
  base : RetainedEqualCopy.Base r t (prod (fin a) (fin q))
    (prod (fin q) (fin c)) (prod (fin c) (fin a)) ℚ

def Scheme.Valid (s : Scheme) : Prop :=
  FiniteTrilinear.total s.base.terms=FiniteDirectSum.diagonal (Fin s.t)
    (FiniteMatrixTensor.coeff (Fin s.a) (Fin s.q) (Fin s.c) ℚ)

noncomputable def ofCW (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0 < CWHomogeneousCopies.copies s h) : Scheme :=
  ⟨CWHomogeneousCopies.cols s,CWHomogeneousCopies.rows s,CWHomogeneousCopies.inners s,
    861,500,15,CWHomogeneousCopies.ranks s,CWHomogeneousCopies.copies s h,
    (PaddedMatrixScale.bases_gt_one s hs).2.1,by decide,by decide,ht,
    (PaddedMatrixScale.aspect s).1,(PaddedMatrixScale.aspect s).2,CWRetainedArithmetic.base s h⟩

theorem ofCW_valid (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0 < CWHomogeneousCopies.copies s h) : (ofCW s hs h ht).Valid :=
  CWRetainedArithmetic.base_total s h

def leftChunk {N D A : ℕ} (x : Table (PaddedMatrix.matrix N D) Cell)
    (b : Fin (blockCount N A)) : Run (Table (PaddedMatrix.matrix A D) Cell) :=
  tabulate (PaddedMatrix.matrix A D) (fun i =>
    if hi : index b i.1 < N then ⟨read x (⟨_,hi⟩,i.2),0,8⟩ else ⟨zero,0,8⟩)

def rightChunk {D P C : ℕ} (y : Table (PaddedMatrix.matrix D P) Cell)
    (b : Fin (blockCount P C)) : Run (Table (PaddedMatrix.matrix D C) Cell) :=
  tabulate (PaddedMatrix.matrix D C) (fun i =>
    if hi : index b i.2 < P then ⟨read y (i.1,⟨_,hi⟩),0,8⟩ else ⟨zero,0,8⟩)

theorem leftChunk_read {N D A : ℕ} (x : Table (PaddedMatrix.matrix N D) Cell)
    (hA : 0 < A) (i : Fin N) (j : Fin D) :
    read (leftChunk x (blockOf hA i)).value (slotOf hA i,j)=read x (i,j) := by
  simp only [leftChunk,tabulate_read,index_recovery,i.isLt,↓reduceDIte]

theorem rightChunk_read {D P C : ℕ} (y : Table (PaddedMatrix.matrix D P) Cell)
    (hC : 0 < C) (i : Fin D) (j : Fin P) :
    read (rightChunk y (blockOf hC j)).value (i,slotOf hC j)=read y (i,j) := by
  simp only [rightChunk,tabulate_read,index_recovery,j.isLt,↓reduceDIte]

variable {N D P A C : ℕ}

def run (s : Scheme) (hD : 0 < D) (hA : 0 < A) (hC : 0 < C)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : C ≤ D^s.z)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    Run (Table (PaddedMatrix.matrix N P) Cell) :=
  let left := tabulate (fin (blockCount N A)) (leftChunk x)
  let right := tabulate (fin (blockCount P C)) (rightChunk y)
  let products := tabulate (prod (fin (blockCount N A)) (fin (blockCount P C))) (fun b =>
    BinaryMatrixSetup.execute s.a s.q s.c s.num s.den s.z s.hq hD s.hnum s.hden s.aspect s.inner
      s.ht s.base hfirst hlast (read left.value b.1) (read right.value b.2))
  let out := tabulate (PaddedMatrix.matrix N P) (fun i =>
    ⟨read (read products.value (blockOf hA i.1,blockOf hC i.2)) (slotOf hA i.1,slotOf hC i.2),0,16⟩)
  ⟨out.value,left.bitSteps+right.bitSteps+products.bitSteps+out.bitSteps,
    left.control+right.control+products.control+out.control+16⟩

theorem run_correct (s : Scheme) (hv : s.Valid) (hD : 0 < D) (hA : 0 < A) (hC : 0 < C)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : C ≤ D^s.z)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (i : Fin N × Fin P) :
    view (read (run s hD hA hC hfirst hlast x y).value i)=
      ∑ j : Fin D,view (read x (i.1,j))*view (read y (j,i.2)) := by
  simp only [run,tabulate_read]
  rw [BinaryMatrixSetup.execute_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv]
  simp only [leftChunk_read _ hA,rightChunk_read _ hC]

theorem chunk_bits (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (i : Fin (blockCount N A)) (j : Fin (blockCount P C)) :
    (leftChunk x i).bitSteps=0 ∧ (rightChunk y j).bitSteps=0 := by
  constructor
  · rw [leftChunk,tabulate_bits]
    apply Finset.sum_eq_zero; intro a _; split_ifs <;> rfl
  · rw [rightChunk,tabulate_bits]
    apply Finset.sum_eq_zero; intro a _; split_ifs <;> rfl

theorem leftChunk_bound (x : Table (PaddedMatrix.matrix N D) Cell)
    (H : ℕ) (hx : BinaryRetainedBounds.Bounded x H) (i : Fin (blockCount N A)) :
    BinaryRetainedBounds.Bounded (leftChunk x i).value H := by
  intro a
  simp only [leftChunk,tabulate_read]
  split_ifs
  · exact hx _
  · simp

theorem rightChunk_bound (y : Table (PaddedMatrix.matrix D P) Cell)
    (H : ℕ) (hy : BinaryRetainedBounds.Bounded y H) (j : Fin (blockCount P C)) :
    BinaryRetainedBounds.Bounded (rightChunk y j).value H := by
  intro a
  simp only [rightChunk,tabulate_read]
  split_ifs
  · exact hy _
  · simp

theorem leftChunk_control (x : Table (PaddedMatrix.matrix N D) Cell) (i : Fin (blockCount N A)) :
    (leftChunk x i).control=40*A*D+8 := by
  rw [leftChunk,tabulate_control]
  simp only [apply_dite,dite_eq_ite,ite_self,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,smul_eq_mul,PaddedMatrix.matrix,prod,fin]
  ring

theorem rightChunk_control (y : Table (PaddedMatrix.matrix D P) Cell) (j : Fin (blockCount P C)) :
    (rightChunk y j).control=40*D*C+8 := by
  rw [rightChunk,tabulate_control]
  simp only [apply_dite,dite_eq_ite,ite_self,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,smul_eq_mul,PaddedMatrix.matrix,prod,fin]
  ring

theorem run_control (s : Scheme) (hD : 0 < D) (hA : 0 < A) (hC : 0 < C)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : C ≤ D^s.z)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell) :
    (run s hD hA hC hfirst hlast x y).control =
      (∑ i : Fin (blockCount N A), ∑ j : Fin (blockCount P C),
        (BinaryMatrixSetup.execute s.a s.q s.c s.num s.den s.z s.hq hD s.hnum s.hden s.aspect s.inner
          s.ht s.base hfirst hlast (leftChunk x i).value (rightChunk y j).value).control)+
      blockCount N A*(40*A*D+40)+blockCount P C*(40*D*C+40)+
      32*blockCount N A*blockCount P C+48*N*P+48 := by
  simp only [run,tabulate_control,leftChunk_control,rightChunk_control,tabulate_read,
    Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul,
    Fintype.sum_prod_type,PaddedMatrix.matrix,prod,fin]
  ring

/-- The same fully charged scalar bound is used for every padded chunk. -/
def scalarBudget (s : Scheme) (D H : ℕ) :=
  1400*(D.size+3)*(s.q.size+D.size+6)^2+
    BinaryRecursiveCost.bits s.base (BinaryMatrixSetup.select s.q D).value.2 H

theorem run_bits (s : Scheme) (hD : 0 < D) (hA : 0 < A) (hC : 0 < C)
    (hfirst : (A-1)^s.den ≤ D^s.num) (hlast : C ≤ D^s.z)
    (H : ℕ) (hH : 1 ≤ H)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (run s hD hA hC hfirst hlast x y).bitSteps ≤ blockCount N A*blockCount P C*scalarBudget s D H := by
  have hl (i : Fin (blockCount N A)) : (leftChunk x i).bitSteps=0 := by
    rw [leftChunk,tabulate_bits]
    apply Finset.sum_eq_zero; intro a _; split_ifs <;> rfl
  have hr (j : Fin (blockCount P C)) : (rightChunk y j).bitSteps=0 := by
    rw [rightChunk,tabulate_bits]
    apply Finset.sum_eq_zero; intro a _; split_ifs <;> rfl
  have hf := BinaryMatrixSetup.selected_fits s.a s.q s.c D A C s.num s.den s.z s.hq hD s.hnum s.hden
    s.aspect s.inner hfirst hlast
  have hc (i : Fin (blockCount N A)) (j : Fin (blockCount P C)) :=
    PaddedMatrix.execute_bits (fin s.a) (fin s.q) (fin s.c) s.ht s.base _ H hf.1 hf.2.2 hH
      (leftChunk x i).value (rightChunk y j).value (leftChunk_bound x H hx i) (rightChunk_bound y H hy j)
  have hs := BinaryMatrixSetup.select_bits s.q D s.hq hD
  simp only [run,tabulate_bits,hl,hr,Finset.sum_const_zero,zero_add,add_zero,tabulate_read]
  have ht (ij : Fin (blockCount N A) × Fin (blockCount P C)) :
      (BinaryMatrixSetup.execute s.a s.q s.c s.num s.den s.z s.hq hD s.hnum s.hden s.aspect s.inner
        s.ht s.base hfirst hlast (leftChunk x ij.1).value (rightChunk y ij.2).value).bitSteps ≤ scalarBudget s D H :=
    Nat.add_le_add hs (hc ij.1 ij.2)
  have hh := Finset.sum_le_sum (fun ij (_ : ij ∈ Finset.univ) => ht ij)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] using hh

/-- The independent long-side fit is required to absorb the final padded
column chunk. It is not inferred from the number of query rows. -/
theorem batch_fit (N P A C : ℕ) (_hA : 0 < A) (_hC : 0 < C) (hfit : C ≤ P) :
    blockCount N A*blockCount P C*A*C ≤ 2*(N+A)*P := by
  have ha : blockCount N A*A ≤ N+A := by
    rw [blockCount,Nat.ceilDiv_eq_add_pred_div]
    exact (Nat.div_mul_le_self _ _).trans (by omega)
  have hc : blockCount P C*C ≤ P+C := by
    rw [blockCount,Nat.ceilDiv_eq_add_pred_div]
    exact (Nat.div_mul_le_self _ _).trans (by omega)
  have hh := Nat.mul_le_mul ha (hc.trans (show P+C ≤ 2*P by omega))
  convert hh using 1 <;> ring

#print axioms ofCW_valid
#print axioms leftChunk_read
#print axioms rightChunk_read
#print axioms run_correct
#print axioms chunk_bits
#print axioms leftChunk_bound
#print axioms rightChunk_bound
#print axioms leftChunk_control
#print axioms rightChunk_control
#print axioms run_control
#print axioms run_bits
#print axioms batch_fit
end ThinMatrix.RectangularBatch
