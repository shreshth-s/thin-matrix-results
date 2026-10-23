import BinaryRecursiveCost
import MatrixPowerReindex
import CWRetainedArithmetic

set_option autoImplicit false

/-! Ordinary row/inner/column matrix arrays at tensor-power dimensions.
Reindexing copies every input/output slot once. Arbitrary dimensions still
require their own next-power padding adapter and address-cost proof. -/
namespace ThinMatrix.BinaryMatrixPowers
open scoped BigOperators
open RecursiveTable (Layout Table prod fin power read)
open RetainedEqualCopy (Base copies)
open PolynomialDegeneration FiniteMatrixPowers MatrixPowerReindex
open BinaryCell BinaryRecursiveDot
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] {r t : ℕ}

def matrixLayout {A B : Type} (t : ℕ) (a : Layout A) (b : Layout B) (k : ℕ) :=
  prod (fin t) (prod (power a k) (power b k))

def toWords {A B : Type} (a : Layout A) (b : Layout B) (k : ℕ)
    (x : Table (matrixLayout t a b k) Cell) : Run (Table (copies t (prod a b) k) Cell) :=
  tabulate (copies t (prod a b) k) (fun p => ⟨read x (p.1,unpair k p.2),0,8⟩)

def fromWords {A B : Type} (a : Layout A) (b : Layout B) (k : ℕ)
    (x : Table (copies t (prod a b) k) Cell) : Run (Table (matrixLayout t a b k) Cell) :=
  tabulate (matrixLayout t a b k) (fun p => ⟨read x (p.1,pair k p.2),0,8⟩)

def execute (a : Layout A) (b : Layout B) (c : Layout C) (ht : 0<t)
    (d : Base r t (prod a b) (prod b c) (prod c a) ℚ) (k : ℕ)
    (x : Table (matrixLayout t a b k) Cell) (y : Table (matrixLayout t b c k) Cell) :
    Run (Table (matrixLayout t c a k) Cell) :=
  let left := toWords a b k x
  let right := toWords b c k y
  let answer := BinaryRecursiveRecovery.execute ht d k left.value right.value
  let output := fromWords c a k answer.value
  ⟨output.value,left.bitSteps+right.bitSteps+answer.bitSteps+output.bitSteps,
    left.control+right.control+answer.control+output.control+16⟩

set_option backward.isDefEq.respectTransparency false in
theorem execute_correct (a : Layout A) (b : Layout B) (c : Layout C) (ht : 0<t)
    (d : Base r t (prod a b) (prod b c) (prod c a) ℚ)
    (hd : FiniteTrilinear.total d.terms=FiniteDirectSum.diagonal (Fin t)
      (FiniteMatrixTensor.coeff A B C ℚ)) (k : ℕ)
    (x : Table (matrixLayout t a b k) Cell) (y : Table (matrixLayout t b c k) Cell)
    (z : Fin t×(PowerIndex C k×PowerIndex A k)) :
    view (read (execute a b c ht d k x y).value z)=
      ∑ v : PowerIndex B k,view (read x (z.1,(z.2.2,v)))*view (read y (z.1,(v,z.2.1))) := by
  have hc : FiniteTrilinear.total d.terms=FiniteDirectSum.diagonal (Fin t)
      (fun i j l => ((FiniteMatrixTensor.coeff A B C ℤ i j l):ℚ)) := by
    rw [hd]
    congr 1
    funext i j l
    simp [FiniteMatrixTensor.coeff]
  have hh := BinaryRecursiveRecovery.execute_correct ht d (FiniteMatrixTensor.coeff A B C ℤ) hc k
    (toWords a b k x).value (toWords b c k y).value (z.1,pair k z.2)
  simp only [toWords,tabulate_read] at hh
  have hv := bilinear_matrix k (fun p => view (read x (z.1,p))) (fun q => view (read y (z.1,q))) z.2
  have hout := hh.trans hv
  simpa only [execute,toWords,fromWords,tabulate_read] using hout

theorem reshape_costs {A B : Type} [Fintype A] [Fintype B]
    (a : Layout A) (b : Layout B) (k : ℕ)
    (x : Table (matrixLayout t a b k) Cell) (y : Table (copies t (prod a b) k) Cell) :
    (toWords a b k x).bitSteps=0 ∧ (fromWords a b k y).bitSteps=0 ∧
    (toWords a b k x).control=40*t*(a.size*b.size)^k+8 ∧
    (fromWords a b k y).control=40*t*(a.size*b.size)^k+8 := by
  simp only [toWords,fromWords,tabulate_bits,tabulate_control,Finset.sum_const_zero,
    Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,powerIndex_card,smul_eq_mul]
  rw [←RecursiveTable.size_eq_card a,←RecursiveTable.size_eq_card b]
  simp only [copies,matrixLayout,prod,fin,RecursiveTable.power_size,and_self_left]
  simp only [mul_pow]
  ring_nf
  trivial

/-- The actual extracted CW base, with its original copy labels, supplies
the matrix program. No fast-multiplier oracle is a premise. -/
theorem cw_correct (s : ℕ) (h : CWTargetExtractionRate.Sample s)
    (ht : 0<CWHomogeneousCopies.copies s h) (k : ℕ)
    (x : Table (matrixLayout (CWHomogeneousCopies.copies s h)
      (fin (CWHomogeneousCopies.cols s)) (fin (CWHomogeneousCopies.rows s)) k) Cell)
    (y : Table (matrixLayout (CWHomogeneousCopies.copies s h)
      (fin (CWHomogeneousCopies.rows s)) (fin (CWHomogeneousCopies.inners s)) k) Cell)
    (z : Fin (CWHomogeneousCopies.copies s h)×
      (PowerIndex (Fin (CWHomogeneousCopies.inners s)) k×PowerIndex (Fin (CWHomogeneousCopies.cols s)) k)) :
    view (read (execute (fin (CWHomogeneousCopies.cols s)) (fin (CWHomogeneousCopies.rows s))
      (fin (CWHomogeneousCopies.inners s)) ht (CWRetainedArithmetic.base s h) k x y).value z)=
      ∑ v : PowerIndex (Fin (CWHomogeneousCopies.rows s)) k,
        view (read x (z.1,(z.2.2,v)))*view (read y (z.1,(v,z.2.1))) :=
  execute_correct _ _ _ ht _ (CWRetainedArithmetic.base_total s h) k x y z

#print axioms execute_correct
#print axioms reshape_costs
#print axioms cw_correct
end ThinMatrix.BinaryMatrixPowers
