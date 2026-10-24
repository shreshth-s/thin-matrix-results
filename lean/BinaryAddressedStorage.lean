import BinaryAddressedControl
import SharedFullyAddressedBatch

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Retained-layout majorants for the addressed recursive product in the
same indexed-array model as BinaryAlignedAPSPTheorem. These count the full
recursive tree, even if dead child workspaces are kept; no compiler or garbage
collector behavior is assumed. Scalar bit buffers are priced separately.
-/
namespace ThinMatrix.BinaryAddressedStorage
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open RecursiveTable (Table prod fin)
open PolynomialDegeneration RetainedEqualCopy BinaryAddressedRecursion
variable {a b c r t : ℕ}

/-- References/records for forms and their operand banks, child padding,
child result banks, and output dots. The factor sixteen accounts for both
operand references, scalar result/partial sum, and tabulation metadata. -/
def localCells (r t A B C k : ℕ) :=
  16*(r*A^k*(t*A+1)+r*B^k*(t*B+1)+
    ((r+t-1)/t)*(t*(A^k+B^k)+1)+t*C^(k+1)*(r+1)+1)

/-- Full retained recursion tree, rather than one table or one active path. -/
def treeCells (r t A B C : ℕ) : ℕ → ℕ
  | 0 => 16*t+16
  | k+1 => ((r+t-1)/t)*treeCells r t A B C k+localCells r t A B C k

theorem forms_cells (ha : 0<a) (hb : 0<b) (k : ℕ)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (x : Cells t a b (k+1)) :
    (forms ha hb k coeff x).value.toList.length=r*(a*b)^k := by
  simp only [Vector.length_toList,BinaryRecursiveTable.layout_size]

theorem padded_cells (ha : 0<a) (hb : 0<b) (k g : ℕ) (x : Cells r a b k) :
    (padded (t:=t) ha hb k g x).value.toList.length=t*(a*b)^k := by
  simp only [Vector.length_toList,BinaryRecursiveTable.layout_size]

theorem child_bank_cells (k : ℕ) (children : Table (fin ((r+t-1)/t)) (Cells t a b k)) :
    (children.toList.map (fun row => row.toList.length)).sum=((r+t-1)/t)*t*(a*b)^k := by
  simp only [Vector.length_toList,BinaryRecursiveTable.layout_size,List.map_const',
    List.sum_replicate,smul_eq_mul,fin]
  ring

theorem output_cells (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) Cell)
    (k : ℕ) (x : Cells t a b k) (y : Cells t b c k) :
    (run ha hb hc ht d k x y).value.toList.length=t*(c*a)^k := by
  simp only [Vector.length_toList,BinaryRecursiveTable.layout_size]

theorem tree_le_control (r t A B C k : ℕ) :
    treeCells r t A B C k≤2*BinaryAddressedRecursion.control r t A B C k := by
  induction k with
  | zero => simp only [treeCells,BinaryAddressedRecursion.control];omega
  | succ k ih =>
    have hh := Nat.mul_le_mul_left ((r+t-1)/t) ih
    simp only [treeCells,localCells,BinaryAddressedRecursion.control]
    ring_nf at hh ⊢
    omega

theorem tree_bound (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (k : ℕ) : treeCells r t (a*b) (b*c) (c*a) k≤
      4*RetainedEqualCopyCosts.levelConstant r t (a*b) (b*c) (c*a)*(k+1)*M^k := by
  have hc := BinaryAddressedRecursion.control_bound r t (a*b) (b*c) (c*a) k
  have hr := BinaryRecursiveUniform.recurrence_bounds ht d M hM hg hAB hBC hCA k
  have ht' := tree_le_control r t (a*b) (b*c) (c*a) k
  simp only [prod,fin] at hr
  nlinarith

/-- Original arrays, binary padding/recovery outputs, cleared fixed-base
coefficients, denominator powers, recursion frames, and the full child tree. -/
def matrixCells (r t a b c n m p k : ℕ) :=
  16*(n*m+m*p+n*p+t*((a*b)^k+(b*c)^k+(c*a)^k)+r*t*(a*b+b*c+c*a)+k+1)+
    treeCells r t (a*b) (b*c) (c*a) k

def matrixConstant (r t a b c : ℕ) :=
  16*(5+3*t+r*t*(a*b+b*c+c*a))+4*RetainedEqualCopyCosts.levelConstant r t (a*b) (b*c) (c*a)

theorem matrix_bound (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (n m p k : ℕ) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k) :
    matrixCells r t a b c n m p k≤ matrixConstant r t a b c*(k+1)*M^k := by
  have htree := tree_bound ht d M hM hg hAB hBC hCA k
  have hab := Nat.pow_le_pow_left hAB k
  have hbc := Nat.pow_le_pow_left hBC k
  have hca := Nat.pow_le_pow_left hCA k
  have hnm : n*m≤(a*b)^k := by simpa only [mul_pow] using Nat.mul_le_mul hn hm
  have hmp : m*p≤(b*c)^k := by simpa only [mul_pow] using Nat.mul_le_mul hm hp
  have hnp : n*p≤(c*a)^k := by simpa only [mul_pow,mul_comm] using Nat.mul_le_mul hn hp
  have hpow : 1≤M^k := one_le_pow₀ hM
  have hsum : n*m+m*p+n*p+t*((a*b)^k+(b*c)^k+(c*a)^k)+r*t*(a*b+b*c+c*a)+k+1≤
      (5+3*t+r*t*(a*b+b*c+c*a))*(k+1)*M^k := by
    have hdim : n*m+m*p+n*p+t*((a*b)^k+(b*c)^k+(c*a)^k)≤(3+3*t)*M^k := by
      nlinarith [Nat.mul_le_mul_left t hab,Nat.mul_le_mul_left t hbc,Nat.mul_le_mul_left t hca]
    have hdim' := hdim.trans (Nat.le_mul_of_pos_left _ (show 1≤k+1 by omega))
    have hfixed := Nat.mul_le_mul_left (r*t*(a*b+b*c+c*a))
      (show 1≤(k+1)*M^k by nlinarith)
    have hk : k+1≤(k+1)*M^k := Nat.le_mul_of_pos_right _ hpow
    nlinarith
  unfold matrixCells matrixConstant
  nlinarith

theorem matrix_size (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (n m p k : ℕ) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k) :
    (matrixCells r t a b c n m p k).size≤
      (matrixConstant r t a b c).size+(k+1).size+k*M.size+1 := by
  have hs := Nat.size_le_size (matrix_bound ht d M hM hg hAB hBC hCA n m p k hn hm hp)
  have hprod := BinaryMultiplierAdapter.size_mul (matrixConstant r t a b c*(k+1)) (M^k)
  have hinner := BinaryMultiplierAdapter.size_mul (matrixConstant r t a b c) (k+1)
  have hpow := BinaryRetainedBounds.size_power M k
  omega

/-- A retained scalar slot carries a magnitude, sign, bounded local addresses
and counters. `bitWidth` is the already proved common width of these fields.
All fields of every retained record are included; input tables are separate. -/
def bitCells (cells bitWidth : ℕ) := 32*(cells+1)*(bitWidth+1)

/-- Convert a concrete polynomial-in-dimension layout majorant into an
explicit binary address width, without assuming a fixed final width. -/
theorem bitCells_size (cells bitWidth : ℕ) :
    (bitCells cells bitWidth).size≤8+cells.size+bitWidth.size := by
  unfold bitCells
  have hsucc (n : ℕ) : (n+1).size≤n.size+1 := by
    apply Nat.size_le.mpr
    have hh : n<2^n.size := Nat.size_le.mp (le_refl _)
    rw [pow_succ]
    have hp : 0<2^n.size := pow_pos (by decide) _
    omega
  have hc := hsucc cells
  have hw := hsucc bitWidth
  have hmul := BinaryMultiplierAdapter.size_mul (32*(cells+1)) (bitWidth+1)
  have hinner := BinaryMultiplierAdapter.size_mul 32 (cells+1)
  have hs : Nat.size 32=6 := by decide
  rw [hs] at hinner
  omega

/-- Every address in the complete retained matrix tree has the displayed
width, including all previous child arrays. -/
theorem tree_address_size (cells bitWidth j : ℕ) (hj : j<bitCells cells bitWidth) :
    j.size≤8+cells.size+bitWidth.size :=
  (Nat.size_le_size hj.le).trans (bitCells_size cells bitWidth)

/-- Outer banks and all product trees are retained together. Input cells,
chunk arrays, every product result, output rows and one local stack per tree
are present in this majorant. -/
def batchCells (N D P A C recursiveCells : ℕ) :=
  N*D+D*P+SharedFullyAddressedBatch.outerCells N D P A C+
    CompactBlocks.blockCount N A*CompactBlocks.blockCount P C*(recursiveCells+1)+1

theorem batch_contains_outer (N D P A C recursiveCells : ℕ) :
    SharedFullyAddressedBatch.outerCells N D P A C≤batchCells N D P A C recursiveCells := by
  unfold batchCells
  omega

theorem batch_contains_all_trees (N D P A C recursiveCells : ℕ) :
    CompactBlocks.blockCount N A*CompactBlocks.blockCount P C*recursiveCells≤batchCells N D P A C recursiveCells := by
  unfold batchCells
  nlinarith

#print axioms forms_cells
#print axioms padded_cells
#print axioms child_bank_cells
#print axioms output_cells
#print axioms tree_le_control
#print axioms tree_bound
#print axioms matrix_bound
#print axioms matrix_size
#print axioms bitCells_size
#print axioms tree_address_size
#print axioms batch_contains_outer
#print axioms batch_contains_all_trees
end ThinMatrix.BinaryAddressedStorage
