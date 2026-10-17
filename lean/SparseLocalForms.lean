import CoefficientBounds

/-!
# Integer coefficient-vector implementation of the six cache forms

The input and output grids contain all `q * width` integer cells.  The only
auxiliary-degree shift is the `p₁` term of normal row four, `H(z)`.  Missing
negative degrees read zero.  Opposite coordinates are `s,v,w,0`; no cyclic
multiplication or inverse of an integer is used by these linear operations.

`cellProgram` is an explicit thirteen-instruction register program: four
read/scale/add blocks, then one output write.  `denseLocalRow` materializes
the programs' outputs in nested arrays, rather than returning a function
which reruns the computation at each read.  Its scalar-site count includes
a conservative initialization charge for every cell.
These are integer scalar operations; a word-RAM implementation and signed
integer representation are separate interfaces.
-/

namespace ThinMatrix.SparseLocalForms

open scoped BigOperators
open Polynomial CyclicRing CoefficientBounds

abbrev CoeffVector (q width : ℕ) := Fin width → Fin q → ℤ

def rowCoefficients (firstNormal : Bool) (row : Fin 6) : Fin 4 → ℤ :=
  if firstNormal then normalRowCoefficients row else oppositeRowCoefficients row

def shifted (firstNormal : Bool) (row : Fin 6) (col : Fin 4) : Bool :=
  firstNormal && decide (row = 4 ∧ col = 2)

def readCell {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width) (col : Fin 4)
    (degree : Fin width) (residue : Fin q) : ℤ :=
  if shifted firstNormal row col then
    if h : 0 < degree.val then
      children col ⟨degree.val - 1, by omega⟩ residue
    else 0
  else children col degree residue

/-- Four fixed-coefficient terms, including a zero read at degree zero
when a positive auxiliary shift is requested. -/
def localRow {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width) : CoeffVector q width :=
  fun degree residue => ∑ col, rowCoefficients firstNormal row col *
    readCell firstNormal row children col degree residue

/-- The semantic polynomial form; the scalar shift occurs before truncation. -/
noncomputable def localPolynomial {R : Type*} [CommRing R]
    (firstNormal : Bool) (row : Fin 6) (children : Fin 4 → R[X]) : R[X] :=
  ∑ col, C (rowCoefficients firstNormal row col : R) *
    (if shifted firstNormal row col then X * children col else children col)

theorem normal_localPolynomial {R : Type*} [CommRing R]
    (children : Fin 4 → R[X]) :
    (fun row => localPolynomial true row children) =
      ![children 0 + children 2 + children 3,
        children 0 + children 2, children 1 - children 3, children 1,
        -children 0 - children 1 + X * children 2, children 3] := by
  funext row
  fin_cases row <;>
    simp [localPolynomial, rowCoefficients, shifted,
      normalRowCoefficients, Fin.sum_univ_succ] <;> ring

theorem opposite_localPolynomial {R : Type*} [CommRing R]
    (children : Fin 4 → R[X]) :
    (fun row => localPolynomial false row children) =
      ![children 0 + children 1, children 0 - children 1,
        children 0 + children 1 - children 2,
        children 0 - children 1 + children 2,
        2 * children 0, children 2] := by
  funext row
  fin_cases row <;>
    simp [localPolynomial, rowCoefficients, shifted,
      oppositeRowCoefficients, Fin.sum_univ_succ] <;> ring

/-- A three-coordinate opposite source is padded by one literal zero
array. No fourth raw coordinate is contracted or counted as input data. -/
def padOpposite {q width : ℕ} (children : Fin 3 → CoeffVector q width) :
    Fin 4 → CoeffVector q width :=
  fun col => if h : col.val < 3 then children ⟨col.val,h⟩ else fun _ _ => 0

theorem padOpposite_get {q width : ℕ} (children : Fin 3 → CoeffVector q width)
    (col : Fin 3) : padOpposite children col.castSucc = children col := by
  simp [padOpposite, col.isLt]

theorem padOpposite_last {q width : ℕ} (children : Fin 3 → CoeffVector q width) :
    padOpposite children 3 = fun _ _ => 0 := by
  simp [padOpposite]

theorem opposite_fourth_ignored {q width : ℕ}
    (children : Fin 4 → CoeffVector q width) (extra : CoeffVector q width)
    (row : Fin 6) :
    localRow false row (Function.update children 3 extra) = localRow false row children := by
  funext degree residue
  fin_cases row <;>
    simp [localRow, rowCoefficients, oppositeRowCoefficients, shifted, readCell,
      Fin.sum_univ_succ]

/-- Extracting the first `width` auxiliary coefficients keeps the complete
cyclic vector at every degree. -/
noncomputable def extract {q width : ℕ} [NeZero q] (p : (Cyclic q)[X]) : CoeffVector q width :=
  fun degree residue => p.coeff degree.val residue

theorem readCell_extract {q width : ℕ} [NeZero q]
    (firstNormal : Bool) (row : Fin 6) (children : Fin 4 → (Cyclic q)[X])
    (col : Fin 4) (degree : Fin width) (residue : Fin q) :
    readCell firstNormal row (fun c => extract (children c)) col degree residue =
      ((if shifted firstNormal row col then X * children col else children col).coeff
        degree.val) residue := by
  by_cases hs : shifted firstNormal row col = true
  · simp only [readCell, hs, ↓reduceIte]
    split
    · rename_i hd
      have heq : degree.val = (degree.val - 1) + 1 := by omega
      simp only [extract]
      conv_rhs => rw [heq]
      rw [coeff_X_mul]
    · rename_i hd
      have heq : degree.val = 0 := by omega
      simp [heq]
  · simp [readCell, hs, extract]

/-- Each concrete stored row equals its polynomial form on every retained
degree and residue; coefficients above the truncation never need reading. -/
theorem localRow_extract {q width : ℕ} [NeZero q]
    (firstNormal : Bool) (row : Fin 6) (children : Fin 4 → (Cyclic q)[X]) :
    localRow firstNormal row (fun c => extract (children c)) =
      (extract (localPolynomial firstNormal row children) : CoeffVector q width) := by
  funext degree residue
  unfold localRow extract localPolynomial
  rw [Polynomial.finsetSum_coeff, CyclicRing.sum_coeff]
  apply Finset.sum_congr rfl
  intro col _
  rw [Polynomial.coeff_C_mul, intCast_mul_coeff]
  congr 1
  exact readCell_extract firstNormal row children col degree residue

theorem rowCoefficients_bound (firstNormal : Bool) (row : Fin 6) (col : Fin 4) :
    |rowCoefficients firstNormal row col| ≤ 2 := by
  cases firstNormal <;> simp only [rowCoefficients, Bool.false_eq_true, ↓reduceIte]
  · exact oppositeRowCoefficients_bound row col
  · exact normalRowCoefficients_bound row col

theorem row_budget (firstNormal : Bool) (row : Fin 6) :
    (∑ col, |rowCoefficients firstNormal row col|) ≤ 8 := by
  cases firstNormal <;> simp only [rowCoefficients, Bool.false_eq_true, ↓reduceIte]
  · exact oppositeRow_budget row
  · exact normalRow_budget row

theorem readCell_bound {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width) (A : ℤ) (hA : 0 ≤ A)
    (hc : ∀ col degree residue, |children col degree residue| ≤ A)
    (col : Fin 4) (degree : Fin width) (residue : Fin q) :
    |readCell firstNormal row children col degree residue| ≤ A := by
  unfold readCell
  split
  · split
    · exact hc _ _ _
    · simpa using hA
  · exact hc _ _ _

/-- All partial accumulators, not only the final row, obey the row budget. -/
theorem partial_accumulator_bound {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width) (A : ℤ) (hA : 0 ≤ A)
    (hc : ∀ col degree residue, |children col degree residue| ≤ A)
    (degree : Fin width) (residue : Fin q) (s : Finset (Fin 4)) :
    |∑ col ∈ s, rowCoefficients firstNormal row col *
      readCell firstNormal row children col degree residue| ≤ 8*A :=
  partial_linear_node_bound _ _ (row_budget firstNormal row) s A hA
    (fun col => readCell_bound firstNormal row children A hA hc col degree residue)

theorem scaled_temporary_bound {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width) (A : ℤ) (hA : 0 ≤ A)
    (hc : ∀ col degree residue, |children col degree residue| ≤ A)
    (col : Fin 4) (degree : Fin width) (residue : Fin q) :
    |rowCoefficients firstNormal row col *
      readCell firstNormal row children col degree residue| ≤ 2*A := by
  rw [abs_mul]
  exact mul_le_mul (rowCoefficients_bound firstNormal row col)
    (readCell_bound firstNormal row children A hA hc col degree residue)
    (abs_nonneg _) (by norm_num)

/-- The three integer registers used by a single scalar cell program. -/
structure Registers where
  temporary : ℤ := 0
  accumulator : ℤ := 0
  output : ℤ := 0
  deriving DecidableEq

inductive Instruction where
  | read (column : Fin 4)
  | scale (coefficient : ℤ)
  | add
  | write
  deriving DecidableEq

def executeInstruction (read : Fin 4 → ℤ) : Instruction → Registers → Registers
  | .read col, state => { state with temporary := read col }
  | .scale coefficient, state => { state with temporary := coefficient * state.temporary }
  | .add, state => { state with accumulator := state.accumulator + state.temporary }
  | .write, state => { state with output := state.accumulator }

def cellProgram (firstNormal : Bool) (row : Fin 6) : List Instruction :=
  [.read 0, .scale (rowCoefficients firstNormal row 0), .add,
   .read 1, .scale (rowCoefficients firstNormal row 1), .add,
   .read 2, .scale (rowCoefficients firstNormal row 2), .add,
   .read 3, .scale (rowCoefficients firstNormal row 3), .add, .write]

def executeCell {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width)
    (degree : Fin width) (residue : Fin q) : Registers :=
  (cellProgram firstNormal row).foldl
    (fun state instruction => executeInstruction
      (fun col => readCell firstNormal row children col degree residue) instruction state) {}

theorem executeCell_correct {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width) (degree : Fin width) (residue : Fin q) :
    (executeCell firstNormal row children degree residue).output =
      localRow firstNormal row children degree residue := by
  simp [executeCell, cellProgram, executeInstruction, localRow, Fin.sum_univ_succ,
    add_assoc]

theorem cellProgram_length (firstNormal : Bool) (row : Fin 6) :
    (cellProgram firstNormal row).length = 13 := rfl

def grid (q width : ℕ) : List (Fin width × Fin q) :=
  (List.finRange width).flatMap fun degree =>
    (List.finRange q).map fun residue => (degree, residue)

theorem mem_grid {q width : ℕ} (key : Fin width × Fin q) : key ∈ grid q width := by
  simp [grid]

theorem grid_length (q width : ℕ) : (grid q width).length = width*q := by
  simp [grid, List.length_flatMap]

/-- The scalar-site counter follows the actual list of cell programs
tabulated by `denseLocalRow`, plus one initialization charge per cell. -/
def materializeScalarCost (q width : ℕ) (firstNormal : Bool) (row : Fin 6) : ℕ :=
  (grid q width).length +
    ((grid q width).map fun _ => (cellProgram firstNormal row).length).sum

theorem materializeScalarCost_eq (q width : ℕ) (firstNormal : Bool) (row : Fin 6) :
    materializeScalarCost q width firstNormal row = 14*q*width := by
  simp [materializeScalarCost, cellProgram_length, grid_length]
  ring

/-- Actual nested arrays, with `q` stored residues for every auxiliary degree. -/
abbrev DenseVector (q width : ℕ) := Vector (Vector ℤ q) width

def denseRead {q width : ℕ} (v : DenseVector q width) : CoeffVector q width :=
  fun degree residue => (v.get degree).get residue

def toDense {q width : ℕ} (v : CoeffVector q width) : DenseVector q width :=
  Vector.ofFn fun degree => Vector.ofFn fun residue => v degree residue

theorem denseRead_toDense {q width : ℕ} (v : CoeffVector q width) :
    denseRead (toDense v) = v := by
  funext degree residue
  simp [denseRead, toDense]

/-- Nested `Vector.ofFn` materializes each cell once. Subsequent reads use
the backing array; they do not rerun its thirteen-instruction program. -/
def denseLocalRow {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → DenseVector q width) : DenseVector q width :=
  Vector.ofFn fun degree => Vector.ofFn fun residue =>
    (executeCell firstNormal row (fun col => denseRead (children col)) degree residue).output

theorem denseLocalRow_correct {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → DenseVector q width) :
    denseRead (denseLocalRow firstNormal row children) =
      localRow firstNormal row (fun col => denseRead (children col)) := by
  funext degree residue
  simp [denseRead, denseLocalRow, executeCell_correct]

theorem denseLocalRow_extract {q width : ℕ} [NeZero q]
    (firstNormal : Bool) (row : Fin 6) (children : Fin 4 → (Cyclic q)[X]) :
    denseRead (denseLocalRow firstNormal row (fun col => toDense (extract (children col)))) =
      (extract (localPolynomial firstNormal row children) : CoeffVector q width) := by
  rw [denseLocalRow_correct]
  simpa only [denseRead_toDense] using localRow_extract firstNormal row children

theorem localRow_bound {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → CoeffVector q width) (A : ℤ) (hA : 0 ≤ A)
    (hc : ∀ col degree residue, |children col degree residue| ≤ A)
    (degree : Fin width) (residue : Fin q) :
    |localRow firstNormal row children degree residue| ≤ 8*A := by
  simpa only [localRow] using
    partial_accumulator_bound firstNormal row children A hA hc degree residue Finset.univ

theorem denseLocalRow_bound {q width : ℕ} (firstNormal : Bool) (row : Fin 6)
    (children : Fin 4 → DenseVector q width) (A : ℤ) (hA : 0 ≤ A)
    (hc : ∀ col degree residue, |denseRead (children col) degree residue| ≤ A)
    (degree : Fin width) (residue : Fin q) :
    |denseRead (denseLocalRow firstNormal row children) degree residue| ≤ 8*A := by
  rw [denseLocalRow_correct]
  exact localRow_bound firstNormal row _ A hA hc degree residue

/-- The six children of one shared prefix need no general ring products. -/
theorem six_row_scalar_cost (q width : ℕ) (firstNormal : Bool) :
    (∑ row : Fin 6, materializeScalarCost q width firstNormal row) = 84*q*width := by
  simp [materializeScalarCost_eq]
  ring

end ThinMatrix.SparseLocalForms

#print axioms ThinMatrix.SparseLocalForms.normal_localPolynomial
#print axioms ThinMatrix.SparseLocalForms.opposite_localPolynomial
#print axioms ThinMatrix.SparseLocalForms.opposite_fourth_ignored
#print axioms ThinMatrix.SparseLocalForms.localRow_extract
#print axioms ThinMatrix.SparseLocalForms.partial_accumulator_bound
#print axioms ThinMatrix.SparseLocalForms.scaled_temporary_bound
#print axioms ThinMatrix.SparseLocalForms.executeCell_correct
#print axioms ThinMatrix.SparseLocalForms.materializeScalarCost_eq
#print axioms ThinMatrix.SparseLocalForms.denseLocalRow_extract
#print axioms ThinMatrix.SparseLocalForms.denseLocalRow_bound
#print axioms ThinMatrix.SparseLocalForms.six_row_scalar_cost
