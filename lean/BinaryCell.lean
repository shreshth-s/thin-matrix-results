import BinaryArrayFFT
import BackendScalarBits
import BitArraySimulation

/-! Canonical binary coefficient cells shared by source, LOW and HIGH programs.
All arithmetic consumes bits of stored operands. Integer views occur only in
refinement statements and erased proof fields. -/
namespace ThinMatrix.BinaryCell
open IntegerArithmetic
open scoped BigOperators
abbrev Cell := BinaryArrayFFT.Integer
abbrev Result (A : Type) := FFTBitCost.BinaryResult A

def view (a : Cell) : ℤ := a.view

def zero : Cell := BinaryArrayFFT.zeroInteger
@[simp] theorem zero_view : view zero = 0 := rfl

def fromOperation (op : BackendScalarBits.ScalarInstruction) : Result Cell :=
  let result := BackendScalarBits.execute op
  ⟨⟨result.1,(BackendScalarBits.execute_canonical_width op).trans
    (congrArg (fun z : ℤ => z.natAbs.size) (BackendScalarBits.execute_correct op).symm)⟩,result.2⟩

@[simp] theorem fromOperation_view (op : BackendScalarBits.ScalarInstruction) :
    view (fromOperation op).value = BackendScalarBits.instructionValue op :=
  BackendScalarBits.execute_correct op

def add (a b : Cell) : Result Cell := fromOperation (.add a.bits b.bits)
def sub (a b : Cell) : Result Cell := fromOperation (.subtract a.bits b.bits)
def mul (a b : Cell) : Result Cell := fromOperation (.multiply a.bits b.bits)
def copy (a : Cell) : Result Cell := fromOperation (.copy a.bits)
def neg (a : Cell) : Result Cell := sub zero a

@[simp] theorem add_view (a b : Cell) : view (add a b).value = view a+view b := fromOperation_view _
@[simp] theorem sub_view (a b : Cell) : view (sub a b).value = view a-view b := fromOperation_view _
@[simp] theorem mul_view (a b : Cell) : view (mul a b).value = view a*view b := fromOperation_view _
@[simp] theorem copy_view (a : Cell) : view (copy a).value = view a := fromOperation_view _
@[simp] theorem neg_view (a : Cell) : view (neg a).value = -view a := by simp [neg]

theorem canonical (a : Cell) : a.bits.magnitude.length = (view a).natAbs.size := a.canonical

theorem add_price (B : ℕ) (a b : Cell)
    (ha : (view a).natAbs.size ≤ B) (hb : (view b).natAbs.size ≤ B) :
    (add a b).bitSteps ≤ BackendScalarBits.backendScalarUnit B := by
  have h := BackendScalarBits.execute_price B (.add a.bits b.bits)
    ⟨by simpa only [canonical] using ha,by simpa only [canonical] using hb⟩
  exact h.trans (by unfold BackendScalarBits.backendScalarUnit; omega)

theorem sub_price (B : ℕ) (a b : Cell)
    (ha : (view a).natAbs.size ≤ B) (hb : (view b).natAbs.size ≤ B) :
    (sub a b).bitSteps ≤ BackendScalarBits.backendScalarUnit B := by
  have h := BackendScalarBits.execute_price B (.subtract a.bits b.bits)
    ⟨by simpa only [canonical] using ha,by simpa only [canonical] using hb⟩
  exact h.trans (by unfold BackendScalarBits.backendScalarUnit; omega)

theorem mul_price (B : ℕ) (a b : Cell)
    (ha : (view a).natAbs.size ≤ B) (hb : (view b).natAbs.size ≤ B) :
    (mul a b).bitSteps ≤ BackendScalarBits.backendScalarUnit B := by
  have h := BackendScalarBits.execute_price B (.multiply a.bits b.bits)
    ⟨by simpa only [canonical] using ha,by simpa only [canonical] using hb⟩
  exact h.trans (by unfold BackendScalarBits.backendScalarUnit; omega)

theorem copy_price (B : ℕ) (a : Cell) (ha : (view a).natAbs.size ≤ B) :
    (copy a).bitSteps ≤ BackendScalarBits.backendScalarUnit B := by
  have h := BackendScalarBits.execute_price B (.copy a.bits) (by simpa only [BackendScalarBits.ScalarInstruction.Fits,canonical] using ha)
  exact h.trans (by unfold BackendScalarBits.backendScalarUnit; omega)

def zeroBits : SignedBits := ⟨false,[]⟩
def oneBits : SignedBits := ⟨false,[true]⟩
def twoBits : SignedBits := ⟨false,[false,true]⟩
def negOneBits : SignedBits := ⟨true,[true]⟩
def negTwoBits : SignedBits := ⟨true,[false,true]⟩

def rowCoeffBits (normal : Bool) (row : Fin 6) (col : Fin 4) : SignedBits :=
  if normal then
    ![![oneBits,zeroBits,oneBits,oneBits],![oneBits,zeroBits,oneBits,zeroBits],
      ![zeroBits,oneBits,zeroBits,negOneBits],![zeroBits,oneBits,zeroBits,zeroBits],
      ![negOneBits,negOneBits,oneBits,zeroBits],![zeroBits,zeroBits,zeroBits,oneBits]] row col
  else
    ![![oneBits,oneBits,zeroBits,zeroBits],![oneBits,negOneBits,zeroBits,zeroBits],
      ![oneBits,oneBits,negOneBits,zeroBits],![oneBits,negOneBits,oneBits,zeroBits],
      ![twoBits,zeroBits,zeroBits,zeroBits],![zeroBits,zeroBits,oneBits,zeroBits]] row col

def coefficient (normal : Bool) (row : Fin 6) (col : Fin 4) : Cell :=
  ⟨rowCoeffBits normal row col,by
    cases normal <;> fin_cases row <;> fin_cases col <;> decide⟩

@[simp] theorem coefficient_view (normal : Bool) (row : Fin 6) (col : Fin 4) :
    view (coefficient normal row col) = SparseLocalForms.rowCoefficients normal row col := by
  cases normal <;> fin_cases row <;> fin_cases col <;> rfl

theorem coefficient_size (normal : Bool) (row : Fin 6) (col : Fin 4) :
    (view (coefficient normal row col)).natAbs.size ≤ 2 := by
  cases normal <;> fin_cases row <;> fin_cases col <;> decide

/-- Vector arithmetic stores the joint per-coordinate results once. -/
def vectorAdd {q : ℕ} (a b : Vector Cell q) : Result (Vector Cell q) :=
  let rows := Vector.ofFn (fun i => add (a.get i) (b.get i))
  ⟨rows.map (fun r => r.value),(rows.toList.map (fun r => r.bitSteps)).sum⟩

def vectorSub {q : ℕ} (a b : Vector Cell q) : Result (Vector Cell q) :=
  let rows := Vector.ofFn (fun i => sub (a.get i) (b.get i))
  ⟨rows.map (fun r => r.value),(rows.toList.map (fun r => r.bitSteps)).sum⟩

def vectorZero (q : ℕ) : Vector Cell q := Vector.replicate q zero

@[simp] theorem vectorAdd_view {q : ℕ} (a b : Vector Cell q) (i : Fin q) :
    view ((vectorAdd a b).value.get i) = view (a.get i)+view (b.get i) := by
  simp only [vectorAdd,Vector.get_map,Vector.get_ofFn,add_view]

@[simp] theorem vectorSub_view {q : ℕ} (a b : Vector Cell q) (i : Fin q) :
    view ((vectorSub a b).value.get i) = view (a.get i)-view (b.get i) := by
  simp only [vectorSub,Vector.get_map,Vector.get_ofFn,sub_view]


/-- Strong sign-and-magnitude normalization at interfaces that disallow
negative zero. Only stored bits are inspected; no semantic conversion runs. -/
def toSigned (a : Cell) : Result BitArraySimulation.Signed :=
  let normalized := IntegerArithmetic.normalizeSignedCounted a.bits
  ⟨⟨normalized.1,by
      dsimp only [normalized]
      simp only [BitArraySimulation.Canonical,IntegerArithmetic.normalizeSignedCounted_value,
        IntegerArithmetic.ofInt_correct]⟩,normalized.2⟩

@[simp] theorem toSigned_view (a : Cell) :
    BitArraySimulation.denote (toSigned a).value = view a := by
  simp only [toSigned,BitArraySimulation.denote,IntegerArithmetic.normalizeSignedCounted_value,
    IntegerArithmetic.ofInt_correct,view,BinaryArrayFFT.Integer.view]

theorem toSigned_price (a : Cell) : (toSigned a).bitSteps ≤ 8*(view a).natAbs.size+8 := by
  simpa only [toSigned,canonical] using IntegerArithmetic.normalizeSignedCounted_steps a.bits

#print axioms toSigned_view
#print axioms toSigned_price
#print axioms fromOperation_view
#print axioms add_price
#print axioms coefficient_view
#print axioms coefficient_size
#print axioms vectorAdd_view
#print axioms vectorSub_view
end ThinMatrix.BinaryCell
