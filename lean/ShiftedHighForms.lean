import BinaryCroppedHighInput
import ShiftedSourceEmbedding

set_option autoImplicit false

/-! The actual shifted HIGH coefficient ROM. Ordinary normal forms exclude
p1 and the private normal form is -x1-x2+p1. Opposite forms are unchanged.
The generic joint-cap encoder consumes these binary literals directly. -/
namespace ThinMatrix.ShiftedHighForms
open BinaryCell WalshEmbedding CacheBounds BinaryHighExecution
open scoped BigOperators

def negOne : Cell := ⟨⟨true,[true]⟩,by decide⟩
@[simp] theorem negOne_view : view negOne = -1 := rfl

def normalCell : Fin 6 → Fin 4 → Cell :=
  ![![BinaryModularCell.one,zero,zero,BinaryModularCell.one],
    ![BinaryModularCell.one,zero,zero,zero],
    ![zero,BinaryModularCell.one,zero,negOne],
    ![zero,BinaryModularCell.one,zero,zero],
    ![negOne,negOne,BinaryModularCell.one,zero],
    ![zero,zero,zero,zero]]

def normalForm (n : NormalLetter) : Fin 5 → ℤ :=
  ![ShiftedSourceEmbedding.ordinaryNormal false false n,
    ShiftedSourceEmbedding.ordinaryNormal false true n,
    ShiftedSourceEmbedding.ordinaryNormal true false n,
    ShiftedSourceEmbedding.ordinaryNormal true true n,
    ShiftedSourceEmbedding.privateNormal n]

def coefficient (normal : Bool) (row : Fin 6) (col : Fin 4) : Cell :=
  if normal then normalCell row col else highCoefficient false row col

theorem normalCell_view (row : Fin 5) (col : Fin 4) :
    view (normalCell row.castSucc col) = normalForm (SourceCoordinates.normalEquiv col) row := by
  fin_cases row <;> fin_cases col <;> rfl

theorem normalCell_private (col : Fin 4) :
    view (normalCell 4 col) = (![-1,-1,1,0] : Fin 4 → ℤ) col := by fin_cases col <;> rfl

theorem coefficient_magnitude (normal : Bool) (row : Fin 6) (col : Fin 4) :
    |view (coefficient normal row col)| ≤ 2 := by
  cases normal
  · exact highCoefficient_magnitude false row col
  · change |view (normalCell row col)| ≤ 2
    fin_cases row <;> fin_cases col <;> decide

/-- Literal finite ROM, including zero outside its valid dimensions. -/
def forms (L : ℕ) (side : Bool) : Forms := fun d row raw =>
  if hc : raw < 4 then
    if row.val < 5 then coefficient (if d < L then side else !side) row ⟨raw,hc⟩
    else zero
  else zero

def integerForms (L : ℕ) (side : Bool) : SharedEncoder.LocalForms ℤ :=
  fun d row raw => view (forms L side d row raw)

theorem forms_magnitude (L : ℕ) (side : Bool) (d : ℕ) (row : Label) (raw : ℕ) :
    |view (forms L side d row raw)| ≤ 2 := by
  unfold forms
  split
  · split
    · exact coefficient_magnitude _ _ _
    · norm_num
  · norm_num

theorem nativeForms_eq (L q : ℕ) (side : Bool) :
    nativeForms (forms L side) q = (fun d row raw => (integerForms L side d row raw : Vector ℤ q)) := rfl

/-- This is the five-term identity used by the shifted source contraction,
with exactly the normal ROM's four ordinary rows and its private row. -/
theorem local_identity (n : NormalLetter) (o : OppositeLetter) :
    (∑ row : Fin 4, normalForm n row.castSucc *
      (![ordinaryOpposite false false o,ordinaryOpposite false true o,
        ordinaryOpposite true false o,ordinaryOpposite true true o] : Fin 4 → ℤ) row) +
      normalForm n 4 * ShiftedSourceEmbedding.privateOpposite o = innerCoefficient n o := by
  cases n <;> cases o <;> decide

#print axioms negOne_view
#print axioms normalCell_view
#print axioms normalCell_private
#print axioms coefficient_magnitude
#print axioms forms_magnitude
#print axioms nativeForms_eq
#print axioms local_identity
end ThinMatrix.ShiftedHighForms
