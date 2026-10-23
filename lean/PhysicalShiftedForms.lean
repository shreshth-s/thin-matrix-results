import PhysicalSupportProducts

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! The literal integer HIGH forms lifted to the coefficient ring, with
exact private/inner pencils and ordinary forms in each physical half. -/
namespace ThinMatrix.PhysicalShiftedForms
open WalshEmbedding CompleteThinProduct PhysicalWordReindex
open scoped BigOperators
variable {R : Type*} [CommRing R]

noncomputable def lift {L : ℕ} (side : Bool) (i : Fin (2*L)) (label : Fin 5) (w : SourceWord L) : R :=
  (ShiftedPhysicalHigh.form side i label w : R)

theorem full_sum (n : NormalLetter) (o : OppositeLetter) :
    (∑ l : Fin 5, ShiftedHighForms.normalForm n l*oppositeForm (R:=ℤ) o l)=innerCoefficient n o := by
  cases n <;> cases o <;> decide

theorem inner_cast (n : NormalLetter) (o : OppositeLetter) :
    ((innerCoefficient (R:=ℤ) n o : ℤ) : R)=innerCoefficient n o := by
  cases n <;> cases o <;> norm_num [innerCoefficient]

theorem normal_private_cast (n : NormalLetter) :
    ((ShiftedHighForms.normalForm n 4 : ℤ) : R)=ShiftedSourceEmbedding.privateNormal n := by
  change ((ShiftedSourceEmbedding.privateNormal (R:=ℤ) n : ℤ) : R)=_
  cases n <;> norm_num [ShiftedSourceEmbedding.privateNormal]

theorem opposite_private_cast (o : OppositeLetter) :
    ((oppositeForm (R:=ℤ) o 4 : ℤ) : R)=ShiftedSourceEmbedding.privateOpposite o := by
  cases o with
  | s => change ((2:ℤ):R)=2; norm_num
  | v => change ((0:ℤ):R)=0; norm_num
  | w => change ((0:ℤ):R)=0; norm_num

theorem private_left {L : ℕ} (j : Fin L) (x y : SourceWord L) :
    privateKernel (lift (R:=R) true) (lift false) (physicalLeft j) x y=
      ShiftedSourceEmbedding.privateNormal (x.1 j)*ShiftedSourceEmbedding.privateOpposite (y.2 j) := by
  simp only [privateKernel,lift,ShiftedPhysicalHigh.form,Bool.false_eq_true,↓reduceIte,halfLift_left,normal_private_cast,opposite_private_cast]

theorem private_right {L : ℕ} (j : Fin L) (x y : SourceWord L) :
    privateKernel (lift (R:=R) true) (lift false) (physicalRight j) x y=
      ShiftedSourceEmbedding.privateNormal (y.1 j)*ShiftedSourceEmbedding.privateOpposite (x.2 j) := by
  simp only [privateKernel,lift,ShiftedPhysicalHigh.form,Bool.false_eq_true,↓reduceIte,halfLift_right,normal_private_cast,opposite_private_cast,mul_comm]

theorem full_left {L : ℕ} (j : Fin L) (x y : SourceWord L) :
    fullKernel (lift (R:=R) true) (lift false) (physicalLeft j) x y=innerCoefficient (x.1 j) (y.2 j) := by
  simp only [fullKernel,lift,ShiftedPhysicalHigh.form,Bool.false_eq_true,↓reduceIte,halfLift_left,←Int.cast_mul,←Int.cast_sum,full_sum,inner_cast]

theorem full_right {L : ℕ} (j : Fin L) (x y : SourceWord L) :
    fullKernel (lift (R:=R) true) (lift false) (physicalRight j) x y=innerCoefficient (y.1 j) (x.2 j) := by
  simp only [fullKernel,lift,ShiftedPhysicalHigh.form,Bool.false_eq_true,↓reduceIte,halfLift_right,mul_comm,←Int.cast_mul,←Int.cast_sum,full_sum,inner_cast]

theorem normal_ordinary (label : Fin 4) (n : NormalLetter) :
    ShiftedHighForms.normalForm n label.castSucc=PhysicalOrdinaryForms.normal label n := by
  fin_cases label <;> cases n <;> rfl

theorem opposite_ordinary (label : Fin 4) (o : OppositeLetter) :
    oppositeForm (R:=ℤ) o label.castSucc=PhysicalOrdinaryForms.opposite label o := by
  fin_cases label <;> cases o <;> rfl

theorem ordinary_left {L : ℕ} (side : Bool) (j : Fin L) (label : Fin 4) (w : SourceWord L) :
    lift (R:=R) side (physicalLeft j) label.castSucc w=
      if side then (PhysicalOrdinaryForms.normal label (w.1 j) : R) else (PhysicalOrdinaryForms.opposite label (w.2 j) : R) := by
  cases side <;> simp only [lift,ShiftedPhysicalHigh.form,Bool.false_eq_true,↓reduceIte,halfLift_left,normal_ordinary,opposite_ordinary]

theorem ordinary_right {L : ℕ} (side : Bool) (j : Fin L) (label : Fin 4) (w : SourceWord L) :
    lift (R:=R) side (physicalRight j) label.castSucc w=
      if side then (PhysicalOrdinaryForms.opposite label (w.2 j) : R) else (PhysicalOrdinaryForms.normal label (w.1 j) : R) := by
  cases side <;> simp only [lift,ShiftedPhysicalHigh.form,Bool.false_eq_true,↓reduceIte,halfLift_right,normal_ordinary,opposite_ordinary]

#print axioms full_sum
#print axioms inner_cast
#print axioms normal_private_cast
#print axioms opposite_private_cast
#print axioms private_left
#print axioms private_right
#print axioms full_left
#print axioms full_right
#print axioms normal_ordinary
#print axioms opposite_ordinary
#print axioms ordinary_left
#print axioms ordinary_right
end ThinMatrix.PhysicalShiftedForms
