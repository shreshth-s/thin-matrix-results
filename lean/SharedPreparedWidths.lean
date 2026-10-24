import SharedFullyAddressedBatch
import BinaryAddressedPrice
import SharedCompletionWidths

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace ThinMatrix.SharedPreparedWidths
open RectangularBatch (Scheme)
open SharedFullyAddressedBatch (growth growth_properties)
variable {D A Z : ℕ}

def cells (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A Z) :=
  BinaryAddressedStorage.matrixCells scheme.r scheme.t scheme.a scheme.q scheme.c A D Z shape.depth

def fields (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A Z) (H : ℕ) :=
  BinaryAddressedPrice.fieldWidth scheme.base (growth scheme) shape.depth H

def cellSlope (scheme : Scheme) :=
  BinaryAddressedPrice.storageSlope scheme.r scheme.t scheme.a scheme.q scheme.c (growth scheme)

def fieldSlope (scheme : Scheme) := BinaryAddressedPrice.fieldSlope scheme.base (growth scheme)

theorem cells_size (scheme : Scheme) (hD : 0 < D)
    (hf : (A-1)^scheme.den ≤ D^scheme.num) (hl : Z ≤ D^scheme.z) :
    (cells scheme (SharedMatrixSetup.prepare scheme hD hf hl).value).size ≤ cellSlope scheme*(D.size+2) := by
  let shape := (SharedMatrixSetup.prepare scheme hD hf hl).value
  have hg := growth_properties scheme
  have hh := BinaryAddressedPrice.matrix_width scheme.ht scheme.base (growth scheme)
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 A D Z shape.depth
    shape.first_fit shape.middle_fit shape.last_fit
  have hk := (BinaryMatrixSetup.select_bounds scheme.q D scheme.hq hD).2.2
  apply hh.trans
  apply Nat.mul_le_mul_left
  change (BinaryMatrixSetup.select scheme.q D).value.2+1 ≤ D.size+2
  omega

theorem field_width (scheme : Scheme) (hD : 0 < D)
    (hf : (A-1)^scheme.den ≤ D^scheme.num) (hl : Z ≤ D^scheme.z) (H : ℕ) :
    fields scheme (SharedMatrixSetup.prepare scheme hD hf hl).value H ≤ fieldSlope scheme*(D.size+H.size+3) := by
  have hh := BinaryAddressedPrice.field_width scheme.base (growth scheme)
    (SharedMatrixSetup.prepare scheme hD hf hl).value.depth H
  have hk := (BinaryMatrixSetup.select_bounds scheme.q D scheme.hq hD).2.2
  apply hh.trans
  apply Nat.mul_le_mul_left
  change (BinaryMatrixSetup.select scheme.q D).value.2+H.size+2 ≤ D.size+H.size+3
  omega

/-- All recursive matrix trees and the scalar/address/cost-counter fields
are bounded from the chosen support size and input bit width. No desired
runtime or pre-assumed machine address budget is used. -/
theorem retained_power_bounds (scheme : Scheme) (hD : 0 < D)
    (hf : (A-1)^scheme.den ≤ D^scheme.num) (hl : Z ≤ D^scheme.z) (H U : ℕ)
    (hcell : cellSlope scheme*(D.size+2) ≤ U)
    (hfield : fieldSlope scheme*(D.size+H.size+3) ≤ U) :
    cells scheme (SharedMatrixSetup.prepare scheme hD hf hl).value ≤ 2^U ∧
    fields scheme (SharedMatrixSetup.prepare scheme hD hf hl).value H ≤ U := by
  constructor
  · exact (Nat.size_le.mp ((cells_size scheme hD hf hl).trans hcell)).le
  · exact (field_width scheme hD hf hl H).trans hfield

#print axioms cells_size
#print axioms field_width
#print axioms retained_power_bounds
end ThinMatrix.SharedPreparedWidths
