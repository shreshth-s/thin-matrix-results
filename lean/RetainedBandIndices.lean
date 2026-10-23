import NormalizedCoefficientCollection

set_option autoImplicit false

/-! Enumerate actual stored-width band indices once. The arithmetic here is
indexed-register control; no binary cost for native division is asserted. -/
namespace ThinMatrix.RetainedBandIndices
open BinaryGroupedCoordinates

def produce {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (N : ℕ) :
    Run (Vector (Fin (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth L m)))
      (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth L m))) :=
  let count := TilingCosts.bandCount N shape.width
  let he : count=TilingCosts.bandCount N (ThinMatrixBackend.tileWidth L m) := congrArg (TilingCosts.bandCount N) shape.width_eq
  let ids : Vector (Fin count) count := Vector.ofFn id
  ⟨Vector.cast he (ids.map (Fin.cast he)),0,32*count+32⟩

theorem produce_get {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (N : ℕ)
    (i : Fin (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth L m))) : (produce shape N).value.get i=i := by
  simp only [produce,Vector.get_cast,Vector.get_map,Vector.get_ofFn,id_eq]
  apply Fin.ext
  rfl

theorem produce_bits {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (N : ℕ) : (produce shape N).bitSteps=0 := rfl

theorem produce_control {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (N : ℕ) :
    (produce shape N).control=32*TilingCosts.bandCount N (ThinMatrixBackend.tileWidth L m)+32 := by
  simp only [produce,shape.width_eq]

#print axioms produce_get
#print axioms produce_bits
#print axioms produce_control
end ThinMatrix.RetainedBandIndices
