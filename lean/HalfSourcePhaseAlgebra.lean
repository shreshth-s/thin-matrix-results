import Mathlib.Tactic

/-! Scalar polynomial identities for actual phase-cost aggregation. -/
namespace ThinMatrix.HalfSourcePhaseAlgebra
set_option autoImplicit false
set_option maxHeartbeats 100000

theorem source_target (C H l F : ℝ) :
    8*C*H^17*l^17*F + 10^15*(H*l)^17*(3*F) =
      ((8*C+3*10^15)*H^17)*l^17*F := by
  rw[mul_pow]
  ring

#print axioms source_target
end ThinMatrix.HalfSourcePhaseAlgebra
