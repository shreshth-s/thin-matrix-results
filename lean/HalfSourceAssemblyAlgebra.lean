import HalfSourceRawCosts

set_option autoImplicit false
namespace ThinMatrix.HalfSourceAssemblyAlgebra

/-- Scalar-only final assembly keeps the already bounded source ledgers
and their polynomial price opaque during normalization. -/
theorem sum_seven (cap main spine B F v : ℝ)
    (hcap : cap≤B*F*v) (hmain : main≤B*(3*F*v+F*v+F*v))
    (hspine : spine≤B*F*v) (hn : 0≤B*F*v) :
    cap+main+spine≤8*F*B*v := by
  nlinarith only[hcap,hmain,hspine,hn]

#print axioms sum_seven
end ThinMatrix.HalfSourceAssemblyAlgebra
