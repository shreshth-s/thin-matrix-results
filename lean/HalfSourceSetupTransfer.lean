import HalfSourceAssemblyAlgebra

set_option autoImplicit false
namespace ThinMatrix.HalfSourceSetupTransfer

theorem source (cost c P H l B v V : ℝ) (hc : 0≤c) (hP : 0≤P)
    (hbv : 0≤B*v) (hp : P≤H*l) (hv : B*v≤V)
    (hcost : cost≤8*c*P^17*B*v) :
    cost≤8*c*H^17*l^17*V := by
  have hpoly := pow_le_pow_left₀ hP hp 17
  have hHl : 0≤H*l := hP.trans hp
  calc
    cost≤8*c*P^17*B*v := hcost
    _ =(8*c*P^17)*(B*v) := by ring
    _ ≤(8*c*(H*l)^17)*V := mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) hv hbv (by positivity)
    _ =_ := by ring

#print axioms source
end ThinMatrix.HalfSourceSetupTransfer
