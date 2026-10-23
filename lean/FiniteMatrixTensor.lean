import FiniteTrilinear

set_option autoImplicit false

namespace ThinMatrix.FiniteMatrixTensor
open scoped BigOperators
open FiniteTrilinear
variable {A B C D E F R : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [DecidableEq D] [DecidableEq E] [DecidableEq F] [CommRing R]

/-- X=(row,inner), Y=(inner,column), Z=(column,row). -/
def coeff (A B C R : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] [CommRing R] :
    Tensor (A×B) (B×C) (C×A) R := fun x y z =>
  if x.1=z.2 ∧ x.2=y.1 ∧ y.2=z.1 then 1 else 0

theorem multiply [Fintype A] [Fintype B] [Fintype C]
    (x : A×B → R) (y : B×C → R) (z : C×A) :
    bilinear (coeff A B C R) x y z=∑ b : B,x (z.2,b)*y (b,z.1) := by
  classical
  simp [bilinear,coeff,Fintype.sum_prod_type,ite_and,ite_mul]

theorem product_coeff (x : (A×D)×(B×E)) (y : (B×E)×(C×F)) (z : (C×F)×(A×D)) :
    coeff A B C R (x.1.1,x.2.1) (y.1.1,y.2.1) (z.1.1,z.2.1)*
      coeff D E F R (x.1.2,x.2.2) (y.1.2,y.2.2) (z.1.2,z.2.2)=
    coeff (A×D) (B×E) (C×F) R x y z := by
  simp only [coeff,Prod.ext_iff,ite_mul,one_mul,zero_mul]
  split_ifs <;> simp_all

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
theorem axis_dimensions [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (A×B)=Fintype.card A*Fintype.card B ∧
    Fintype.card (B×C)=Fintype.card B*Fintype.card C ∧
    Fintype.card (C×A)=Fintype.card C*Fintype.card A := by simp

theorem cyclic (x : A×B) (y : B×C) (z : C×A) :
    coeff A B C R x y z=coeff C A B R z x y := by
  simp [coeff,and_comm,and_assoc,eq_comm]

#print axioms cyclic
#print axioms multiply
#print axioms product_coeff
#print axioms axis_dimensions
end ThinMatrix.FiniteMatrixTensor
