import FiniteMatrixPowers

set_option autoImplicit false

namespace ThinMatrix.MatrixPowerReindex
open scoped BigOperators
open FiniteTrilinear PolynomialDegeneration FiniteMatrixPowers
variable {A B C : Type}

def unpair : (k : ℕ) → PowerIndex (A×B) k → PowerIndex A k×PowerIndex B k
  | 0,_ => (PUnit.unit,PUnit.unit)
  | k+1,x => let tail := unpair k x.2; ((x.1.1,tail.1),(x.1.2,tail.2))

theorem unpair_pair (k : ℕ) (x : PowerIndex A k×PowerIndex B k) :
    unpair k (pair k x)=x := by
  induction k with
  | zero =>
    change PUnit×PUnit at x
    exact Subsingleton.elim (α:=PUnit×PUnit) _ _
  | succ k ih =>
    simp only [unpair,pair,ih]
    cases x with
    | mk x y => cases x;cases y;rfl

theorem pair_unpair (k : ℕ) (x : PowerIndex (A×B) k) : pair k (unpair k x)=x := by
  induction k with
  | zero => exact Subsingleton.elim (α:=PUnit) _ _
  | succ k ih =>
    change (x.1,pair k (unpair k x.2))=x
    rw [ih]
    exact Prod.eta x

def pairEquiv (k : ℕ) : (PowerIndex A k×PowerIndex B k) ≃ PowerIndex (A×B) k :=
  ⟨pair k,unpair k,unpair_pair k,pair_unpair k⟩

theorem bilinear_matrix [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {R : Type} [CommRing R] (k : ℕ)
    (x : PowerIndex A k×PowerIndex B k → R)
    (y : PowerIndex B k×PowerIndex C k → R) (z : PowerIndex C k×PowerIndex A k) :
    bilinear (tensorPower (FiniteMatrixTensor.coeff A B C R) k)
      (fun p => x (unpair k p)) (fun q => y (unpair k q)) (pair k z)=
      ∑ b : PowerIndex B k,x (z.2,b)*y (b,z.1) := by
  rw [←FiniteMatrixTensor.multiply x y z]
  unfold bilinear
  rw [←(pairEquiv (A:=A) (B:=B) k).sum_comp]
  apply Finset.sum_congr rfl;intro p _
  rw [←(pairEquiv (A:=B) (B:=C) k).sum_comp]
  apply Finset.sum_congr rfl;intro q _
  simp only [pairEquiv,Equiv.coe_fn_mk,unpair_pair,tensor_matrix]

#print axioms unpair_pair
#print axioms pair_unpair
#print axioms bilinear_matrix
end ThinMatrix.MatrixPowerReindex
