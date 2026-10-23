import FiniteMatrixTensor
import PolynomialDegeneration

set_option autoImplicit false

namespace ThinMatrix.FiniteMatrixPowers
open FiniteTrilinear PolynomialDegeneration
variable {A B C R : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] [CommRing R]

instance powerDecidableEq (A : Type*) [DecidableEq A] (k : ℕ) : DecidableEq (PowerIndex A k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (A×PowerIndex A k))

def pair : (k : ℕ) → PowerIndex A k × PowerIndex B k → PowerIndex (A×B) k
  | 0,_ => PUnit.unit
  | k+1,x => ((x.1.1,x.2.1),pair k (x.1.2,x.2.2))

theorem tensor_matrix (k : ℕ) (x : PowerIndex A k × PowerIndex B k)
    (y : PowerIndex B k × PowerIndex C k) (z : PowerIndex C k × PowerIndex A k) :
    tensorPower (FiniteMatrixTensor.coeff A B C R) k (pair k x) (pair k y) (pair k z)=
      FiniteMatrixTensor.coeff (PowerIndex A k) (PowerIndex B k) (PowerIndex C k) R x y z := by
  induction k with
  | zero =>
    change PUnit×PUnit at x y z
    have hx : x=(PUnit.unit,PUnit.unit) := Subsingleton.elim _ _
    have hy : y=(PUnit.unit,PUnit.unit) := Subsingleton.elim _ _
    have hz : z=(PUnit.unit,PUnit.unit) := Subsingleton.elim _ _
    subst x;subst y;subst z
    simp [tensorPower,FiniteMatrixTensor.coeff]
  | succ k ih =>
    change FiniteMatrixTensor.coeff A B C R (x.1.1,x.2.1) (y.1.1,y.2.1) (z.1.1,z.2.1)*
      tensorPower (FiniteMatrixTensor.coeff A B C R) k (pair k (x.1.2,x.2.2))
        (pair k (y.1.2,y.2.2)) (pair k (z.1.2,z.2.2))=_
    rw [ih]
    exact FiniteMatrixTensor.product_coeff x y z

def rotate {I J K : Type*} (a : Term I J K R) : Term K I J R :=
  ⟨a.right,a.left,a.middle⟩

theorem total_rotate {I J K S : Type*} [Fintype S] (a : S → Term I J K R) :
    total (fun s => rotate (a s))=fun k i j => total a i j k := by
  funext k i j
  unfold total
  apply Finset.sum_congr rfl
  intro s _
  simp only [rotate,Term.tensor]
  ring

#print axioms tensor_matrix
#print axioms total_rotate
end ThinMatrix.FiniteMatrixPowers
