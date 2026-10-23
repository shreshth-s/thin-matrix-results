import FiniteDirectSum
import FiniteMatrixTensor

set_option autoImplicit false

namespace ThinMatrix.FiniteDependentCopies
open FiniteTrilinear FiniteDirectSum
variable {S T A B C R : Type*} [DecidableEq S] [DecidableEq T]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [CommRing R]
  (U V W : S → Type*) [∀ s,DecidableEq (U s)] [∀ s,DecidableEq (V s)] [∀ s,DecidableEq (W s)]

def direct : Tensor (Σ s,U s×V s) (Σ s,V s×W s) (Σ s,W s×U s) R :=
  fun x y z => if h : x.1=y.1 ∧ x.1=z.1 then
    FiniteMatrixTensor.coeff (U x.1) (V x.1) (W x.1) R x.2
      (h.1.symm ▸ y.2) (h.2.symm ▸ z.2) else 0

def left (e : T ≃ S) (a : ∀ s,A ≃ U s) (b : ∀ s,B ≃ V s)
    (x : T×(A×B)) : Σ s,U s×V s := ⟨e x.1,(a _ x.2.1,b _ x.2.2)⟩
def middle (e : T ≃ S) (b : ∀ s,B ≃ V s) (c : ∀ s,C ≃ W s)
    (y : T×(B×C)) : Σ s,V s×W s := ⟨e y.1,(b _ y.2.1,c _ y.2.2)⟩
def right (e : T ≃ S) (c : ∀ s,C ≃ W s) (a : ∀ s,A ≃ U s)
    (z : T×(C×A)) : Σ s,W s×U s := ⟨e z.1,(c _ z.2.1,a _ z.2.2)⟩

theorem uniform (e : T ≃ S) (a : ∀ s,A ≃ U s) (b : ∀ s,B ≃ V s) (c : ∀ s,C ≃ W s) :
    restrict (direct U V W) (left U V e a b) (middle V W e b c) (right U W e c a)=
      diagonal T (FiniteMatrixTensor.coeff A B C R) := by
  funext x y z
  obtain ⟨i,x⟩ := x;obtain ⟨j,y⟩ := y;obtain ⟨k,z⟩ := z
  by_cases h : i=j ∧ i=k
  · obtain ⟨rfl,rfl⟩ := h
    simp [restrict,left,middle,right,direct,diagonal,FiniteMatrixTensor.coeff]
  · have hne : ¬(e i=e j ∧ e i=e k) := by simpa only [Equiv.apply_eq_iff_eq] using h
    simp only [restrict,left,middle,right,direct,hne,↓reduceDIte,diagonal,h,ite_false]

#print axioms uniform
end ThinMatrix.FiniteDependentCopies
