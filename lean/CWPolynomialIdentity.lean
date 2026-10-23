import Mathlib

set_option autoImplicit false

/-! Universal scalar expansion underlying the finite CW coefficient tensor.
The parameter t is an element of an arbitrary commutative ring. It is later
instantiated with the formal polynomial variable; it is not any tensor axis.
The identity is proved symbolically for every q, including q=0. -/
namespace ThinMatrix.CWPolynomialIdentity
open scoped BigOperators
variable {R : Type*} [CommRing R]

def cross (a b c x y z : R) : R := x*b*c+a*y*c+a*b*z
def pairs (a b c x y z : R) : R := x*y*c+x*b*z+a*y*z

theorem triple (a b c x y z t : R) :
    (a+t*x)*(b+t*y)*(c+t*z)=a*b*c+t*cross a b c x y z+t^2*pairs a b c x y z+t^3*(x*y*z) := by
  unfold cross pairs
  ring

def witness (q : ℕ) (a b c u v w t : R) (x y z : Fin q → R) : R :=
  t*(∑ i,(a+t*x i)*(b+t*y i)*(c+t*z i))-
    (a+t^2*(∑ i,x i))*(b+t^2*(∑ i,y i))*(c+t^2*(∑ i,z i))+
    (1-(q:R)*t)*(a+t^3*u)*(b+t^3*v)*(c+t^3*w)

def cw (q : ℕ) (a b c u v w : R) (x y z : Fin q → R) : R :=
  (∑ i,pairs a b c (x i) (y i) (z i))+cross a b c u v w

theorem sum_cross (q : ℕ) (a b c : R) (x y z : Fin q → R) :
    (∑ i,cross a b c (x i) (y i) (z i))=cross a b c (∑ i,x i) (∑ i,y i) (∑ i,z i) := by
  simp [cross,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]

theorem expansion (q : ℕ) (a b c u v w t : R) (x y z : Fin q → R) :
    witness q a b c u v w t x y z =
      t^3*cw q a b c u v w x y z+
      t^4*((∑ i,x i*y i*z i)-pairs a b c (∑ i,x i) (∑ i,y i) (∑ i,z i)-(q:R)*cross a b c u v w)+
      t^6*(-((∑ i,x i)*(∑ i,y i)*(∑ i,z i))+pairs a b c u v w)-
      t^7*((q:R)*pairs a b c u v w)+t^9*(u*v*w)-t^10*((q:R)*(u*v*w)) := by
  have hs : (∑ i,(a+t*x i)*(b+t*y i)*(c+t*z i))=
      (q:R)*(a*b*c)+t*cross a b c (∑ i,x i) (∑ i,y i) (∑ i,z i)+
      t^2*(∑ i,pairs a b c (x i) (y i) (z i))+t^3*(∑ i,x i*y i*z i) := by
    simp_rw [triple]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,sum_cross]
    ring
  unfold witness cw
  rw [hs,triple]
  unfold cross pairs
  ring

#print axioms triple
#print axioms sum_cross
#print axioms expansion
end ThinMatrix.CWPolynomialIdentity
