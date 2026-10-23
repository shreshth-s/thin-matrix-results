import PolynomialDegeneration
import CWPolynomialIdentity

set_option autoImplicit false

/-! An explicit polynomial degeneration of the big CW tensor. Axis labels are
`none` (0), `some (some i)` (private i+1), `some none` (terminal q+1).
The formal polynomial variable is independent of these three tensor axes.
There are q+2 separated terms over R[X], not q+2 exact terms for CW over R.
Coefficients below degree 3 vanish, degree 3 is CW, and degree is at most 10.
This is finite certificate data; no asymptotic rank theorem is assumed. -/
namespace ThinMatrix.CWPolynomialCertificate
open scoped BigOperators
open Polynomial FiniteTrilinear
variable {R : Type*} [CommRing R]

abbrev Axis (q : ℕ) := Option (Option (Fin q))
def origin {q : ℕ} : Axis q := none
def terminal {q : ℕ} : Axis q := some none
def privateLabel {q : ℕ} (i : Fin q) : Axis q := some (some i)

def basis {q : ℕ} (a i : Axis q) : R := if i=a then 1 else 0

theorem axis_card (q : ℕ) : Fintype.card (Axis q)=q+2 := by simp [Axis]

/-- Independent coefficient definition: q pairs in each orientation and
three terminal corner terms, with three distinct variable spaces. -/
def target (q : ℕ) : Tensor (Axis q) (Axis q) (Axis q) R := fun i j k =>
  (∑ a : Fin q, (basis (privateLabel a) i*basis (privateLabel a) j*basis origin k+
    basis (privateLabel a) i*basis origin j*basis (privateLabel a) k+
    basis origin i*basis (privateLabel a) j*basis (privateLabel a) k))+
  (basis terminal i*basis origin j*basis origin k+
    basis origin i*basis terminal j*basis origin k+
    basis origin i*basis origin j*basis terminal k)

def privateAt {q : ℕ} (a : Fin q) (t : R) (i : Axis q) : R :=
  basis origin i+t*basis (privateLabel a) i

def sumAt {q : ℕ} (t : R) (i : Axis q) : R :=
  basis origin i+t^2*(∑ a : Fin q,basis (privateLabel a) i)

def terminalAt {q : ℕ} (t : R) (i : Axis q) : R :=
  basis origin i+t^3*basis terminal i

def mainAt {q : ℕ} (a : Fin q) (t : R) : Term (Axis q) (Axis q) (Axis q) R :=
  ⟨fun i => t*privateAt a t i,privateAt a t,privateAt a t⟩

def negativeAt (q : ℕ) (t : R) : Term (Axis q) (Axis q) (Axis q) R :=
  ⟨fun i => -sumAt t i,sumAt t,sumAt t⟩

def terminalTermAt (q : ℕ) (t : R) : Term (Axis q) (Axis q) (Axis q) R :=
  ⟨fun i => (1-(q:R)*t)*terminalAt t i,terminalAt t,terminalAt t⟩

/-- Computable scalar term data, usable directly at rational interpolation nodes. -/
def termsAt (q : ℕ) (t : R) : Fin (q+2) → Term (Axis q) (Axis q) (Axis q) R :=
  Fin.addCases (fun a => mainAt a t)
    (Fin.cons (negativeAt q t) (Fin.cons (terminalTermAt q t) (fun i => Fin.elim0 i)))

/-- Mathlib polynomials serve as the semantic denotation of the scalar data. -/
noncomputable def terms (q : ℕ) : Fin (q+2) → Term (Axis q) (Axis q) (Axis q) R[X] :=
  termsAt q X

theorem basis_poly {q : ℕ} (a i : Axis q) : (basis a i : R[X])=C (basis a i : R) := by
  unfold basis
  split_ifs <;> simp

theorem total_formula (q : ℕ) (i j k : Axis q) :
    total (terms (R:=R) q) i j k = CWPolynomialIdentity.witness q
      (C (basis origin i)) (C (basis origin j)) (C (basis origin k))
      (C (basis terminal i)) (C (basis terminal j)) (C (basis terminal k)) X
      (fun a => C (basis (privateLabel a) i))
      (fun a => C (basis (privateLabel a) j))
      (fun a => C (basis (privateLabel a) k)) := by
  simp only [total,terms,termsAt,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
  simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.sum_univ_zero,add_zero]
  simp only [mainAt,negativeAt,terminalTermAt,Term.tensor,privateAt,sumAt,terminalAt,basis_poly,
    CWPolynomialIdentity.witness]
  rw [show (∑ a : Fin q, X*(C (basis origin i)+X*C (basis (privateLabel a) i))*
      (C (basis origin j)+X*C (basis (privateLabel a) j))*
      (C (basis origin k)+X*C (basis (privateLabel a) k))) =
    X*(∑ a : Fin q,(C (basis origin i)+X*C (basis (privateLabel a) i))*
      (C (basis origin j)+X*C (basis (privateLabel a) j))*
      (C (basis origin k)+X*C (basis (privateLabel a) k))) by
        simp only [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;ring]
  ring

/-- Scalar coefficient arrays for the error terms, derived by expansion. -/
def e4 (q : ℕ) (i j k : Axis q) : R :=
  (∑ a : Fin q,basis (privateLabel a) i*basis (privateLabel a) j*basis (privateLabel a) k)-
  CWPolynomialIdentity.pairs (basis origin i) (basis origin j) (basis origin k)
    (∑ a : Fin q,basis (privateLabel a) i) (∑ a : Fin q,basis (privateLabel a) j) (∑ a : Fin q,basis (privateLabel a) k)-
  (q:R)*CWPolynomialIdentity.cross (basis origin i) (basis origin j) (basis origin k)
    (basis terminal i) (basis terminal j) (basis terminal k)

def e6 (q : ℕ) (i j k : Axis q) : R :=
  -((∑ a : Fin q,basis (privateLabel a) i)*(∑ a : Fin q,basis (privateLabel a) j)*(∑ a : Fin q,basis (privateLabel a) k))+
  CWPolynomialIdentity.pairs (basis origin i) (basis origin j) (basis origin k)
    (basis terminal i) (basis terminal j) (basis terminal k)

def e7 (q : ℕ) (i j k : Axis q) : R :=
  -(q:R)*CWPolynomialIdentity.pairs (basis origin i) (basis origin j) (basis origin k)
    (basis terminal i) (basis terminal j) (basis terminal k)

def e9 (q : ℕ) (i j k : Axis q) : R := basis terminal i*basis terminal j*basis terminal k

def e10 (q : ℕ) (i j k : Axis q) : R := -(q:R)*e9 q i j k

theorem polynomial_expansion (q : ℕ) (i j k : Axis q) :
    total (terms (R:=R) q) i j k =
      C (target q i j k)*X^3+C (e4 q i j k)*X^4+C (e6 q i j k)*X^6+
      C (e7 q i j k)*X^7+C (e9 q i j k)*X^9+C (e10 q i j k)*X^10 := by
  rw [total_formula,CWPolynomialIdentity.expansion]
  simp only [target,e4,e6,e7,e9,e10,CWPolynomialIdentity.cw,CWPolynomialIdentity.pairs,
    CWPolynomialIdentity.cross,map_sum,map_add,map_sub,map_mul,map_neg,map_natCast]
  ring

theorem coefficient_low (q : ℕ) (i j k : Axis q) (n : ℕ) (hn : n<3) :
    (total (terms q) i j k : R[X]).coeff n=0 := by
  rw [polynomial_expansion]
  simp only [coeff_add,coeff_C_mul_X_pow]
  split_ifs <;> first | omega | simp

theorem coefficient_target (q : ℕ) (i j k : Axis q) :
    (total (terms q) i j k : R[X]).coeff 3=target q i j k := by
  rw [polynomial_expansion]
  simp

theorem degree_bound (q : ℕ) (i j k : Axis q) :
    (total (terms q) i j k : R[X]).natDegree≤10 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [polynomial_expansion]
  simp only [coeff_add,coeff_C_mul_X_pow]
  split_ifs <;> first | omega | simp

theorem basis_map {A : Type*} [CommRing A] (f : R →+* A) {q : ℕ} (a i : Axis q) :
    f (basis a i)= (basis a i : A) := by
  unfold basis
  split_ifs <;> simp

theorem termsAt_map {A : Type*} [CommRing A] (f : R →+* A) (q : ℕ) (t : R) (a : Fin (q+2)) :
    (termsAt q t a).map f=termsAt q (f t) a := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · simp only [termsAt,Fin.addCases_left,mainAt,Term.map]
    congr 1 <;> funext i <;> simp only [privateAt,map_add,map_mul,basis_map]
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [termsAt,Fin.addCases_right,Fin.cons_zero,negativeAt,Term.map]
      congr 1 <;> funext k <;> simp [sumAt,basis_map]
    · have hj : j=0 := Fin.eq_zero j
      subst j
      simp only [termsAt,Fin.addCases_right,Fin.cons_succ,Fin.cons_zero,terminalTermAt,Term.map]
      congr 1 <;> funext k <;> simp [terminalAt,basis_map]

theorem terms_specialize (q : ℕ) (t : R) (a : Fin (q+2)) :
    (terms (R:=R) q a).map (evalRingHom t)=termsAt q t a := by
  simpa [terms] using termsAt_map (evalRingHom t) q X a

/-- Every specialization has an explicit q+2-term decomposition. This is
not an exact q+2-term decomposition of the leading CW coefficient. -/
theorem specialized (q : ℕ) (t : R) :
    total (fun a => (terms q a).map (evalRingHom t))=
      fun i j k => (total (terms q) i j k).eval t :=
  total_map _ _

theorem specialized_computable (q : ℕ) (t : R) :
    total (termsAt q t)=fun i j k => (total (terms (R:=R) q) i j k).eval t := by
  simpa only [terms_specialize] using specialized q t

/-- Explicit data for the polynomial degeneration, over every commutative
ring. Specializing to Q below supplies characteristic-zero rational data. -/
noncomputable def certificate (q : ℕ) :
    PolynomialDegeneration.Certificate (target (R:=R) q) (q+2) 3 10 where
  terms := terms q
  below := coefficient_low q
  leading := coefficient_target q
  bounded := degree_bound q

/-- CW16 has a polynomial family with 18 separated terms, leading order 3
and degree at most 10. This states a degeneration, not exact tensor rank. -/
noncomputable def cw16 :
    PolynomialDegeneration.Certificate (target (R:=ℚ) 16) 18 3 10 := certificate 16

/-- A concrete family for every tensor power, including the scalar zeroth
power. The polynomial degree overhead is retained for later interpolation. -/
noncomputable def cw16Power (n : ℕ) :
    PolynomialDegeneration.Certificate
      (PolynomialDegeneration.tensorPower (target (R:=ℚ) 16) n)
      (18^n) (3*n) (10*n) := cw16.power n

theorem cw16Power_axis_card (n : ℕ) :
    Fintype.card (PolynomialDegeneration.PowerIndex (Axis 16) n)=18^n := by
  rw [PolynomialDegeneration.powerIndex_card,axis_card]

#print axioms certificate
#print axioms cw16
#print axioms cw16Power
#print axioms cw16Power_axis_card
#print axioms axis_card
#print axioms basis_poly
#print axioms total_formula
#print axioms polynomial_expansion
#print axioms coefficient_low
#print axioms coefficient_target
#print axioms degree_bound
#print axioms basis_map
#print axioms termsAt_map
#print axioms terms_specialize
#print axioms specialized
#print axioms specialized_computable
end ThinMatrix.CWPolynomialCertificate
