import CWPolynomialCertificate
import IntegerCoefficientExtraction

set_option autoImplicit false

/-! Computable scalar tensor-power term data. The term index is a nested
finite product, avoiding noncomputable enumerations or a supplied rank oracle. -/
namespace ThinMatrix.CWPowerSpecialization
open scoped BigOperators
open Polynomial FiniteTrilinear PolynomialDegeneration CWPolynomialCertificate
variable {R I J K S : Type*} [CommRing R]

def powerTerms (a : S → Term I J K R) : (n : ℕ) →
    PowerIndex S n → Term (PowerIndex I n) (PowerIndex J n) (PowerIndex K n) R
  | 0 => fun _ => ⟨fun _ => 1,fun _ => 1,fun _ => 1⟩
  | n+1 => fun s => (a s.1).product (powerTerms a n s.2)

theorem powerTerms_total [Fintype S] (a : S → Term I J K R) (n : ℕ) :
    total (powerTerms a n)=tensorPower (total a) n := by
  induction n with
  | zero => funext i j k;simp [total,powerTerms,Term.tensor,tensorPower,PowerIndex]
  | succ n ih =>
      calc
        _ = total (fun s : S×PowerIndex S n => (a s.1).product (powerTerms a n s.2)) := by
          funext i j k
          exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun s => rfl)
        _ = _ := by rw [total_product,ih];rfl

theorem powerTerms_map {A : Type*} [CommRing A] (f : R →+* A) (a : S → Term I J K R)
    (n : ℕ) (s : PowerIndex S n) :
    (powerTerms a n s).map f=powerTerms (fun x => (a x).map f) n s := by
  induction n with
  | zero => simp [powerTerms,Term.map]
  | succ n ih =>
      calc
        _ = ((a s.1).map f).product ((powerTerms a n s.2).map f) := by
          simp only [powerTerms,Term.product,Term.map,map_mul]
          rfl
        _ = _ := by rw [ih];rfl

abbrev Index (n : ℕ) := PowerIndex (Axis 16) n
abbrev TermIndex (n : ℕ) := PowerIndex (Fin 18) n

def atInteger (n : ℕ) (t : ℤ) : TermIndex n → Term (Index n) (Index n) (Index n) ℤ :=
  powerTerms (termsAt 16 t) n

noncomputable def family (n : ℕ) : Tensor (Index n) (Index n) (Index n) ℤ[X] :=
  total (powerTerms (terms (R:=ℤ) 16) n)

theorem atInteger_eval (n : ℕ) (t : ℤ) :
    total (atInteger n t)=fun i j k => (family n i j k).eval t := by
  have h (s : TermIndex n) :
      (powerTerms (terms (R:=ℤ) 16) n s).map (evalRingHom t)=atInteger n t s := by
    rw [powerTerms_map]
    simp only [terms_specialize,atInteger]
  simpa only [h,family,coe_evalRingHom] using total_map (evalRingHom t) (powerTerms (terms (R:=ℤ) 16) n)

theorem family_bounds (n : ℕ) (i j k : Index n) :
    (∀ a,a<3*n → (family n i j k).coeff a=0) ∧
    (family n i j k).coeff (3*n)=tensorPower (target (R:=ℤ) 16) n i j k ∧
    (family n i j k).natDegree≤10*n := by
  simp only [family,powerTerms_total]
  induction n with
  | zero => simp [tensorPower]
  | succ n ih =>
      have ht := ih i.2 j.2 k.2
      constructor
      · intro a ha
        exact mul_below _ _ 3 (3*n) (coefficient_low 16 i.1 j.1 k.1) ht.1 a (by omega)
      constructor
      · change Polynomial.coeff (_ * _ : ℤ[X]) (3*(n+1))=_
        rw [show 3*(n+1)=3+3*n by omega,mul_leading _ _ 3 (3*n)
          (coefficient_low 16 i.1 j.1 k.1) ht.1,coefficient_target,ht.2.1]
        rfl
      · exact natDegree_mul_le.trans ((Nat.add_le_add (degree_bound 16 i.1 j.1 k.1) ht.2.2).trans_eq (by omega))

#print axioms powerTerms_total
#print axioms powerTerms_map
#print axioms atInteger_eval
#print axioms family_bounds
end ThinMatrix.CWPowerSpecialization
