import FiniteBilinearSubstitution
import PolynomialDegeneration

set_option autoImplicit false

/-! A constructive equal-copy recursion. Starting from r separated terms
for t simultaneous copies, level k uses exactly t*ceil(r/t)^k terms.
This is an exact finite coefficient identity, before any asymptotic or bit
complexity claim. The last batch is padded through the proved slot injection. -/
namespace ThinMatrix.EqualCopyRecursion
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum FiniteBilinearSubstitution PolynomialDegeneration
variable {I J K R : Type*} [CommRing R] {r t : ℕ}

def Budget (r t : ℕ) : ℕ → Type
  | 0 => Fin t
  | k+1 => Fin ((r+t-1)/t) × Budget r t k

instance budgetFintype (r t k : ℕ) : Fintype (Budget r t k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype (Fin t))
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin ((r+t-1)/t) × Budget r t k))

theorem budget_card (r t k : ℕ) : Fintype.card (Budget r t k)=t*((r+t-1)/t)^k := by
  induction k with
  | zero =>
    change Fintype.card (Fin t)=_
    rw [Fintype.card_fin,pow_zero,mul_one]
  | succ k ih =>
    change Fintype.card (Fin ((r+t-1)/t) × Budget r t k)=_
    rw [Fintype.card_prod,Fintype.card_fin,ih,pow_succ]
    ring

def unnest {A B : Type*} (x : Fin t×(A×B)) : (Fin t×A)×B := ((x.1,x.2.1),x.2.2)

def terms (ht : 0<t) (a : Fin r → Term (Fin t×I) (Fin t×J) (Fin t×K) R) :
    (k : ℕ) → Budget r t k →
      Term (Fin t×PowerIndex I k) (Fin t×PowerIndex J k) (Fin t×PowerIndex K k) R
  | 0 => fun (h : Fin t) =>
      ⟨fun x => if h=x.1 then 1 else 0,
       fun y => if h=y.1 then 1 else 0,
       fun z => if h=z.1 then 1 else 0⟩
  | k+1 => fun h =>
      (substitute a (batchTerm (slot r t ht) (terms ht a k)) h).restrict unnest unnest unnest

theorem terms_total (ht : 0<t)
    (u : Tensor I J K R) (a : Fin r → Term (Fin t×I) (Fin t×J) (Fin t×K) R)
    (ha : total a=diagonal (Fin t) u) (k : ℕ) :
    total (terms ht a k)=diagonal (Fin t) (tensorPower u k) := by
  induction k with
  | zero =>
    funext x y z
    change (∑ h : Fin t, (if h=x.1 then (1:R) else 0)*
      (if h=y.1 then 1 else 0)*(if h=z.1 then 1 else 0))=
        if x.1=y.1 ∧ x.1=z.1 then 1 else 0
    simp only [ite_and,ite_mul,mul_ite,one_mul,zero_mul,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    split_ifs <;> simp_all
  | succ k ih =>
    change total (fun h =>
      (substitute a (batchTerm (slot r t ht) (terms ht a k)) h).restrict unnest unnest unnest)=_
    rw [total_restrict,total_substitute a _ _
      (batch_total _ (slot_injective r t ht) _ _ ih),ha]
    funext x y z
    simp only [restrict,unnest,diagonal,tensorPower,product]
    split_ifs <;> simp

/-- Restricting to one actual copy produces a single tensor power. -/
def single (ht : 0<t) (a : Fin r → Term (Fin t×I) (Fin t×J) (Fin t×K) R)
    (k : ℕ) (h : Budget r t k) :
    Term (PowerIndex I k) (PowerIndex J k) (PowerIndex K k) R :=
  (terms ht a k h).restrict (fun x => (⟨0,ht⟩,x))
    (fun y => (⟨0,ht⟩,y)) (fun z => (⟨0,ht⟩,z))

theorem single_total (ht : 0<t)
    (u : Tensor I J K R) (a : Fin r → Term (Fin t×I) (Fin t×J) (Fin t×K) R)
    (ha : total a=diagonal (Fin t) u) (k : ℕ) :
    total (single ht a k)=tensorPower u k := by
  unfold single
  rw [total_restrict,terms_total ht u a ha]
  rfl

#print axioms budget_card
#print axioms terms_total
#print axioms single_total
end ThinMatrix.EqualCopyRecursion
