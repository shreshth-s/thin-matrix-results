import FiniteTrilinear

set_option autoImplicit false

/-! Homogeneous direct sums, with explicit coefficients. Enlarging a batch
uses an injection into a rectangular grid of slots; unused slots are zero.
The construction retains every batch and does not divide a rank by fiat. -/
namespace ThinMatrix.FiniteDirectSum
open scoped BigOperators
open FiniteTrilinear

variable {S T G H I J K R : Type*} [CommRing R]
  [DecidableEq S] [DecidableEq T] [DecidableEq G]

def diagonal (S : Type*) [DecidableEq S] (u : Tensor I J K R) :
    Tensor (S×I) (S×J) (S×K) R :=
  fun x y z => if x.1=y.1 ∧ x.1=z.1 then u x.2 y.2 z.2 else 0

def batchTerm (e : S → G×T) (a : H → Term (T×I) (T×J) (T×K) R)
    (gh : G×H) : Term (S×I) (S×J) (S×K) R :=
  ⟨fun x => if gh.1=(e x.1).1 then (a gh.2).left ((e x.1).2,x.2) else 0,
   fun y => if gh.1=(e y.1).1 then (a gh.2).middle ((e y.1).2,y.2) else 0,
   fun z => if gh.1=(e z.1).1 then (a gh.2).right ((e z.1).2,z.2) else 0⟩

theorem batch_total [Fintype G] [Fintype H]
    (e : S → G×T) (he : Function.Injective e)
    (u : Tensor I J K R) (a : H → Term (T×I) (T×J) (T×K) R)
    (ha : total a=diagonal T u) : total (batchTerm e a)=diagonal S u := by
  funext x y z
  simp only [total,Fintype.sum_prod_type,batchTerm,Term.tensor]
  by_cases hy : (e x.1).1=(e y.1).1
  · by_cases hz : (e x.1).1=(e z.1).1
    · simp only [←hy,←hz]
      simp only [ite_mul,mul_ite,zero_mul,mul_zero]
      have same (p : Prop) [Decidable p] (v : R) :
          (if p then if p then if p then v else 0 else 0 else 0)=(if p then v else 0) := by
        by_cases h : p <;> simp [h]
      simp only [same,Finset.sum_ite_irrel,Finset.sum_const_zero,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      have h := congrFun (congrFun (congrFun ha ((e x.1).2,x.2))
        ((e y.1).2,y.2)) ((e z.1).2,z.2)
      change total a ((e x.1).2,x.2) ((e y.1).2,y.2) ((e z.1).2,z.2)=_
      rw [h]
      have heq : ((e x.1).2=(e y.1).2 ∧ (e x.1).2=(e z.1).2) ↔
          (x.1=y.1 ∧ x.1=z.1) := by
        constructor
        · rintro ⟨h₁,h₂⟩
          exact ⟨he (Prod.ext hy h₁),he (Prod.ext hz h₂)⟩
        · rintro ⟨h₁,h₂⟩
          exact ⟨congrArg (fun s => (e s).2) h₁,congrArg (fun s => (e s).2) h₂⟩
      simp only [diagonal,heq]
    · have hne : x.1≠z.1 := fun h => hz (congrArg (fun s => (e s).1) h)
      simp only [diagonal,hne,and_false,ite_false]
      apply Finset.sum_eq_zero
      intro g _
      apply Finset.sum_eq_zero
      intro h _
      by_cases hx : g=(e x.1).1
      · have hgz : g≠(e z.1).1 := by simpa [hx] using hz
        simp [hx,hz]
      · simp [hx]
  · have hne : x.1≠y.1 := fun h => hy (congrArg (fun s => (e s).1) h)
    simp only [diagonal,hne,false_and,ite_false]
    apply Finset.sum_eq_zero
    intro g _
    apply Finset.sum_eq_zero
    intro h _
    by_cases hx : g=(e x.1).1
    · have hgy : g≠(e y.1).1 := by simpa [hx] using hy
      simp [hx,hy]
    · simp [hx]

/-- Division/remainder routing into exactly ceil(r/t) batches. -/
def slot (r t : ℕ) (ht : 0<t) (s : Fin r) : Fin ((r+t-1)/t)×Fin t :=
  (⟨s.val/t,by
    have hrem := Nat.mod_lt (r+t-1) ht
    have hdiv := Nat.mod_add_div (r+t-1) t
    rw [Nat.mul_comm t] at hdiv
    have hs := s.isLt
    apply (Nat.div_lt_iff_lt_mul ht).2
    omega⟩,⟨s.val%t,Nat.mod_lt _ ht⟩)

theorem slot_injective (r t : ℕ) (ht : 0<t) : Function.Injective (slot r t ht) := by
  intro a b h
  have hd := congrArg (fun x => x.1.val) h
  have hm := congrArg (fun x => x.2.val) h
  simp only [slot] at hd hm
  apply Fin.ext
  have ha := Nat.mod_add_div a.val t
  have hb := Nat.mod_add_div b.val t
  rw [hd,hm] at ha
  omega

#print axioms batch_total
#print axioms slot_injective
end ThinMatrix.FiniteDirectSum
