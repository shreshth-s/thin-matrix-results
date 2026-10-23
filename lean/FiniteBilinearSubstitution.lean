import FiniteDirectSum

set_option autoImplicit false

/-! Substitution of a simultaneous bilinear algorithm into the scalar
products of another one. This is the finite batching step in the equal-copy
asymptotic-sum argument; all coefficients are given by explicit finite sums. -/
namespace ThinMatrix.FiniteBilinearSubstitution
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum
variable {S H I J K A B C R : Type*} [CommRing R] [Fintype S] [DecidableEq S]

def substitute (a : S → Term I J K R)
    (b : H → Term (S×A) (S×B) (S×C) R) (h : H) :
    Term (I×A) (J×B) (K×C) R :=
  ⟨fun x => ∑ s,(a s).left x.1*(b h).left (s,x.2),
   fun y => ∑ s,(a s).middle y.1*(b h).middle (s,y.2),
   fun z => ∑ s,(a s).right z.1*(b h).right (s,z.2)⟩

theorem total_substitute [Fintype H] (a : S → Term I J K R)
    (b : H → Term (S×A) (S×B) (S×C) R) (u : Tensor A B C R)
    (hb : total b=diagonal S u) :
    total (substitute a b)=product (total a) u := by
  funext x y z
  calc
    _ = ∑ h, ∑ v, ∑ t, ∑ s,
        (a s).left x.1*(a t).middle y.1*(a v).right z.1*
          ((b h).tensor (s,x.2) (t,y.2) (v,z.2)) := by
      simp only [total,substitute,Term.tensor,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro h _
      apply Finset.sum_congr rfl; intro v _
      apply Finset.sum_congr rfl; intro t _
      apply Finset.sum_congr rfl; intro s _
      ring
    _ = ∑ v, ∑ t, ∑ s,
        (a s).left x.1*(a t).middle y.1*(a v).right z.1*
          (total b (s,x.2) (t,y.2) (v,z.2)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro v _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro t _
      rw [Finset.sum_comm]
      simp only [total,Finset.mul_sum]
    _ = _ := by
      rw [hb]
      simp [diagonal,product,total,Term.tensor,ite_and,Finset.sum_mul]

#print axioms total_substitute
end ThinMatrix.FiniteBilinearSubstitution
