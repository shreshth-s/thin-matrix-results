import Mathlib

set_option autoImplicit false

namespace ThinMatrix.FiniteHistogram
open scoped BigOperators
variable {I A : Type*} [Fintype I] [DecidableEq A]

def hist (f : I → A) (a : A) : ℕ := Fintype.card {i // f i=a}

theorem hist_comp (f : I → A) (e : Equiv.Perm I) (a : A) : hist (f ∘ e) a=hist f a := by
  exact Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

noncomputable def matching (f g : I → A) (h : ∀ a,hist f a=hist g a) : Equiv.Perm I :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fun a => Fintype.equivOfCardEq (h a))).trans (Equiv.sigmaFiberEquiv g))

theorem matching_spec (f g : I → A) (h : ∀ a,hist f a=hist g a) (i : I) :
    g (matching f g h i)=f i := by
  exact (Fintype.equivOfCardEq (h (f i)) ⟨i,rfl⟩).property

theorem exists_perm (f g : I → A) (h : ∀ a,hist f a=hist g a) :
    ∃ e : Equiv.Perm I,f ∘ e=g := by
  refine ⟨matching g f (fun a => (h a).symm),?_⟩
  funext i
  exact matching_spec g f (fun a => (h a).symm) i

#print axioms matching
#print axioms hist_comp
#print axioms matching_spec
#print axioms exists_perm
end ThinMatrix.FiniteHistogram
