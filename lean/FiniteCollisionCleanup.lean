import Mathlib

set_option autoImplicit false

/-! A finite, executable conservative cleanup. It removes every vertex-label
triple incident to a collision in the original candidate set. No isolated
copies or survival bound are supplied as assumptions. -/
namespace ThinMatrix.FiniteCollisionCleanup
variable {W X Y Z : Type*} [DecidableEq W] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def Shares (x : W → X) (y : W → Y) (z : W → Z) (a b : W) : Prop :=
  x a=x b ∨ y a=y b ∨ z a=z b
instance (x : W → X) (y : W → Y) (z : W → Z) (a b : W) : Decidable (Shares x y z a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def collisions (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z) : Finset (W×W) :=
  (E.product E).filter (fun p => p.1≠p.2 ∧ Shares x y z p.1 p.2)
def removed (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z) : Finset W :=
  (collisions E x y z).image Prod.fst
def keep (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z) : Finset W :=
  E \ removed E x y z

theorem keep_subset (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z) : keep E x y z⊆E :=
  Finset.sdiff_subset

theorem removed_subset (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z) : removed E x y z⊆E := by
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1

theorem unique_neighbor (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z)
    (a b : W) (ha : a ∈ keep E x y z) (hb : b ∈ E) (hs : Shares x y z a b) : b=a := by
  have h := Finset.mem_sdiff.mp ha
  by_contra hn
  apply h.2
  apply Finset.mem_image.mpr
  refine ⟨(a,b),?_,rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h.1,hb⟩,Ne.symm hn,hs⟩

theorem no_cross (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z)
    (a b c t : W) (ha : a ∈ keep E x y z) (hb : b ∈ keep E x y z)
    (hc : c ∈ keep E x y z) (ht : t ∈ E)
    (hx : x t=x a) (hy : y t=y b) (hz : z t=z c) : a=b ∧ a=c := by
  have hta := unique_neighbor E x y z a t ha ht (Or.inl hx.symm)
  have htb := unique_neighbor E x y z b t hb ht (Or.inr (Or.inl hy.symm))
  have htc := unique_neighbor E x y z c t hc ht (Or.inr (Or.inr hz.symm))
  exact ⟨hta.symm.trans htb,hta.symm.trans htc⟩

theorem retained_card (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z) :
    E.card≤(keep E x y z).card+(collisions E x y z).card := by
  have hs := removed_subset E x y z
  have hc := Finset.card_image_le (s:=collisions E x y z) (f:=Prod.fst)
  have hd := Finset.card_sdiff_add_card_eq_card hs
  change (removed E x y z).card≤_ at hc
  unfold keep
  omega

theorem collision_budget (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z) :
    (collisions E x y z).card≤E.card*E.card := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_product _ _)

#print axioms keep_subset
#print axioms removed_subset
#print axioms unique_neighbor
#print axioms no_cross
#print axioms retained_card
#print axioms collision_budget
end ThinMatrix.FiniteCollisionCleanup
