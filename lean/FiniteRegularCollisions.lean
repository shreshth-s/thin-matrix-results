import FiniteCollisionCleanup

set_option autoImplicit false
namespace ThinMatrix.FiniteRegularCollisions
open scoped BigOperators
open FiniteCollisionCleanup
variable {W X Y Z : Type*} [DecidableEq W] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def keyPairs (E : Finset W) (f : W → X) : Finset (W×W) :=
  (E.product E).filter (fun p => p.1≠p.2 ∧ f p.1=f p.2)

theorem keyPairs_card (E : Finset W) (f : W → X) (D : ℕ)
    (h : ∀ u ∈ E,(E.filter (fun v => f v=f u)).card=D) :
    (keyPairs E f).card=E.card*(D-1) := by
  calc
    _ = ∑ u ∈ E,∑ v ∈ E,if u≠v ∧ f u=f v then 1 else 0 := by
      simp only [keyPairs,Finset.card_filter]
      exact Finset.sum_product _ _ _
    _ = ∑ _u ∈ E,(D-1) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.card_filter]
      have he : E.filter (fun v => u≠v ∧ f u=f v)=(E.filter (fun v => f v=f u)).erase u := by
        ext v
        simp only [Finset.mem_filter,Finset.mem_erase]
        constructor
        · rintro ⟨hv,hn,hf⟩;exact ⟨Ne.symm hn,hv,hf.symm⟩
        · rintro ⟨hn,hv,hf⟩;exact ⟨hv,Ne.symm hn,hf.symm⟩
      have huF : u ∈ E.filter (fun v => f v=f u) := Finset.mem_filter.mpr ⟨hu,rfl⟩
      rw [he,Finset.card_erase_of_mem huF,h u hu]
    _ = _ := by simp

theorem keyPairs_disjoint (E : Finset W) (f : W → X) (g : W → Y)
    (h : Function.Injective (fun u => (f u,g u))) : Disjoint (keyPairs E f) (keyPairs E g) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp := (Finset.mem_filter.mp hp).2
  have hq := (Finset.mem_filter.mp hq).2
  exact hp.1 (h (Prod.ext hp.2 hq.2))

theorem collisions_card (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z)
    (hxy : Function.Injective (fun u => (x u,y u)))
    (hxz : Function.Injective (fun u => (x u,z u)))
    (hyz : Function.Injective (fun u => (y u,z u))) :
    (collisions E x y z).card=(keyPairs E x).card+(keyPairs E y).card+(keyPairs E z).card := by
  have he : collisions E x y z=(keyPairs E x ∪ keyPairs E y) ∪ keyPairs E z := by
    ext p
    simp only [collisions,keyPairs,Finset.mem_filter,Finset.mem_union,Shares]
    tauto
  rw [he,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
    ⟨keyPairs_disjoint E x z hxz,keyPairs_disjoint E y z hyz⟩),
    Finset.card_union_of_disjoint (keyPairs_disjoint E x y hxy)]

theorem regular_collisions_card (E : Finset W) (x : W → X) (y : W → Y) (z : W → Z)
    (hxy : Function.Injective (fun u => (x u,y u)))
    (hxz : Function.Injective (fun u => (x u,z u)))
    (hyz : Function.Injective (fun u => (y u,z u)))
    (Dx Dy Dz : ℕ) (hDx : 0<Dx) (hDy : 0<Dy) (hDz : 0<Dz)
    (hx : ∀ u ∈ E,(E.filter (fun v => x v=x u)).card=Dx)
    (hy : ∀ u ∈ E,(E.filter (fun v => y v=y u)).card=Dy)
    (hz : ∀ u ∈ E,(E.filter (fun v => z v=z u)).card=Dz) :
    (collisions E x y z).card=E.card*(Dx+Dy+Dz-3) := by
  rw [collisions_card E x y z hxy hxz hyz,keyPairs_card E x Dx hx,
    keyPairs_card E y Dy hy,keyPairs_card E z Dz hz,← Nat.mul_add,← Nat.mul_add]
  congr 1
  omega

#print axioms keyPairs_card
#print axioms keyPairs_disjoint
#print axioms collisions_card
#print axioms regular_collisions_card
end ThinMatrix.FiniteRegularCollisions
