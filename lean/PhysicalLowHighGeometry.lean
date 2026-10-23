import PhysicalShiftedForms

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Common physical support for the retained LOW pencil and HIGH query. -/
namespace ThinMatrix.PhysicalLowHighGeometry
open PhysicalWordReindex PhysicalSupportProducts ResidualFamilyKeys
open CompleteThinProduct PhysicalShiftedForms HighBoxDP
open scoped BigOperators
variable {R : Type*} [CommRing R] {L m : ℕ}

theorem support_size (a : Mask L m) : (support a).card=m :=
  GoodMapEmbedding.goodSlots_size L m _ a.good

noncomputable def embedding (a b : Mask L m) : Fin (2*m) ↪o Fin (2*L) :=
  physicalEmbedding (support a) (support b) (support_size a) (support_size b)

theorem embedding_support (a b : Mask L m) : embeddedSupport (embedding a b)=physicalSupport (support a) (support b) :=
  physicalEmbedding_support _ _ _ _

theorem kernel (a b : Mask L m) (x y : SourceWord L) :
    GraphPhysicalLow.kernel (R:=R) a b x y=
      ∏ i, (Polynomial.C (privateKernel (lift (R:=R) true) (lift false) (embedding a b i) x y)+
        Polynomial.X*Polynomial.C (fullKernel (lift (R:=R) true) (lift false) (embedding a b i) x y)) := by
  have hs := Finset.prod_image (s:=Finset.univ)
    (f:=fun i => Polynomial.C (privateKernel (lift (R:=R) true) (lift false) i x y)+
      Polynomial.X*Polynomial.C (fullKernel (lift (R:=R) true) (lift false) i x y))
    (g:=embedding a b) (fun _ _ _ _ h => (embedding a b).injective h)
  rw [←hs]
  change _ = ∏ i∈embeddedSupport (embedding a b), _
  rw [embedding_support,prod_physical_support]
  unfold GraphPhysicalLow.kernel
  rw [prod_selected a (fun j => ShiftedLowChannelFormula.localPencil (R:=R) (x.1 j) (y.2 j)),
    prod_selected b (fun j => ShiftedLowChannelFormula.localPencil (R:=R) (y.1 j) (x.2 j))]
  simp only [private_left,private_right,full_left,full_right,ShiftedLowChannelFormula.localPencil]

theorem outside_left (a b : Mask L m) (outside : Vector (Fin 4) (2*L)) (w : SourceWord L) :
    ((PhysicalOrdinaryForms.ordinary a b false outside w : ℤ) : R)=
      ∏ i∈(embeddedSupport (embedding a b))ᶜ, lift (R:=R) true i (outside.get i).castSucc w := by
  rw [embedding_support,prod_physical_compl]
  simp only [PhysicalOrdinaryForms.ordinary,PhysicalOrdinaryForms.normalPosition,
    PhysicalOrdinaryForms.oppositePosition,Bool.false_eq_true,↓reduceIte,Int.cast_mul,Int.cast_prod,
    ordinary_left,ordinary_right]
  exact congrArg₂ (·*·)
    (prod_remaining a (fun j => (PhysicalOrdinaryForms.normal (outside.get (physicalLeft j)) (w.1 j) : R)))
    (prod_remaining b (fun j => (PhysicalOrdinaryForms.opposite (outside.get (physicalRight j)) (w.2 j) : R)))

theorem outside_right (a b : Mask L m) (outside : Vector (Fin 4) (2*L)) (w : SourceWord L) :
    ((PhysicalOrdinaryForms.ordinary b a true outside w : ℤ) : R)=
      ∏ i∈(embeddedSupport (embedding a b))ᶜ, lift (R:=R) false i (outside.get i).castSucc w := by
  rw [embedding_support,prod_physical_compl]
  simp only [PhysicalOrdinaryForms.ordinary,PhysicalOrdinaryForms.normalPosition,
    PhysicalOrdinaryForms.oppositePosition,Bool.false_eq_true,↓reduceIte,Int.cast_mul,Int.cast_prod,
    ordinary_left,ordinary_right,mul_comm]
  exact congrArg₂ (·*·)
    (prod_remaining b (fun j => (PhysicalOrdinaryForms.normal (outside.get (physicalRight j)) (w.1 j) : R)))
    (prod_remaining a (fun j => (PhysicalOrdinaryForms.opposite (outside.get (physicalLeft j)) (w.2 j) : R)))

#print axioms support_size
#print axioms embedding_support
#print axioms kernel
#print axioms outside_left
#print axioms outside_right
end ThinMatrix.PhysicalLowHighGeometry
