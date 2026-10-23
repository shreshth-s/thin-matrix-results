import CWWeightedFibers

set_option autoImplicit false

namespace ThinMatrix.CWHashFibers
open PolynomialDegeneration CWBlockWords CWHashSeparation
variable {F : Type*} [Field F] [DecidableEq F]

abbrev Sample (F : Type*) (n : ℕ) := F×F×PowerIndex F n
def Event (n : ℕ) (x y z : Colors n) (c : F) (r : Sample F n) : Prop :=
  hx n r.1 r.2.2 x=c ∧ hy n r.1 r.2.1 r.2.2 y=c ∧ hz n r.1 r.2.1 r.2.2 z=c
instance (n : ℕ) (x y z : Colors n) (c : F) (r : Sample F n) : Decidable (Event n x y z c r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

omit [DecidableEq F] in
theorem event_iff_xy (h2 : (2:F)≠0) (n : ℕ) (x y z : Colors n)
    (hc : Compatible n x y z) (c : F) (r : Sample F n) :
    Event n x y z c r ↔ hx n r.1 r.2.2 x=c ∧ hy n r.1 r.2.1 r.2.2 y=c := by
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · intro h
    refine ⟨h.1,h.2,?_⟩
    have he := hash_relation h2 n r.1 r.2.1 r.2.2 x y z hc
    rw [h.1,h.2] at he
    apply mul_left_cancel₀ h2
    linear_combination -he

/-- Both offsets are forced; an arbitrary condition on the weights is retained. -/
def restrictedEquiv (h2 : (2:F)≠0) (n : ℕ) (x y z : Colors n)
    (hc : Compatible n x y z) (c : F) (P : PowerIndex F n → Prop) :
    {r : Sample F n // Event n x y z c r ∧ P r.2.2} ≃ {w : PowerIndex F n // P w} where
  toFun r := ⟨r.val.2.2,r.property.2⟩
  invFun w := ⟨(c-weighted n w.val x,weighted n w.val x-weighted n w.val y,w.val),
    ⟨(event_iff_xy h2 n x y z hc c _).mpr ⟨by dsimp [hx];ring,by dsimp [hy];ring⟩,w.property⟩⟩
  left_inv r := by
    apply Subtype.ext
    apply Prod.ext
    · have h := r.property.1.1
      dsimp [hx] at h ⊢
      linear_combination -h
    · apply Prod.ext
      · have h := r.property.1.1
        have h' := r.property.1.2.1
        dsimp [hx,hy] at h h' ⊢
        linear_combination h-h'
      · rfl
  right_inv _ := rfl

omit [Field F] [DecidableEq F] in
theorem sample_card [Fintype F] (n : ℕ) :
    Fintype.card (Sample F n)=(Fintype.card F)^(n+2) := by
  simp only [Sample,Fintype.card_prod,powerIndex_card,pow_add,pow_two]
  ring

theorem event_card [Fintype F] (h2 : (2:F)≠0) (n : ℕ) (x y z : Colors n)
    (hc : Compatible n x y z) (c : F) :
    Fintype.card {r : Sample F n // Event n x y z c r}=(Fintype.card F)^n := by
  have h := Fintype.card_congr (restrictedEquiv h2 n x y z hc c (fun _ => True))
  simpa only [and_true,Fintype.card_subtype_true,powerIndex_card] using h

#print axioms event_iff_xy
#print axioms sample_card
#print axioms event_card
end ThinMatrix.CWHashFibers
