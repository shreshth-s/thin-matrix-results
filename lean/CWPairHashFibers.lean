import CWHashFibers
import CWWordCollisions

set_option autoImplicit false

namespace ThinMatrix.CWPairHashFibers
open PolynomialDegeneration CWBlockWords CWHashSeparation CWHashFibers CWWordCollisions
variable {F : Type*} [Field F]

abbrev WordEvent (n : ℕ) (u : Word n) (c : F) (r : Sample F n) :=
  Event n (wx n u) (wy n u) (wz n u) c r

theorem word_event_iff_xy (h2 : (2:F)≠0) (n : ℕ) (u : Word n) (c : F) (r : Sample F n) :
    WordEvent n u c r ↔ hx n r.1 r.2.2 (wx n u)=c ∧ hy n r.1 r.2.1 r.2.2 (wy n u)=c :=
  event_iff_xy h2 n _ _ _ (word_compatible n u) c r

theorem shared_x_iff (h2 : (2:F)≠0) (n : ℕ) (u v : Word n) (hX : wx n u=wx n v)
    (c : F) (r : Sample F n) :
    (WordEvent n u c r ∧ WordEvent n v c r) ↔
      WordEvent n u c r ∧ weighted n r.2.2 (wy n u)-weighted n r.2.2 (wy n v)=0 := by
  simp only [word_event_iff_xy h2]
  dsimp [hx,hy]
  rw [hX]
  constructor
  · intro h
    exact ⟨h.1,by linear_combination h.1.2-h.2.2⟩
  · rintro ⟨h,hd⟩
    exact ⟨h,⟨h.1,by linear_combination h.2-hd⟩⟩

theorem shared_y_iff (h2 : (2:F)≠0) (n : ℕ) (u v : Word n) (hY : wy n u=wy n v)
    (c : F) (r : Sample F n) :
    (WordEvent n u c r ∧ WordEvent n v c r) ↔
      WordEvent n u c r ∧ weighted n r.2.2 (wx n u)-weighted n r.2.2 (wx n v)=0 := by
  simp only [word_event_iff_xy h2]
  dsimp [hx,hy]
  rw [hY]
  constructor
  · intro h
    exact ⟨h.1,by linear_combination h.1.1-h.2.1⟩
  · rintro ⟨h,hd⟩
    exact ⟨h,⟨by linear_combination h.1-hd,h.2⟩⟩

theorem shared_z_iff (h2 : (2:F)≠0) (n : ℕ) (u v : Word n) (hZ : wz n u=wz n v)
    (c : F) (r : Sample F n) :
    (WordEvent n u c r ∧ WordEvent n v c r) ↔
      WordEvent n u c r ∧ weighted n r.2.2 (wx n u)-weighted n r.2.2 (wx n v)=0 := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    have hu := h.1.1
    have hv := h.2.1
    dsimp [hx] at hu hv
    linear_combination hu-hv
  · rintro ⟨h,hd⟩
    refine ⟨h,?_,?_,?_⟩
    · have hu := h.1
      dsimp [hx] at hu ⊢
      linear_combination hu-hd
    · have hvx : hx n r.1 r.2.2 (wx n v)=c := by
        have hu := h.1
        dsimp [hx] at hu ⊢
        linear_combination hu-hd
      have hvz : hz n r.1 r.2.1 r.2.2 (wz n v)=c := by rw [← hZ];exact h.2.2
      have he := hash_relation h2 n r.1 r.2.1 r.2.2 _ _ _ (word_compatible n v)
      rw [hvx,hvz] at he
      linear_combination he
    · rw [← hZ]
      exact h.2.2

section Counting
variable [DecidableEq F] [Fintype F]

theorem constrained_card (h2 : (2:F)≠0)
    (hinj : Function.Injective (fun a : Fin 3 => (a.val:F)))
    (n : ℕ) (u : Word n) (x y : Colors n) (hne : x≠y) (c : F) :
    Fintype.card {r : Sample F n // WordEvent n u c r ∧
      weighted n r.2.2 x-weighted n r.2.2 y=0}=(Fintype.card F)^(n-1) := by
  rw [Fintype.card_congr (restrictedEquiv h2 n _ _ _ (word_compatible n u) c
    (fun w => weighted n w x-weighted n w y=0))]
  exact CWWeightedFibers.card hinj n x y hne 0

theorem pair_card (h2 : (2:F)≠0)
    (hinj : Function.Injective (fun a : Fin 3 => (a.val:F)))
    (n : ℕ) (u v : Word n) (hne : u≠v)
    (hs : wx n u=wx n v ∨ wy n u=wy n v ∨ wz n u=wz n v) (c : F) :
    Fintype.card {r : Sample F n // WordEvent n u c r ∧ WordEvent n v c r}=
      (Fintype.card F)^(n-1) := by
  rcases hs with hx | hy | hz
  · have hd : wy n u≠wy n v := fun he => hne (xy_injective n (Prod.ext hx he))
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (shared_x_iff h2 n u v hx c))]
    exact constrained_card h2 hinj n u _ _ hd c
  · have hd : wx n u≠wx n v := fun he => hne (xy_injective n (Prod.ext he hy))
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (shared_y_iff h2 n u v hy c))]
    exact constrained_card h2 hinj n u _ _ hd c
  · have hd : wx n u≠wx n v := fun he => hne (xz_injective n (Prod.ext he hz))
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (shared_z_iff h2 n u v hz c))]
    exact constrained_card h2 hinj n u _ _ hd c
end Counting

#print axioms word_event_iff_xy
#print axioms shared_x_iff
#print axioms shared_y_iff
#print axioms shared_z_iff
#print axioms constrained_card
#print axioms pair_card
end ThinMatrix.CWPairHashFibers
