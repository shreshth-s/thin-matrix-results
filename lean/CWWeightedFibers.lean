import CWHashSeparation

set_option autoImplicit false

namespace ThinMatrix.CWWeightedFibers
open PolynomialDegeneration CWBlockWords CWHashSeparation
variable {F : Type*} [Field F] [DecidableEq F]

abbrev Fiber (n : ℕ) (x y : Colors n) (c : F) :=
  {w : PowerIndex F n // weighted n w x-weighted n w y=c}

/-- If the first coefficient differs, all remaining weights are free. -/
def headEquiv (n : ℕ) (x y : Colors (n+1)) (c : F)
    (h : (x.1.val:F)-(y.1.val:F)≠0) : Fiber n.succ x y c ≃ PowerIndex F n where
  toFun w := w.val.2
  invFun t := ⟨((c-(weighted n t x.2-weighted n t y.2))/((x.1.val:F)-(y.1.val:F)),t),by
    change _+weighted n t x.2-(_+weighted n t y.2)=c
    have hd := div_mul_cancel₀ (c-(weighted n t x.2-weighted n t y.2)) h
    linear_combination hd⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · apply (div_eq_iff h).2
      have hw := w.property
      change w.val.1*(x.1.val:F)+weighted n w.val.2 x.2-
        (w.val.1*(y.1.val:F)+weighted n w.val.2 y.2)=c at hw
      linear_combination -hw
    · rfl
  right_inv _ := rfl

/-- If the first coefficient agrees, that weight is free and the tail decides. -/
def tailEquiv (n : ℕ) (x y : Colors (n+1)) (c : F)
    (h : (x.1.val:F)=(y.1.val:F)) : Fiber n.succ x y c ≃ F×Fiber n x.2 y.2 c where
  toFun w := (w.val.1,⟨w.val.2,by
    have hw := w.property
    change w.val.1*(x.1.val:F)+weighted n w.val.2 x.2-
      (w.val.1*(y.1.val:F)+weighted n w.val.2 y.2)=c at hw
    rw [h] at hw
    linear_combination hw⟩)
  invFun t := ⟨(t.1,t.2.val),by
    change t.1*(x.1.val:F)+weighted n t.2.val x.2-
      (t.1*(y.1.val:F)+weighted n t.2.val y.2)=c
    rw [h]
    linear_combination t.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_mul [Fintype F]
    (hinj : Function.Injective (fun a : Fin 3 => (a.val:F)))
    (n : ℕ) (x y : Colors n) (hne : x≠y) (c : F) :
    Fintype.card (Fiber n x y c)*Fintype.card F=(Fintype.card F)^n := by
  induction n with
  | zero =>
      change PUnit at x y
      exact False.elim (hne (@Subsingleton.elim PUnit inferInstance x y))
  | succ n ih =>
      by_cases h : x.1=y.1
      · have ht : x.2≠y.2 := fun ht => hne (Prod.ext h ht)
        rw [Fintype.card_congr (tailEquiv n x y c (congrArg (fun a : Fin 3 => (a.val:F)) h)),Fintype.card_prod]
        rw [mul_assoc,ih x.2 y.2 ht,pow_succ']
      · have hc : (x.1.val:F)-(y.1.val:F)≠0 := sub_ne_zero.mpr (fun he => h (hinj he))
        rw [Fintype.card_congr (headEquiv n x y c hc),powerIndex_card,pow_succ]

theorem card [Fintype F]
    (hinj : Function.Injective (fun a : Fin 3 => (a.val:F)))
    (n : ℕ) (x y : Colors n) (hne : x≠y) (c : F) :
    Fintype.card (Fiber n x y c)=(Fintype.card F)^(n-1) := by
  have hn : 0<n := by
    cases n with
    | zero =>
        change PUnit at x y
        exact False.elim (hne (@Subsingleton.elim PUnit inferInstance x y))
    | succ n => omega
  have h := card_mul hinj n x y hne c
  have he : (Fintype.card F)^(n-1)*Fintype.card F=(Fintype.card F)^n := by
    rw [← pow_succ,Nat.sub_add_cancel hn]
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos (h.trans he.symm)

#print axioms card_mul
#print axioms card
end ThinMatrix.CWWeightedFibers
