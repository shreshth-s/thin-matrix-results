import CWPowerSpecialization

set_option autoImplicit false

namespace ThinMatrix.CWFiniteKeys
open scoped BigOperators
open PolynomialDegeneration CWPolynomialCertificate CWPowerSpecialization
variable {A R : Type*}

def keys (base : List A) : (n : ℕ) → List (PowerIndex A n)
  | 0 => [PUnit.unit]
  | n+1 => let child := keys base n
    base.flatMap (fun a => child.map (fun b => (a,b)))

theorem keys_length (base : List A) (n : ℕ) : (keys base n).length=base.length^n := by
  induction n with
  | zero => simp [keys]
  | succ n ih => simp [keys,List.length_flatMap,ih,pow_succ' ]

theorem flatMap_sum [AddMonoid R] (xs : List A) (f : A → List R) :
    (xs.flatMap f).sum=(xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih,List.sum_append]

theorem keys_sum [Fintype A] [AddCommMonoid R] (base : List A)
    (hb : ∀ f : A → R,(base.map f).sum=∑ a,f a) (n : ℕ) (f : PowerIndex A n → R) :
    ((keys base n).map f).sum=∑ a,f a := by
  induction n with
  | zero => simp [keys,PowerIndex]
  | succ n ih =>
      calc
        _ = ∑ a : A,∑ b : PowerIndex A n,f (a,b) := by
          simp only [keys,List.map_flatMap,flatMap_sum,List.map_map,Function.comp_def]
          rw [hb]
          apply Finset.sum_congr rfl
          intro a _
          exact ih (fun b => f (a,b))
        _ = _ := by
          rw [← Fintype.sum_prod_type]
          exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun a => rfl)

def axes : List (Axis 16) := none :: some none :: List.ofFn (fun a : Fin 16 => some (some a))
def axisKeys (n : ℕ) : List (Index n) := keys axes n
def termKeys (n : ℕ) : List (TermIndex n) := keys (List.ofFn (id : Fin 18 → Fin 18)) n

theorem axes_length : axes.length=18 := by simp [axes]

theorem axisKeys_length (n : ℕ) : (axisKeys n).length=18^n := by rw [axisKeys,keys_length,axes_length]

theorem termKeys_length (n : ℕ) : (termKeys n).length=18^n := by simp only [termKeys,keys_length,List.length_ofFn]

theorem axes_sum [AddCommMonoid R] (f : Axis 16 → R) : (axes.map f).sum=∑ a,f a := by
  simp only [axes,List.map_cons,List.sum_cons,List.map_ofFn,Function.comp_def,List.sum_ofFn,Fintype.sum_option]

theorem axisKeys_sum [AddCommMonoid R] (n : ℕ) (f : Index n → R) :
    ((axisKeys n).map f).sum=∑ a,f a := keys_sum axes axes_sum n f

theorem termKeys_sum [AddCommMonoid R] (n : ℕ) (f : TermIndex n → R) :
    ((termKeys n).map f).sum=∑ a,f a := by
  apply keys_sum
  intro f
  simp only [List.map_ofFn,Function.comp_def,id_eq,List.sum_ofFn]

#print axioms keys_length
#print axioms flatMap_sum
#print axioms keys_sum
#print axioms axes_length
#print axioms axisKeys_length
#print axioms termKeys_length
#print axioms axes_sum
#print axioms axisKeys_sum
#print axioms termKeys_sum
end ThinMatrix.CWFiniteKeys
