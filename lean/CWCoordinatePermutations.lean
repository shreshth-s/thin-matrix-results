import CWTypeCounts
import FiniteHistogram

set_option autoImplicit false
namespace ThinMatrix.CWCoordinatePermutations
open scoped BigOperators
open PolynomialDegeneration CWBlockWords CWTypeCounts

def toFn {A : Type*} : (n : ℕ) → PowerIndex A n → Fin n → A
  | 0 => fun _ => Fin.elim0
  | n+1 => fun w => Fin.cases w.1 (toFn n w.2)
def ofFn {A : Type*} : (n : ℕ) → (Fin n → A) → PowerIndex A n
  | 0 => fun _ => PUnit.unit
  | n+1 => fun f => (f 0,ofFn n (fun i => f i.succ))

def funEquiv (A : Type*) (n : ℕ) : PowerIndex A n ≃ (Fin n → A) where
  toFun := toFn n
  invFun := ofFn n
  left_inv := by
    intro w
    induction n with
    | zero => cases w;rfl
    | succ n ih => exact Prod.ext rfl (ih w.2)
  right_inv := by
    intro f
    induction n with
    | zero => funext i;exact Fin.elim0 i
    | succ n ih =>
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun (ih (fun j => f j.succ)) j

theorem count_hist {A : Type*} [DecidableEq A] (n : ℕ) (w : PowerIndex A n) (a : A) :
    count a n w=FiniteHistogram.hist (toFn n w) a := by
  unfold FiniteHistogram.hist
  rw [Fintype.card_subtype]
  simp only [Finset.card_filter]
  induction n with
  | zero => simp [count]
  | succ n ih =>
      simp only [count,Fin.sum_univ_succ,toFn,Fin.cases_zero,Fin.cases_succ]
      rw [ih w.2]
      congr 1

theorem toFn_map {A B : Type*} (f : A → B) (n : ℕ) (w : PowerIndex A n) :
    toFn n (mapWord f n w)=f ∘ toFn n w := by
  induction n with
  | zero => funext i;exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (ih w.2) j

def permute {A : Type*} (n : ℕ) (e : Equiv.Perm (Fin n)) : Equiv.Perm (PowerIndex A n) :=
  (funEquiv A n).trans ((Equiv.piCongrLeft (fun _ : Fin n => A) e.symm).trans (funEquiv A n).symm)

theorem toFn_permute {A : Type*} (n : ℕ) (e : Equiv.Perm (Fin n)) (w : PowerIndex A n) :
    toFn n (permute n e w)=toFn n w ∘ e := by
  change (funEquiv A n) ((funEquiv A n).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext i
  simp [Equiv.piCongrLeft,funEquiv]

theorem count_permute {A : Type*} [DecidableEq A] (n : ℕ) (e : Equiv.Perm (Fin n))
    (w : PowerIndex A n) (a : A) : count a n (permute n e w)=count a n w := by
  rw [count_hist,toFn_permute,FiniteHistogram.hist_comp,← count_hist]

theorem map_permute {A B : Type*} (f : A → B) (n : ℕ) (e : Equiv.Perm (Fin n)) (w : PowerIndex A n) :
    mapWord f n (permute n e w)=permute n e (mapWord f n w) := by
  apply (funEquiv B n).injective
  change toFn n _=toFn n _
  rw [toFn_map,toFn_permute,toFn_permute,toFn_map]
  rfl

theorem exists_permute {A : Type*} [DecidableEq A] (n : ℕ) (u v : PowerIndex A n)
    (h : ∀ a,count a n u=count a n v) : ∃ e : Equiv.Perm (Fin n),permute n e u=v := by
  obtain ⟨e,he⟩ := FiniteHistogram.exists_perm (toFn n u) (toFn n v)
    (fun a => by simpa only [← count_hist] using h a)
  refine ⟨e,(funEquiv A n).injective ?_⟩
  exact (toFn_permute n e u).trans he

#print axioms funEquiv
#print axioms permute
#print axioms count_hist
#print axioms toFn_map
#print axioms toFn_permute
#print axioms count_permute
#print axioms map_permute
#print axioms exists_permute
end ThinMatrix.CWCoordinatePermutations
