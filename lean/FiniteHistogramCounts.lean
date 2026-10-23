import FiniteHistogram

set_option autoImplicit false
namespace ThinMatrix.FiniteHistogramCounts
open scoped BigOperators
open FiniteHistogram
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

def typeClass (f : I → A) : Finset (I → A) := Finset.univ.filter (fun g => ∀ a,hist g a=hist f a)
def orbitMap (f : I → A) (e : Equiv.Perm I) : typeClass f :=
  ⟨f ∘ e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun a => hist_comp f e a⟩⟩

theorem perm_fiber_card (f g : I → A) (h : ∀ a,hist g a=hist f a) :
    Fintype.card {e : Equiv.Perm I // f ∘ e=g}=∏ a,(hist f a).factorial := by
  obtain ⟨q,hq⟩ := exists_perm f g (fun a => (h a).symm)
  calc
    _ = Fintype.card {e : Equiv.Perm I // f ∘ e=f} := by
      apply Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulRight q⁻¹) ?_)
      intro e
      constructor
      · intro he
        funext i
        change f (e (q.symm i))=f i
        calc
          _ = g (q.symm i) := congrFun he _
          _ = f (q (q.symm i)) := (congrFun hq _).symm
          _ = f i := congrArg f (q.apply_symm_apply i)
      · intro he
        funext i
        have hi := congrFun he (q i)
        change f (e (q.symm (q i)))=f (q i) at hi
        rw [Equiv.symm_apply_apply] at hi
        exact hi.trans (congrFun hq i)
    _ = _ := DomMulAct.stabilizer_card f

omit [DecidableEq I] in
theorem hist_sum (f : I → A) : (∑ a,hist f a)=Fintype.card I := by
  exact (Fintype.card_sigma (α:=fun a => {i // f i=a})).symm.trans
    (Fintype.card_congr (Equiv.sigmaFiberEquiv f))

theorem typeClass_factorial (f : I → A) :
    (typeClass f).card*(∏ a,(hist f a).factorial)=(Fintype.card I).factorial := by
  have he (g : typeClass f) : Fintype.card {e : Equiv.Perm I // orbitMap f e=g}=∏ a,(hist f a).factorial := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun e => show orbitMap f e=g ↔ f ∘ e=g.val from Subtype.ext_iff))]
    exact perm_fiber_card f g.val (Finset.mem_filter.mp g.property).2
  calc
    _ = ∑ _g : typeClass f,∏ a,(hist f a).factorial := by simp
    _ = ∑ g : typeClass f,Fintype.card {e : Equiv.Perm I // orbitMap f e=g} := by simp_rw [he]
    _ = Fintype.card (Σ g : typeClass f,{e : Equiv.Perm I // orbitMap f e=g}) := (Fintype.card_sigma).symm
    _ = Fintype.card (Equiv.Perm I) := Fintype.card_congr (Equiv.sigmaFiberEquiv (orbitMap f))
    _ = _ := Fintype.card_perm

theorem typeClass_multinomial (f : I → A) :
    (typeClass f).card=Nat.multinomial Finset.univ (hist f) := by
  apply Nat.eq_of_mul_eq_mul_left (show 0<∏ a,(hist f a).factorial from Finset.prod_pos (fun a _ => Nat.factorial_pos _))
  rw [Nat.multinomial_spec,hist_sum,mul_comm,typeClass_factorial]

#print axioms perm_fiber_card
#print axioms hist_sum
#print axioms typeClass_factorial
#print axioms typeClass_multinomial
end ThinMatrix.FiniteHistogramCounts
