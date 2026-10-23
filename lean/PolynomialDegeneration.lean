import FiniteTrilinear

set_option autoImplicit false

/-! Explicit finite polynomial degeneration certificates. The term count is
an upper-bound witness, not an assertion that the target has that exact rank.
Orders add and term counts multiply under tensor products. Coordinate
restriction retains the same term budget. These finite operations are the
interfaces for later type-class extraction and polynomial interpolation. -/
namespace ThinMatrix.PolynomialDegeneration
open scoped BigOperators
open Polynomial FiniteTrilinear
variable {R I J K I' J' K' : Type*} [CommRing R]

structure Certificate (target : Tensor I J K R) (count order degree : ℕ) where
  terms : Fin count → Term I J K R[X]
  below : ∀ i j k n, n<order → (total terms i j k).coeff n=0
  leading : ∀ i j k, (total terms i j k).coeff order=target i j k
  bounded : ∀ i j k, (total terms i j k).natDegree≤degree

theorem mul_below (p q : R[X]) (a b : ℕ)
    (hp : ∀ n, n<a → p.coeff n=0) (hq : ∀ n, n<b → q.coeff n=0)
    (n : ℕ) (hn : n<a+b) : (p*q).coeff n=0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  have hh : ij.1<a ∨ ij.2<b := by omega
  rcases hh with h | h
  · rw [hp _ h,zero_mul]
  · rw [hq _ h,mul_zero]

theorem mul_leading (p q : R[X]) (a b : ℕ)
    (hp : ∀ n, n<a → p.coeff n=0) (hq : ∀ n, n<b → q.coeff n=0) :
    (p*q).coeff (a+b)=p.coeff a*q.coeff b := by
  rw [coeff_mul]
  apply Finset.sum_eq_single (a,b)
  · intro ij hij hne
    have hs := Finset.mem_antidiagonal.mp hij
    have hh : ij.1<a ∨ ij.2<b := by
      by_contra h
      push Not at h
      have hi : ij.1=a := by omega
      have hj : ij.2=b := by omega
      exact hne (Prod.ext hi hj)
    rcases hh with h | h
    · rw [hp _ h,zero_mul]
    · rw [hq _ h,mul_zero]
  · simp

noncomputable def Certificate.restrict {target : Tensor I J K R} {count order degree : ℕ}
    (c : Certificate target count order degree) (f : I' → I) (g : J' → J) (h : K' → K) :
    Certificate (FiniteTrilinear.restrict target f g h) count order degree where
  terms := fun a => (c.terms a).restrict f g h
  below := fun i j k n hn => c.below (f i) (g j) (h k) n hn
  leading := fun i j k => c.leading (f i) (g j) (h k)
  bounded := fun i j k => c.bounded (f i) (g j) (h k)

noncomputable def productTerms {r s : ℕ}
    (a : Fin r → Term I J K R[X]) (b : Fin s → Term I' J' K' R[X]) :
    Fin (r*s) → Term (I×I') (J×J') (K×K') R[X] :=
  fun t => let ij := finProdFinEquiv.symm t; (a ij.1).product (b ij.2)

theorem productTerms_total {r s : ℕ}
    (a : Fin r → Term I J K R[X]) (b : Fin s → Term I' J' K' R[X]) :
    total (productTerms a b)=FiniteTrilinear.product (total a) (total b) := by
  unfold productTerms
  rw [total_reindex finProdFinEquiv (fun ij => (a ij.1).product (b ij.2)),total_product]

noncomputable def Certificate.product {target : Tensor I J K R} {other : Tensor I' J' K' R}
    {r s a b d e : ℕ} (c : Certificate target r a d) (v : Certificate other s b e) :
    Certificate (FiniteTrilinear.product target other) (r*s) (a+b) (d+e) where
  terms := productTerms c.terms v.terms
  below := by
    intro i j k n hn
    rw [productTerms_total]
    exact mul_below _ _ a b (c.below _ _ _) (v.below _ _ _) n hn
  leading := by
    intro i j k
    rw [productTerms_total]
    change ((total c.terms i.1 j.1 k.1)*(total v.terms i.2 j.2 k.2)).coeff (a+b)=_
    rw [mul_leading _ _ a b (c.below _ _ _) (v.below _ _ _),c.leading,v.leading]
    rfl
  bounded := by
    intro i j k
    rw [productTerms_total]
    exact (natDegree_mul_le).trans (Nat.add_le_add (c.bounded _ _ _) (v.bounded _ _ _))

universe u
/-- Nested finite product coordinates, with a singleton zeroth power. -/
def PowerIndex (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => I × PowerIndex I n

instance powerIndexFintype [Fintype I] (n : ℕ) : Fintype (PowerIndex I n) := by
  induction n with
  | zero => change Fintype PUnit;infer_instance
  | succ n ih =>
      letI := ih
      change Fintype (I × PowerIndex I n)
      infer_instance

theorem powerIndex_card [Fintype I] (n : ℕ) : Fintype.card (PowerIndex I n)=(Fintype.card I)^n := by
  induction n with
  | zero => simp [PowerIndex]
  | succ n ih =>
      calc
        Fintype.card (PowerIndex I (n+1)) = Fintype.card (I × PowerIndex I n) :=
          Fintype.card_congr (Equiv.refl _)
        _ = (Fintype.card I)^(n+1) := by rw [Fintype.card_prod,ih,pow_succ']

def tensorPower (target : Tensor I J K R) : (n : ℕ) → Tensor (PowerIndex I n) (PowerIndex J n) (PowerIndex K n) R
  | 0 => fun _ _ _ => 1
  | n+1 => FiniteTrilinear.product target (tensorPower target n)

noncomputable def Certificate.power {target : Tensor I J K R} {r order degree : ℕ}
    (c : Certificate target r order degree) : (n : ℕ) →
    Certificate (tensorPower target n) (r^n) (order*n) (degree*n)
  | 0 => {
      terms := fun _ => ⟨fun _ => 1,fun _ => 1,fun _ => 1⟩
      below := by intro i j k n hn;omega
      leading := by intro i j k;simp [total,Term.tensor,tensorPower]
      bounded := by intro i j k;simp [total,Term.tensor] }
  | n+1 => by
      simpa only [PowerIndex,tensorPower,pow_succ',Nat.mul_succ,Nat.add_comm] using
        c.product (c.power n)

#print axioms powerIndex_card
#print axioms Certificate.power
#print axioms mul_below
#print axioms mul_leading
#print axioms Certificate.restrict
#print axioms productTerms_total
#print axioms Certificate.product
end ThinMatrix.PolynomialDegeneration
