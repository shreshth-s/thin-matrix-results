import PolynomialDegeneration

set_option autoImplicit false

/-! Exact finite coefficient extraction at the integer nodes 0,...,d.
This semantic theorem uses mathlib's Lagrange interpolation; executable
integer coefficient construction and its charges are separate refinements. -/
namespace ThinMatrix.RationalInterpolation
open scoped BigOperators
open Polynomial FiniteTrilinear

def node {d : ℕ} (i : Fin (d+1)) : ℚ := i.val

noncomputable def weight (d k : ℕ) (i : Fin (d+1)) : ℚ :=
  (Lagrange.basis Finset.univ node i).coeff k

theorem node_injective (d : ℕ) : Function.Injective (@node d) := by
  intro i j h
  apply Fin.ext
  exact_mod_cast (show (i.val : ℚ)=j.val from h)

theorem coefficient (d k : ℕ) (p : ℚ[X]) (hp : p.natDegree≤d) :
    p.coeff k=∑ i : Fin (d+1),weight d k i*p.eval (node i) := by
  have hd : p.degree < (Finset.univ : Finset (Fin (d+1))).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hp)
  have h := congrArg (fun f : ℚ[X] => f.coeff k)
    (Lagrange.eq_interpolate (node_injective d).injOn hd)
  simp only [Lagrange.interpolate_apply,finsetSum_coeff,coeff_C_mul] at h
  simpa only [weight,mul_comm] using h

noncomputable def extractTerms {I J K : Type*} {r o d : ℕ}
    {target : Tensor I J K ℚ} (c : PolynomialDegeneration.Certificate target r o d) :
    Fin (d+1) × Fin r → Term I J K ℚ := fun s =>
  let a := (c.terms s.2).map (evalRingHom (node s.1))
  ⟨fun i => weight d o s.1*a.left i,a.middle,a.right⟩

theorem extractTerms_total {I J K : Type*} {r o d : ℕ}
    {target : Tensor I J K ℚ} (c : PolynomialDegeneration.Certificate target r o d) :
    total (extractTerms c)=target := by
  funext i j k
  rw [← c.leading i j k,coefficient d o _ (c.bounded i j k)]
  simp only [total,extractTerms,Term.tensor,Term.map,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [eval_finsetSum,eval_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [coe_evalRingHom]
  ring

#print axioms node_injective
#print axioms coefficient
#print axioms extractTerms_total
end ThinMatrix.RationalInterpolation
