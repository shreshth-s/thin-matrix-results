import CWInterpolationProgram

set_option autoImplicit false

/-! Exact separated rational terms, built from retained integer weights and
integer CW evaluations. The term budget includes interpolation overhead;
there is no assertion that CW16 has exact rank 18. -/
namespace ThinMatrix.CWExactDecomposition
open scoped BigOperators
open FiniteTrilinear PolynomialDegeneration CWPolynomialCertificate CWPowerSpecialization
open CWInterpolationProgram IntegerInterpolationWeights

def terms (n : ℕ) (s : Request n) : Term (Index n) (Index n) (Index n) ℚ :=
  let table := prepare (10*n) (order n)
  let a := atInteger n s.1.val s.2
  ⟨fun i => (table.weights.get s.1:ℚ)/table.denominator*a.left i,
    fun j => a.middle j,fun k => a.right k⟩

theorem term_count (n : ℕ) : Fintype.card (Request n)=(10*n+1)*18^n := by
  simp only [Request,Fintype.card_prod,Fintype.card_fin,TermIndex,powerIndex_card]

theorem terms_total (n : ℕ) : total (terms n)=
    fun i j k => (tensorPower (target (R:=ℤ) 16) n i j k : ℚ) := by
  funext i j k
  have h := IntegerCoefficientExtraction.extract_value (10*n) (order n)
    (family n i j k) (family_bounds n i j k).2.2
    (Vector.ofFn (fun a => (family n i j k).eval a.val)) (fun _ => by simp)
  rw [IntegerCoefficientExtraction.extract_numerator,
    IntegerCoefficientExtraction.extract_denominator] at h
  simp only [Vector.get_ofFn,order,(family_bounds n i j k).2.1] at h
  rw [← h]
  simp only [total,terms,Term.tensor,Fintype.sum_prod_type,prepare_weight,prepare_den,
    Int.cast_sum,Int.cast_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have he := congrFun (congrFun (congrFun (atInteger_eval n a.val) i) j) k
  rw [← he]
  simp only [total,Term.tensor,Int.cast_sum,Int.cast_mul,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  simp only [order]
  ring

theorem terms_bilinear (n : ℕ) (x y : Index n → ℚ) (k : Index n) :
    (∑ s : Request n,(terms n s).right k*(∑ i,(terms n s).left i*x i)*
      (∑ j,(terms n s).middle j*y j))=
    bilinear (fun i j k => (tensorPower (target (R:=ℤ) 16) n i j k:ℚ)) x y k := by
  rw [← total_bilinear,terms_total]

theorem zero_count : Fintype.card (Request 0)=1 := by rw [term_count];norm_num

#print axioms term_count
#print axioms terms_total
#print axioms terms_bilinear
#print axioms zero_count
end ThinMatrix.CWExactDecomposition
