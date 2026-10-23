import CountedCWCoefficients
import CWCoefficientBounds
import CWFiniteKeys

set_option autoImplicit false

/-! A finite exact bilinear execution. Input linear-form products are retained
once and reused for all output coordinates. Integer-register arithmetic is
counted, including coefficient generation and final exact division. This is
not a binary-address simulation or a fast rectangular algorithm. -/
namespace ThinMatrix.CWInterpolationProgram
open scoped BigOperators
open FiniteTrilinear PolynomialDegeneration CWPolynomialCertificate CWPowerSpecialization
open CWFiniteKeys CountedCWCoefficients IntegerInterpolationWeights

abbrev Request (n : ℕ) := Fin (10*n+1) × TermIndex n

def order (n : ℕ) : Fin (10*n+1) := ⟨3*n,by omega⟩

def requests (n : ℕ) : List (Request n) :=
  (List.ofFn (id : Fin (10*n+1) → Fin (10*n+1))).flatMap
    (fun a => (termKeys n).map (fun b => (a,b)))

theorem requests_length (n : ℕ) : (requests n).length=(10*n+1)*18^n := by
  simp only [requests,List.length_flatMap,List.length_map,termKeys_length,List.map_ofFn,
    Function.comp_def,List.sum_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

theorem requests_sum {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Request n → R) :
    ((requests n).map f).sum=∑ a : Fin (10*n+1),∑ b : TermIndex n,f (a,b) := by
  simp only [requests,List.map_flatMap,flatMap_sum,List.map_map,Function.comp_def,
    termKeys_sum,List.map_ofFn,id_eq,List.sum_ofFn]

def dot (side : Fin 3) (n : ℕ) (t : ℤ) (s : TermIndex n) (x : Index n → ℤ) : Scalar :=
  sum ((axisKeys n).map (fun i => mul (evaluate side t n s i) (lit (x i))))

theorem dot_value (side : Fin 3) (n : ℕ) (t : ℤ) (s : TermIndex n) (x : Index n → ℤ) :
    (dot side n t s x).1=∑ i,component (atInteger n t s) side i*x i := by
  simp only [dot,sum_value,List.map_map,Function.comp_def,mul,lit,evaluate_value,axisKeys_sum]

def products (n : ℕ) (x y : Index n → ℤ) : List (Request n × Scalar) :=
  (requests n).map (fun s =>
    let left := dot 0 n s.1.val s.2 x
    let right := dot 1 n s.1.val s.2 y
    (s,mul left right))

def collect (n : ℕ) (table : Table (10*n)) (rows : List (Request n × Scalar)) (k : Index n) : Scalar :=
  sum (rows.map (fun p =>
    let coefficient := evaluate 2 p.1.1.val n p.1.2 k
    mul (lit (table.weights.get p.1.1)) (mul coefficient (lit p.2.1))))

structure Output (n : ℕ) where
  key : Index n
  numerator : ℤ
  quotient : ℤ
  operations : ℕ

structure Result (n : ℕ) where
  table : Table (10*n)
  retainedProducts : List (Request n × Scalar)
  outputs : List (Output n)
  operations : ℕ

def execute (n : ℕ) (x y : Index n → ℤ) : Result n :=
  let table := prepare (10*n) (order n)
  let rows := products n x y
  let out := (axisKeys n).map (fun k =>
    let a := collect n table rows k
    (⟨k,a.1,a.1/table.denominator,a.2+1⟩ : Output n))
  ⟨table,rows,out,table.operations+(rows.map (fun p => p.2.2)).sum+(out.map Output.operations).sum⟩

theorem collect_value (n : ℕ) (x y : Index n → ℤ) (k : Index n) :
    (collect n (prepare (10*n) (order n)) (products n x y) k).1=
      ∑ a : Fin (10*n+1),weightNumerator (10*n) (order n) a*
        bilinear (total (atInteger n a.val)) x y k := by
  simp only [collect,sum_value,products,List.map_map,Function.comp_def,mul,lit,
    evaluate_value,dot_value,prepare_weight,requests_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [total_bilinear,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  norm_num [component]
  ring_nf
  simp

noncomputable def polynomial (n : ℕ) (x y : Index n → ℤ) (k : Index n) : Polynomial ℤ :=
  ∑ i,∑ j,Polynomial.C (x i*y j)*family n i j k

theorem polynomial_coeff (n a : ℕ) (x y : Index n → ℤ) (k : Index n) :
    (polynomial n x y k).coeff a=∑ i,∑ j,(family n i j k).coeff a*x i*y j := by
  simp only [polynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polynomial_degree (n : ℕ) (x y : Index n → ℤ) (k : Index n) :
    (polynomial n x y k).natDegree≤10*n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  rw [polynomial_coeff]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (family_bounds n i j k).2.2 ha)]
  simp

theorem polynomial_leading (n : ℕ) (x y : Index n → ℤ) (k : Index n) :
    (polynomial n x y k).coeff (3*n)=bilinear (tensorPower (target (R:=ℤ) 16) n) x y k := by
  simp only [polynomial_coeff,(family_bounds n _ _ _).2.1,bilinear]

theorem polynomial_eval (n : ℕ) (t : ℤ) (x y : Index n → ℤ) (k : Index n) :
    (polynomial n x y k).eval t=bilinear (total (atInteger n t)) x y k := by
  rw [atInteger_eval]
  simp only [polynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,bilinear]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem collect_exact (n : ℕ) (x y : Index n → ℤ) (k : Index n) :
    (collect n (prepare (10*n) (order n)) (products n x y) k).1=
      (prepare (10*n) (order n)).denominator*
        bilinear (tensorPower (target (R:=ℤ) 16) n) x y k := by
  rw [collect_value,prepare_den]
  have h := IntegerCoefficientExtraction.extract_exact (10*n) (order n) (polynomial n x y k)
    (polynomial_degree n x y k) (Vector.ofFn (fun a => (polynomial n x y k).eval a.val))
    (fun _ => by simp only [Vector.get_ofFn])
  simpa only [IntegerCoefficientExtraction.extract_numerator,IntegerCoefficientExtraction.extract_denominator,
    Vector.get_ofFn,polynomial_eval,order,polynomial_leading] using h

theorem execute_correct (n : ℕ) (x y : Index n → ℤ) :
    ((execute n x y).outputs.map (fun o => (o.key,o.quotient)))=
      (axisKeys n).map (fun k => (k,bilinear (tensorPower (target (R:=ℤ) 16) n) x y k)) := by
  simp only [execute,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro k _
  rw [collect_exact]
  congr 1
  exact Int.mul_ediv_cancel_left _ (by rw [prepare_den];exact commonDen_ne_zero (10*n))

#print axioms requests_length
#print axioms requests_sum
#print axioms dot_value
#print axioms collect_value
#print axioms polynomial_coeff
#print axioms polynomial_degree
#print axioms polynomial_leading
#print axioms polynomial_eval
#print axioms collect_exact
#print axioms execute_correct
end ThinMatrix.CWInterpolationProgram
