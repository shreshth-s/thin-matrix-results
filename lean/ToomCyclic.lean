import ToomCook
import PolynomialCyclicFold

/-!+# All-coefficient integer cyclic multiplication through exact Toom--Cook

One stored integer polynomial product supplies every cyclic coefficient.
Only the two possible ordinary degrees are read for each output coefficient.
The count below composes ToomCook's arithmetic-slot schedule with the actual
two-read/add/write folding schedule. Integer bit operations, representation
conversion, and a machine execution refinement remain separate obligations;
this module does not treat an unbounded integer operation as constant time.
-/

namespace ThinMatrix.ToomCyclic

open CyclicRing PolynomialCyclicFold
noncomputable section

theorem input_natDegree_lt {q : ℕ} (hq : 0 < q) (a : Cyclic q) :
    (toPolynomial a).natDegree < q := by
  by_cases hz : toPolynomial a = 0
  · simp [hz, hq]
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (toPolynomial_degree_lt a)

/-- The product is evaluated once, before all output cells are materialized. -/
def multiply {q : ℕ} (B : ℕ) (a b : Cyclic q) :
    ToomCook.Counted (List.Vector ℤ q) :=
  let product := ToomCook.multiplyAtLength B q (toPolynomial a) (toPolynomial b)
  { value := List.Vector.ofFn (fun i : Fin q =>
      product.value.coeff i.val + product.value.coeff (i.val+q))
    operations := product.operations + 4*q }

theorem multiply_correct {q : ℕ} [NeZero q] (B : ℕ) (hB : 0 < B)
    (a b : Cyclic q) (i : Fin q) :
    (multiply B a b).value.get i = (a*b) i := by
  have hp := ToomCook.multiplyAtLength_correct B q hB (NeZero.pos q)
    (toPolynomial a) (toPolynomial b)
    (input_natDegree_lt (NeZero.pos q) a) (input_natDegree_lt (NeZero.pos q) b)
  simp only [multiply, List.Vector.get_ofFn, hp]
  exact (mul_coeff_fold a b i).symm

def fixedCoefficientConstant : ℝ :=
  (2*(ToomCook.overheadFactor (2^100000000))+1:ℝ)*
    ((2:ℝ)^100000000)^(1.00000001:ℝ) + 4

/-- All q coefficients, including q=1, with the folding writes charged.
The enormous arity-dependent constant is kept symbolic. -/
theorem fixed_schedule_bound {q : ℕ} [NeZero q] (a b : Cyclic q) :
    ((multiply 100000000 a b).operations : ℝ) ≤
      fixedCoefficientConstant*(q:ℝ)^(1.00000001:ℝ) := by
  have ht := ToomCook.multiplyAtLength_fixed_operations q (NeZero.pos q)
    (toPolynomial a) (toPolynomial b)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hpow := Real.self_le_rpow_of_one_le hq
    (show (1:ℝ) ≤ (1.00000001:ℝ) by norm_num)
  change (((ToomCook.multiplyAtLength 100000000 q
    (toPolynomial a) (toPolynomial b)).operations+4*q:ℕ):ℝ) ≤ _
  push_cast
  unfold fixedCoefficientConstant
  nlinarith

#print axioms input_natDegree_lt
#print axioms multiply_correct
#print axioms fixed_schedule_bound

end
end ThinMatrix.ToomCyclic
