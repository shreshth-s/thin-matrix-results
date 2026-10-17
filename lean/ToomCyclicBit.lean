import ToomExecutionBound
import ToomDotCost
import PolynomialCyclicFold

/-!
All-coefficient cyclic multiplication through the actual counted integer
array program. The ordinary product is computed once; each of the q folded
coefficients then performs two array reads, a counted address addition,
a counted signed addition, and an allocated output write. The integer view
uses the canonical-bit scalar refinement; the separate BitArraySimulation
module supplies its array representation refinement.
-/
namespace ThinMatrix.ToomCyclicBit
open scoped BigOperators
open Polynomial
open ThinMatrix.ToomBitCost
open ThinMatrix.ToomCook hiding multiplyAtLength
open ThinMatrix.CyclicRing ThinMatrix.PolynomialCyclicFold
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local irreducible] ToomExecutionBound.multiplyAtLength

/-- Ring interpretation of a materialized length-q coefficient array. -/
def asCyclic (q : ℕ) (a : Array ℤ) : Cyclic q :=
  fun i=>(a[i.val]?).getD 0

theorem asCyclic_polynomial (q : ℕ) (a : Array ℤ) (ha : a.size=q) :
    toPolynomial (asCyclic q a)=arrayPolynomial a := by
  ext j
  rw [arrayPolynomial_coeff]
  by_cases hj:j<q
  · simpa only [asCyclic] using coeff_toPolynomial (asCyclic q a) (⟨j,hj⟩:Fin q)
  · rw [coeff_toPolynomial_eq_zero _ _ (by omega),Array.getElem?_eq_none (by omega)]
    rfl

/-- The arbitrary-length actual product array has its complete polynomial
interpretation, including all padded zero coefficients. -/
theorem product_array_polynomial (k q : ℕ) (hk : 2 ≤ k) (hq : 0<q)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q) :
    arrayPolynomial (ToomExecutionBound.multiplyAtLength k q a b).value=
      arrayPolynomial a*arrayPolynomial b := by
  have hf:=arrayPolynomial_natDegree a (by omega)
  have hg:=arrayPolynomial_natDegree b (by omega)
  have hp:=Polynomial.natDegree_mul_le (p:=arrayPolynomial a) (q:=arrayPolynomial b)
  have hN:=ToomCook.padded_length_bounds k q hk hq
  rw [ToomExecutionBound.multiplyAtLength_value k q hk hq a b ha hb]
  exact arrayPolynomial_ofFn _ _ (by omega)

/-- A physical dimension word is copied before it is used as an address
operand. The represented integer is a view of its stored binary digits. -/
def readDimension (q : ℕ) : ToomCook.Counted ℤ := ⟨q,q.size+1⟩

/-- The upper alias address is obtained by a literal signed-bit addition,
not by an uncharged natural-number address expression. -/
def foldCoefficient (q : ℕ) (product : Array ℤ) (i : ℕ) : ToomCook.Counted ℤ :=
  Counted.bind (readInteger product i) (fun lo=>
    Counted.bind (readDimension q) (fun modulus=>
      Counted.bind (bitPrimitives.add i modulus) (fun address=>
        Counted.bind (readInteger product address.natAbs) (fun hi=>
          bitPrimitives.add lo hi))))

def foldArray (q : ℕ) (product : Array ℤ) : ToomCook.Counted (Array ℤ) :=
  tabulateInteger q (fun i=>foldCoefficient q product i.val)

/-- The ordinary product is materialized exactly once before folding. -/
def multiply (k q : ℕ) (a b : Array ℤ) : ToomCook.Counted (Array ℤ) :=
  Counted.bind (ToomExecutionBound.multiplyAtLength k q a b) (foldArray q)

theorem foldCoefficient_value (q : ℕ) (product : Array ℤ) (i : ℕ) :
    (foldCoefficient q product i).value=
      (product[i]?).getD 0+(product[i+q]?).getD 0 := by
  simp only [foldCoefficient,Counted.bind,readInteger,readDimension,
    bitPrimitives_correct.add,←Nat.cast_add,Int.natAbs_natCast]

theorem foldArray_value (q : ℕ) (product : Array ℤ) :
    (foldArray q product).value=Array.ofFn (fun i : Fin q=>
      (product[i.val]?).getD 0+(product[i.val+q]?).getD 0) := by
  simp only [foldArray,tabulateInteger_value,foldCoefficient_value]

theorem multiply_value (k q : ℕ) (hk : 2 ≤ k) (hq : 0<q)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q) :
    (multiply k q a b).value=Array.ofFn (fun i : Fin q=>
      (arrayPolynomial a*arrayPolynomial b).coeff i.val+
      (arrayPolynomial a*arrayPolynomial b).coeff (i.val+q)) := by
  simp only [multiply,Counted.bind,foldArray_value]
  have hpoly:=product_array_polynomial k q hk hq a b ha hb
  congr 1
  funext i
  rw [←arrayPolynomial_coeff,←arrayPolynomial_coeff,hpoly]

theorem multiply_output_size (k q : ℕ) (a b : Array ℤ) :
    (multiply k q a b).value.size=q := by
  simp only [multiply,Counted.bind,foldArray_value,Array.size_ofFn]

/-- Exact cyclic-ring correctness, uniformly for every positive modulus,
including q=1. -/
theorem multiply_correct (k q : ℕ) [NeZero q] (hk : 2 ≤ k)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q) :
    asCyclic q (multiply k q a b).value=asCyclic q a*asCyclic q b := by
  funext i
  rw [mul_coeff_fold,asCyclic_polynomial q a ha,asCyclic_polynomial q b hb]
  rw [show asCyclic q (multiply k q a b).value i=
    (((multiply k q a b).value)[i.val]?).getD 0 from rfl,
    multiply_value k q hk (NeZero.pos q) a b ha hb]
  simp [i.isLt]

/-- The mathematical sum has the same bit-size bound as the concrete
canonical addition circuit, including cancellation and zero. -/
theorem int_add_size (x y : ℤ) :
    (x+y).natAbs.size ≤ max x.natAbs.size y.natAbs.size+1 := by
  have h:=IntegerArithmetic.signedAddIntCounted_size x y
  rwa [IntegerArithmetic.signedAddIntCounted_correct] at h

/-- Original input bounds give a linear bit budget for every ordinary
product coefficient; padding does not enlarge this bound. -/
theorem ordinary_product_coefficient_bits (q A : ℕ) (hq : 0<q)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q)
    (hfa : CoeffBound (arrayPolynomial a) A)
    (hfb : CoeffBound (arrayPolynomial b) A) (j : ℕ) :
    ((arrayPolynomial a*arrayPolynomial b).coeff j).natAbs.size ≤ q.size+2*A.size := by
  have hf:=arrayPolynomial_natDegree a (by omega)
  have h:=product_coefficient_bound (arrayPolynomial a) (arrayPolynomial b) q A
    (by positivity) (by omega) hfa hfb j
  have hn : ((arrayPolynomial a*arrayPolynomial b).coeff j).natAbs ≤ q*A^2 := by
    exact_mod_cast (show (((arrayPolynomial a*arrayPolynomial b).coeff j).natAbs:ℤ) ≤
      ((q*A^2:ℕ):ℤ) by simpa only [Int.natCast_natAbs,Nat.cast_mul,Nat.cast_pow] using h)
  have hs:=ToomExecutionBound.size_mul_le q (A*A)
  have hsA:=ToomExecutionBound.size_mul_le A A
  rw [pow_two] at hn
  exact (Nat.size_le_size hn).trans (by omega)

/-- Every physical ordinary-product read uses the same original-input
bit budget, at arbitrary padded or out-of-range positions. -/
theorem product_array_read_bits (k q A : ℕ) (hk : 2 ≤ k) (hq : 0<q)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q)
    (hfa : CoeffBound (arrayPolynomial a) A)
    (hfb : CoeffBound (arrayPolynomial b) A) (j : ℕ) :
    ((((ToomExecutionBound.multiplyAtLength k q a b).value)[j]?).getD 0).natAbs.size ≤
      q.size+2*A.size := by
  rw [←arrayPolynomial_coeff,product_array_polynomial k q hk hq a b ha hb]
  exact ordinary_product_coefficient_bits q A hq a b ha hb hfa hfb j

/-- Literal folding-cell bound: both reads, the dimension copy, address
addition and coefficient addition are all priced by their actual counters. -/
theorem foldCoefficient_cost (q A : ℕ) (product : Array ℤ) (i : Fin q)
    (hp : ∀ j : ℕ,((product[j]?).getD (0:ℤ)).natAbs.size ≤ q.size+2*A.size) :
    (foldCoefficient q product i.val).operations ≤ 110*(q.size+A.size+2) := by
  let V:=q.size+2*A.size
  have hi : i.val.size ≤ q.size := Nat.size_le_size i.isLt.le
  have haddr : (i.val+q).size ≤ q.size+1 := by
    have h:=int_add_size (i.val:ℤ) (q:ℤ)
    simp only [←Nat.cast_add,Int.natAbs_natCast] at h
    exact h.trans (by omega)
  have hlow : (readInteger product i.val).operations ≤ V+q.size+1 := by
    simp only [readInteger];have h:=hp i.val;dsimp [V];omega
  have hhigh : (readInteger product (i.val+q)).operations ≤ V+q.size+2 := by
    simp only [readInteger];have h:=hp (i.val+q);dsimp [V];omega
  have haddress:=bitPrimitive_add_cost (i.val:ℤ) (q:ℤ)
  simp only [Int.natAbs_natCast] at haddress
  have haddress' : (bitPrimitives.add (i.val:ℤ) (q:ℤ)).operations ≤ 50*(q.size+1) :=
    haddress.trans (by have hm:max i.val.size q.size ≤ q.size:=max_le hi (le_refl _);omega)
  have hadd:=bitPrimitive_add_cost ((product[i.val]?).getD 0) ((product[i.val+q]?).getD 0)
  have hadd' : (bitPrimitives.add ((product[i.val]?).getD 0)
      ((product[i.val+q]?).getD 0)).operations ≤ 50*(V+1) := by
    apply hadd.trans
    have hm:max ((product[i.val]?).getD 0).natAbs.size
      ((product[i.val+q]?).getD 0).natAbs.size ≤ V:=max_le (hp _) (hp _)
    omega
  simp only [foldCoefficient,Counted.bind,readDimension,readInteger,
    bitPrimitives_correct.add,←Nat.cast_add,Int.natAbs_natCast] at ⊢
  change ((product[i.val]?).getD 0).natAbs.size+i.val.size+1+
    (q.size+1+((bitPrimitives.add (i.val:ℤ) (q:ℤ)).operations+
      (((product[i.val+q]?).getD 0).natAbs.size+(i.val+q).size+1+
        (bitPrimitives.add ((product[i.val]?).getD 0) ((product[i.val+q]?).getD 0)).operations))) ≤ _
  dsimp [V] at hlow hhigh hadd'
  have hlo:=hp i.val
  have hhi:=hp (i.val+q)
  omega

/-- A q-cell dense fold is linear in q and the original binary input
sizes, with allocation, index, result-copy and write charges included. -/
theorem foldArray_cost (q A : ℕ) (product : Array ℤ)
    (hp : ∀ j : ℕ,((product[j]?).getD (0:ℤ)).natAbs.size ≤ q.size+2*A.size) :
    (foldArray q product).operations ≤ 200*q*(q.size+A.size+2) := by
  unfold foldArray
  have hcell:=fun i : Fin q=>foldCoefficient_cost q A product i hp
  have hout (i : Fin q) : (foldCoefficient q product i.val).value.natAbs.size ≤ q.size+2*A.size+1 := by
    rw [foldCoefficient_value]
    exact (int_add_size _ _).trans (by have h1:=hp i.val;have h2:=hp (i.val+q);omega)
  have hi (i : Fin q) : i.val.size ≤ q.size := Nat.size_le_size i.isLt.le
  have h:=tabulateInteger_operations_le q (110*(q.size+A.size+2))
    (q.size+2*A.size+1) q.size _ hcell hout hi
  apply h.trans
  nlinarith

/-- Fixed arity-dependent constant for complete cyclic multiplication. -/
def cyclicBitConstant : ℝ := ToomExecutionBound.bitConstant 100000000+200

/-- Complete all-q multiplication with the charged epsilon and a cubic
polynomial in the original coefficient and modulus binary sizes. -/
theorem multiply_fixed_cost (q A : ℕ) (hq : 0<q) (a b : Array ℤ)
    (ha : a.size=q) (hb : b.size=q)
    (hfa : CoeffBound (arrayPolynomial a) A)
    (hfb : CoeffBound (arrayPolynomial b) A) :
    ((multiply (2^100000000) q a b).operations:ℝ) ≤
      cyclicBitConstant*(q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2:ℕ):ℝ)^3 := by
  have hm:=ToomExecutionBound.multiplyAtLength_fixed_bound q A hq a b ha hb hfa hfb
  have hf:=foldArray_cost q A (ToomExecutionBound.multiplyAtLength (2^100000000) q a b).value
    (fun j=>product_array_read_bits _ q A
      (ToomCook.two_le_two_pow 100000000 (by norm_num)) hq a b ha hb hfa hfb j)
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqr : (q:ℝ) ≤ (q:ℝ)^(1.00000001:ℝ) :=
    Real.self_le_rpow_of_one_le hqR (by norm_num)
  have hT : (1:ℝ) ≤ ((q.size+A.size+2:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ q.size+A.size+2 by omega)
  have hTp : ((q.size+A.size+2:ℕ):ℝ) ≤ ((q.size+A.size+2:ℕ):ℝ)^3 := by
    have hs : (1:ℝ) ≤ ((q.size+A.size+2:ℕ):ℝ)^2 := by nlinarith
    have hp:=mul_le_mul_of_nonneg_left hs (by linarith : (0:ℝ) ≤ ((q.size+A.size+2:ℕ):ℝ))
    nlinarith
  have hfold : ((foldArray q (ToomExecutionBound.multiplyAtLength (2^100000000) q a b).value).operations:ℝ) ≤
      200*(q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2:ℕ):ℝ)^3 := by
    have hc : ((foldArray q (ToomExecutionBound.multiplyAtLength (2^100000000) q a b).value).operations:ℝ) ≤
        ((200*q*(q.size+A.size+2):ℕ):ℝ) := Nat.cast_le.mpr hf
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at hc
    apply hc.trans
    have hprod : 200*(q:ℝ)*((q.size+A.size+2:ℕ):ℝ) ≤
        200*(q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2:ℕ):ℝ)^3 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hqr (by norm_num)
      · exact hTp
      · positivity
      · positivity
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hprod
  simp only [multiply,Counted.bind]
  rw [Nat.cast_add]
  unfold cyclicBitConstant
  nlinarith

/-- One complete materialized cyclic vector with exact ring semantics and
its unconditional counted-execution bound. -/
theorem multiply_fixed_correct_and_cost (q A : ℕ) [NeZero q]
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q)
    (hfa : CoeffBound (arrayPolynomial a) A)
    (hfb : CoeffBound (arrayPolynomial b) A) :
    (multiply (2^100000000) q a b).value.size=q ∧
      asCyclic q (multiply (2^100000000) q a b).value=asCyclic q a*asCyclic q b ∧
      ((multiply (2^100000000) q a b).operations:ℝ) ≤
        cyclicBitConstant*(q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2:ℕ):ℝ)^3 := by
  exact ⟨multiply_output_size _ _ _ _,
    multiply_correct _ _ (ToomCook.two_le_two_pow 100000000 (by norm_num)) a b ha hb,
    multiply_fixed_cost q A (NeZero.pos q) a b ha hb hfa hfb⟩

#print axioms multiply_fixed_correct_and_cost

#print axioms multiply_correct
#print axioms ordinary_product_coefficient_bits
#print axioms foldCoefficient_cost
#print axioms foldArray_cost
#print axioms multiply_fixed_cost
end
end ThinMatrix.ToomCyclicBit
