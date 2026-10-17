import CyclicRing
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Tactic

/-!
# Exact ordinary-polynomial to cyclic-convolution folding

Every length-q integer vector is encoded by an ordinary polynomial of degree
less than q. Multiplying two encodings creates degrees at most 2q-2, so a
cyclic coefficient is the sum of exactly the ordinary coefficients at k and
k+q. The modulus is any positive integer, including one. These are semantic
identities and support bounds, not multiplication or bit-cost algorithms.
-/

namespace ThinMatrix.PolynomialCyclicFold

open scoped BigOperators
open CyclicRing

/-- The ordinary integer polynomial with the vector's q coefficients. -/
noncomputable def toPolynomial {q : ℕ} (a : Cyclic q) : Polynomial ℤ :=
  ∑ i : Fin q, Polynomial.monomial i.val (a i)

theorem coeff_toPolynomial_eq_sum {q : ℕ} (a : Cyclic q) (n : ℕ) :
    (toPolynomial a).coeff n = ∑ i : Fin q, if i.val = n then a i else 0 := by
  simp only [toPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem coeff_toPolynomial {q : ℕ} (a : Cyclic q) (k : Fin q) :
    (toPolynomial a).coeff k.val = a k := by
  rw [coeff_toPolynomial_eq_sum]
  have heq (i : Fin q) : i.val = k.val ↔ i = k := Fin.ext_iff.symm
  simp_rw [heq]
  simp

theorem coeff_toPolynomial_eq_zero {q : ℕ} (a : Cyclic q) (n : ℕ) (hn : q ≤ n) :
    (toPolynomial a).coeff n = 0 := by
  rw [coeff_toPolynomial_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : i.val ≠ n := by have hiq := i.isLt; omega
  simp only [if_neg hne]

theorem toPolynomial_degree_lt {q : ℕ} (a : Cyclic q) :
    (toPolynomial a).degree < (q : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  exact coeff_toPolynomial_eq_zero a

/-- Expand the ordinary polynomial product into its actual double monomial sum. -/
theorem product_eq_sum_monomials {q : ℕ} (a b : Cyclic q) :
    toPolynomial a * toPolynomial b =
      ∑ i : Fin q, ∑ j : Fin q, Polynomial.monomial (i.val+j.val) (a i*b j) := by
  simp only [toPolynomial, Finset.sum_mul, Finset.mul_sum, Polynomial.monomial_mul_monomial]
  rw [Finset.sum_comm]

theorem coeff_product_eq_sum {q : ℕ} (a b : Cyclic q) (n : ℕ) :
    (toPolynomial a * toPolynomial b).coeff n =
      ∑ i : Fin q, ∑ j : Fin q, if i.val+j.val = n then a i*b j else 0 := by
  rw [product_eq_sum_monomials]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

/-- No ordinary product coefficient at or above 2q-1 can contribute an alias. -/
theorem coeff_product_eq_zero_of_ge {q : ℕ} (a b : Cyclic q) (n : ℕ)
    (hn : 2*q-1 ≤ n) : (toPolynomial a*toPolynomial b).coeff n = 0 := by
  rw [coeff_product_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hne : i.val+j.val ≠ n := by
    have hiq := i.isLt
    have hjq := j.isLt
    omega
  simp only [if_neg hne]

theorem product_degree_lt {q : ℕ} (a b : Cyclic q) :
    (toPolynomial a*toPolynomial b).degree < ((2*q-1 : ℕ) : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  exact coeff_product_eq_zero_of_ge a b

/-- The cyclic vector is reconstructed from all of its actual monomials. -/
theorem cyclic_eq_sum_monomials {q : ℕ} [NeZero q] (a : Cyclic q) :
    a = ∑ i : Fin q, CyclicRing.monomial i (a i) := by
  funext k
  simp [CyclicRing.sum_coeff, CyclicRing.monomial]

/-- Expansion inside the transported cyclic ring; exponents add modulo q. -/
theorem convolution_eq_sum {q : ℕ} [NeZero q] (a b : Cyclic q) (k : Fin q) :
    convolution a b k =
      ∑ i : Fin q, ∑ j : Fin q, if k = i+j then a i*b j else 0 := by
  calc
    _ = (a*b) k := congrFun (CyclicRing.mul_eq_convolution a b).symm k
    _ = ((∑ i : Fin q, CyclicRing.monomial i (a i)) *
        (∑ j : Fin q, CyclicRing.monomial j (b j))) k := by
      rw [← cyclic_eq_sum_monomials a, ← cyclic_eq_sum_monomials b]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, CyclicRing.sum_coeff, CyclicRing.monomial_mul_coeff]
      rw [Finset.sum_comm]

theorem fin_add_lifts {q : ℕ} (i j k : Fin q) :
    k = i+j ↔ i.val+j.val = k.val ∨ i.val+j.val = k.val+q := by
  have hk := k.isLt
  rw [Fin.ext_iff, Fin.val_add_eq_ite]
  split_ifs <;> omega

theorem fin_add_lifts_disjoint {q : ℕ} (i j k : Fin q) :
    ¬(i.val+j.val = k.val ∧ i.val+j.val = k.val+q) := by
  have hk := k.isLt
  omega

theorem fin_add_indicator {R : Type*} [AddZeroClass R] {q : ℕ}
    (hq : 0<q) (i j k : Fin q) (a : R) :
    (if k = i+j then a else 0) =
      (if i.val+j.val = k.val then a else 0) +
      (if i.val+j.val = k.val+q then a else 0) := by
  classical
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hiff := fin_add_lifts i j k
  by_cases h0 : i.val+j.val = k.val
  · simp [hiff, h0, hq0]
  · by_cases h1 : i.val+j.val = k.val+q <;> simp [hiff, h0, h1, hq0]

/-- Exact arbitrary-modulus folding. Only the two displayed ordinary degrees
can have the requested residue; their contributions are disjoint. -/
theorem convolution_eq_coeff_fold {q : ℕ} [NeZero q] (a b : Cyclic q) (k : Fin q) :
    convolution a b k =
      (toPolynomial a*toPolynomial b).coeff k.val +
      (toPolynomial a*toPolynomial b).coeff (k.val+q) := by
  rw [convolution_eq_sum, coeff_product_eq_sum, coeff_product_eq_sum]
  simp_rw [fin_add_indicator (NeZero.pos q)]
  simp only [Finset.sum_add_distrib]

theorem mul_coeff_fold {q : ℕ} [NeZero q] (a b : Cyclic q) (k : Fin q) :
    (a*b) k = (toPolynomial a*toPolynomial b).coeff k.val +
      (toPolynomial a*toPolynomial b).coeff (k.val+q) := by
  rw [CyclicRing.mul_eq_convolution]
  exact convolution_eq_coeff_fold a b k

/-- Every potential third or later alias is zero, uniformly in its index. -/
theorem coeff_product_later_alias_zero {q : ℕ} (a b : Cyclic q) (k : Fin q)
    (t : ℕ) (ht : 2 ≤ t) :
    (toPolynomial a*toPolynomial b).coeff (k.val+t*q) = 0 := by
  apply coeff_product_eq_zero_of_ge
  have hm := Nat.mul_le_mul_right q ht
  omega

#print axioms coeff_product_eq_sum
#print axioms product_degree_lt
#print axioms convolution_eq_sum
#print axioms convolution_eq_coeff_fold
#print axioms coeff_product_later_alias_zero

end ThinMatrix.PolynomialCyclicFold
