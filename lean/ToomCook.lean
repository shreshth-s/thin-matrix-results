import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
Exact fixed-arity Toom--Cook interpolation. Rational interpolation coefficients
are fixed by the arity; no floating-point arithmetic is used.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace ThinMatrix.ToomCook
open scoped BigOperators
open Polynomial Finset
noncomputable section

def nodes (M : ℕ) (i : Fin M) : ℚ := i.val

theorem nodes_injective (M : ℕ) : Function.Injective (nodes M) := by
  intro i j hij
  apply Fin.ext
  exact Nat.cast_injective hij

def basis (M : ℕ) (i : Fin M) : ℚ[X] :=
  Lagrange.basis Finset.univ (nodes M) i

/-- Interpolation over polynomial-valued chunks uses only a fixed
rational matrix, lifted coefficientwise by `Polynomial.C`. -/
def interpolateChunks (M : ℕ) (values : Fin M → ℚ[X]) : (ℚ[X])[X] :=
  ∑ i, C (values i) * (basis M i).map C

theorem interpolateChunks_eval (M : ℕ) (values : Fin M → ℚ[X]) (j : Fin M) :
    (interpolateChunks M values).eval (C (nodes M j)) = values j := by
  classical
  unfold interpolateChunks
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map_apply]
  have hself : (basis M j).eval (nodes M j) = 1 :=
    Lagrange.eval_basis_self (nodes_injective M).injOn (Finset.mem_univ j)
  have hother : ∀ i : Fin M, i ≠ j → (basis M i).eval (nodes M j) = 0 := by
    intro i hij
    exact Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)
  rw [Finset.sum_eq_single j]
  · rw [hself]; simp
  · intro i hi hij
    rw [hother i hij]; simp
  · simp

theorem interpolateChunks_natDegree (M : ℕ) (hM : 0 < M) (values : Fin M → ℚ[X]) :
    (interpolateChunks M values).natDegree < M := by
  unfold interpolateChunks
  have hb : ∀ i : Fin M, (basis M i).natDegree = M-1 := by
    intro i
    simpa [basis] using Lagrange.natDegree_basis (nodes_injective M).injOn (Finset.mem_univ i)
  have h := Polynomial.natDegree_sum_le_of_forall_le
    (fun i : Fin M => C (values i)*(basis M i).map C) (s := Finset.univ)
    (n := M-1) (by
      intro i hi
      apply (Polynomial.natDegree_mul_le).trans
      simpa only [Polynomial.natDegree_C, zero_add, hb i] using
        (Polynomial.natDegree_map_le (p := basis M i) (f := C)))
  exact h.trans_lt (by omega)

/-- Exact chunk-valued interpolation, justified by uniqueness over the
integral domain `ℚ[X]`, rather than treating this ring as a field. -/
theorem interpolateChunks_correct (M : ℕ) (hM : 0 < M) (p : (ℚ[X])[X])
    (hp : p.natDegree < M) :
    interpolateChunks M (fun i => p.eval (C (nodes M i))) = p := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset (Fin M))
  · intro i hi j hj hij
    apply nodes_injective M
    exact Polynomial.C_injective hij
  · simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast interpolateChunks_natDegree M hM _)
  · simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hp)
  · intro i hi
    exact interpolateChunks_eval M _ i

/-- The literal contiguous coefficient chunk of length `h`. -/
def chunk {R : Type*} [CommRing R] (h i : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range h, C (f.coeff (i*h+j))*X^j

def blockPolynomial {R : Type*} [CommRing R] (k h : ℕ) (f : R[X]) : (R[X])[X] :=
  ∑ i ∈ Finset.range k, C (chunk h i f)*X^i

private theorem sum_range_blocks {R : Type*} [AddCommMonoid R]
    (k h : ℕ) (f : ℕ → R) :
    (∑ n ∈ Finset.range (k*h), f n) =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range h, f (i*h+j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Recombination of actual chunks recovers every input below the
padded length. -/
theorem blockPolynomial_recombine {R : Type*} [CommRing R] [Nontrivial R]
    (k h : ℕ) (f : R[X]) (hf : f.natDegree < k*h) :
    (blockPolynomial k h f).eval (X^h) = f := by
  conv_rhs => rw [f.as_sum_range_C_mul_X_pow' hf]
  rw [sum_range_blocks]
  unfold blockPolynomial chunk
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, mul_assoc, ← pow_add]
  congr 2
  ring

theorem chunk_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (h i : ℕ) (hh : 0 < h) (f : R[X]) :
    (chunk h i f).natDegree < h := by
  unfold chunk
  have hbound := Polynomial.natDegree_sum_le_of_forall_le
    (fun j => C (f.coeff (i*h+j))*X^j) (s := Finset.range h) (n := h-1) (by
      intro j hj
      apply (Polynomial.natDegree_mul_le).trans
      simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add] using
        (show j ≤ h-1 by have := Finset.mem_range.mp hj; omega))
  exact hbound.trans_lt (by omega)

theorem blockPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (k h : ℕ) (hk : 0 < k) (f : R[X]) :
    (blockPolynomial k h f).natDegree < k := by
  unfold blockPolynomial
  have hbound := Polynomial.natDegree_sum_le_of_forall_le
    (fun i => C (chunk h i f)*X^i) (s := Finset.range k) (n := k-1) (by
      intro i hi
      apply (Polynomial.natDegree_mul_le).trans
      simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add] using
        (show i ≤ k-1 by have := Finset.mem_range.mp hi; omega))
  exact hbound.trans_lt (by omega)

/-- The evaluated inputs to the recursive calls. -/
def evaluatedChunk (k h : ℕ) (f : ℚ[X]) (r : Fin (2*k-1)) : ℚ[X] :=
  (blockPolynomial k h f).eval (C (nodes (2*k-1) r))

theorem evaluatedChunk_natDegree (k h : ℕ) (hh : 0 < h) (f : ℚ[X]) (r : Fin (2*k-1)) :
    (evaluatedChunk k h f r).natDegree < h := by
  unfold evaluatedChunk blockPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hbound := Polynomial.natDegree_sum_le_of_forall_le
    (fun i => chunk h i f*(C (nodes (2*k-1) r))^i)
    (s := Finset.range k) (n := h-1) (by
      intro i hi
      apply (Polynomial.natDegree_mul_le).trans
      have hc : ((C (nodes (2*k-1) r) : ℚ[X])^i).natDegree = 0 := by
        rw [← Polynomial.C_pow]
        simp
      rw [hc, add_zero]
      exact Nat.le_pred_of_lt (chunk_natDegree h i hh f))
  exact hbound.trans_lt (by omega)

/-- The recursive exact Toom--Cook algorithm at padded length `k^s`.
Every recursive input has length at most `k^(s-1)`. -/
def multiply (k : ℕ) : ℕ → ℚ[X] → ℚ[X] → ℚ[X]
  | 0, f, g => C (f.coeff 0*g.coeff 0)
  | s+1, f, g =>
      (interpolateChunks (2*k-1) (fun r =>
        multiply k s (evaluatedChunk k (k^s) f r) (evaluatedChunk k (k^s) g r))).eval (X^(k^s))

theorem multiply_correct (k s : ℕ) (hk : 2 ≤ k) (f g : ℚ[X])
    (hf : f.natDegree < k^s) (hg : g.natDegree < k^s) :
    multiply k s f g = f*g := by
  induction s generalizing f g with
  | zero =>
    have hf0 : f.natDegree = 0 := by simpa using hf
    have hg0 : g.natDegree = 0 := by simpa using hg
    rw [Polynomial.eq_C_of_natDegree_eq_zero hf0, Polynomial.eq_C_of_natDegree_eq_zero hg0]
    simp [multiply]
  | succ s ih =>
    have hk0 : 0 < k := by omega
    have hh : 0 < k^s := pow_pos hk0 _
    have hM : 0 < 2*k-1 := by omega
    have hprod : (blockPolynomial k (k^s) f*blockPolynomial k (k^s) g).natDegree < 2*k-1 := by
      have h := Polynomial.natDegree_mul_le (p := blockPolynomial k (k^s) f)
        (q := blockPolynomial k (k^s) g)
      have hfa := blockPolynomial_natDegree k (k^s) hk0 f
      have hga := blockPolynomial_natDegree k (k^s) hk0 g
      omega
    have hvals : (fun r => multiply k s (evaluatedChunk k (k^s) f r)
        (evaluatedChunk k (k^s) g r)) =
      (fun r => (blockPolynomial k (k^s) f*blockPolynomial k (k^s) g).eval (C (nodes (2*k-1) r))) := by
      funext r
      rw [ih _ _ (evaluatedChunk_natDegree k (k^s) hh f r)
        (evaluatedChunk_natDegree k (k^s) hh g r)]
      exact Polynomial.eval_mul.symm
    simp only [multiply]
    rw [hvals, interpolateChunks_correct (2*k-1) hM _ hprod, Polynomial.eval_mul,
      blockPolynomial_recombine k (k^s) f (by simpa [pow_succ, mul_comm] using hf),
      blockPolynomial_recombine k (k^s) g (by simpa [pow_succ, mul_comm] using hg)]


/-- Fixed rational interpolation matrix. -/
def interpolationWeight (M : ℕ) (d r : Fin M) : ℚ := (basis M r).coeff d.val

/-- A common denominator depending only on the fixed interpolation arity. -/
def commonDenominator (M : ℕ) : ℕ :=
  ∏ d : Fin M, ∏ r : Fin M, (interpolationWeight M d r).den

def integerWeight (M : ℕ) (d r : Fin M) : ℤ :=
  ((commonDenominator M/(interpolationWeight M d r).den : ℕ) : ℤ)*
    (interpolationWeight M d r).num

theorem commonDenominator_pos (M : ℕ) : 0 < commonDenominator M := by
  unfold commonDenominator
  exact Finset.prod_pos fun d _ => Finset.prod_pos fun r _ => Rat.den_pos _

theorem denominator_dvd_common (M : ℕ) (d r : Fin M) :
    (interpolationWeight M d r).den ∣ commonDenominator M := by
  unfold commonDenominator
  exact dvd_trans
    (Finset.dvd_prod_of_mem (fun r => (interpolationWeight M d r).den) (Finset.mem_univ r))
    (Finset.dvd_prod_of_mem (fun d => ∏ r : Fin M, (interpolationWeight M d r).den)
      (Finset.mem_univ d))

theorem integerWeight_cast (M : ℕ) (d r : Fin M) :
    (integerWeight M d r : ℚ) = (commonDenominator M : ℚ)*interpolationWeight M d r := by
  unfold integerWeight
  symm
  calc
    (commonDenominator M : ℚ)*interpolationWeight M d r =
        ((commonDenominator M/(interpolationWeight M d r).den : ℕ) : ℚ)*
          (((interpolationWeight M d r).den : ℚ)*interpolationWeight M d r) := by
      rw [← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel (denominator_dvd_common M d r)]
    _ = _ := by rw [Rat.den_mul_eq_num, Int.cast_mul, Int.cast_natCast]

/-- This is the coefficientwise fixed rational interpolation operation. -/
theorem interpolateChunks_coeff (M : ℕ) (values : Fin M → ℚ[X]) (d : Fin M) :
    (interpolateChunks M values).coeff d.val =
      ∑ r : Fin M, C (interpolationWeight M d r)*values r := by
  unfold interpolateChunks interpolationWeight
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  ring

/-- Literal integer numerator before division by the fixed denominator. -/
def interpolationNumerator (M : ℕ) (values : Fin M → ℤ) (d : Fin M) : ℤ :=
  ∑ r : Fin M, integerWeight M d r*values r

theorem interpolationNumerator_cast (M : ℕ) (values : Fin M → ℤ) (d : Fin M) :
    (interpolationNumerator M values d : ℚ) =
      (commonDenominator M : ℚ)*
        ∑ r : Fin M, interpolationWeight M d r*(values r : ℚ) := by
  unfold interpolationNumerator
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integerWeight_cast]
  ring

/-- Exact division is justified only when the complete interpolation
coefficient equals an integer; individual summands need not be divisible. -/
theorem exact_interpolation_division (M : ℕ) (values : Fin M → ℤ) (d : Fin M) (z : ℤ)
    (hz : (z:ℚ) = ∑ r : Fin M, interpolationWeight M d r*(values r:ℚ)) :
    (commonDenominator M : ℤ) ∣ interpolationNumerator M values d ∧
      interpolationNumerator M values d/(commonDenominator M : ℤ) = z := by
  have hq : (interpolationNumerator M values d : ℚ) =
      (commonDenominator M : ℚ)*(z:ℚ) := by
    rw [interpolationNumerator_cast, hz]
  have hi : interpolationNumerator M values d = (commonDenominator M : ℤ)*z := by
    exact_mod_cast hq
  constructor
  · exact ⟨z, hi⟩
  · rw [hi, Int.mul_ediv_cancel_left z (Int.natCast_ne_zero.mpr (Nat.ne_of_gt (commonDenominator_pos M)))]

/-- Complete scalar product interpolation has integer coefficients for
integer inputs, supplying the premise needed by exact division. -/
theorem integer_product_interpolation (k : ℕ) (hk : 0 < k) (f g : ℤ[X])
    (hf : f.natDegree < k) (hg : g.natDegree < k) (d : Fin (2*k-1)) :
    (((f*g).coeff d.val : ℤ):ℚ) =
      ∑ r : Fin (2*k-1), interpolationWeight (2*k-1) d r*
        (f.eval (r.val:ℤ)*g.eval (r.val:ℤ) : ℤ) := by
  let fq := f.map (Int.castRingHom ℚ)
  let gq := g.map (Int.castRingHom ℚ)
  have hfq : fq.natDegree < k := Polynomial.natDegree_map_le.trans_lt hf
  have hgq : gq.natDegree < k := Polynomial.natDegree_map_le.trans_lt hg
  have heq : fq*gq = Lagrange.interpolate (Finset.univ : Finset (Fin (2*k-1)))
      (nodes (2*k-1)) (fun r => fq.eval (nodes (2*k-1) r)*gq.eval (nodes (2*k-1) r)) := by
    apply Lagrange.eq_interpolate_of_eval_eq
    · exact (nodes_injective _).injOn
    · simp only [Finset.card_univ, Fintype.card_fin]
      have hnd : (fq*gq).natDegree < 2*k-1 := by
        have h := Polynomial.natDegree_mul_le (p := fq) (q := gq)
        omega
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnd)
    · intro r hr; exact Polynomial.eval_mul
  have hc := congrArg (fun p : ℚ[X] => p.coeff d.val) heq
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at hc
  simp only [Polynomial.coeff_C_mul] at hc
  simpa [fq, gq, ← Polynomial.map_mul, Polynomial.coeff_map, Polynomial.coeff_C_mul,
    interpolationWeight, basis, nodes, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    mul_comm] using hc

/-- Every complete integer scalar-product interpolation numerator is
exactly divisible by the common fixed denominator. -/
theorem integer_product_exact_division (k : ℕ) (hk : 0 < k) (f g : ℤ[X])
    (hf : f.natDegree < k) (hg : g.natDegree < k) (d : Fin (2*k-1)) :
    interpolationNumerator (2*k-1)
      (fun r => f.eval (r.val:ℤ)*g.eval (r.val:ℤ)) d /
        (commonDenominator (2*k-1) : ℤ) = (f*g).coeff d.val :=
  (exact_interpolation_division (2*k-1) _ d _
    (integer_product_interpolation k hk f g hf hg d)).2


/-- Explicit coefficientwise integer division; no rational division is
charged as a unit-cost arithmetic primitive. -/
def divideCoefficients (D : ℤ) (p : ℤ[X]) : ℤ[X] :=
  ⟨p.toFinsupp.mapRange (fun z => z/D) (by simp)⟩

@[simp] theorem divideCoefficients_coeff (D : ℤ) (p : ℤ[X]) (j : ℕ) :
    (divideCoefficients D p).coeff j = p.coeff j/D := rfl

theorem divideCoefficients_exact (D : ℤ) (hD : D ≠ 0) (p : ℤ[X]) :
    divideCoefficients D (C D*p) = p := by
  ext j
  rw [divideCoefficients_coeff, Polynomial.coeff_C_mul, Int.mul_ediv_cancel_left _ hD]

def interpolationNumeratorPolynomial (M : ℕ) (values : Fin M → ℤ[X]) (d : Fin M) : ℤ[X] :=
  ∑ r, C (integerWeight M d r)*values r

def integerInterpolateCoefficient (M : ℕ) (values : Fin M → ℤ[X]) (d : Fin M) : ℤ[X] :=
  divideCoefficients (commonDenominator M) (interpolationNumeratorPolynomial M values d)

/-- For any genuine integer outer polynomial, the full interpolation
numerator is the fixed denominator times its desired coefficient. -/
theorem integer_interpolation_numerator (M : ℕ) (hM : 0 < M)
    (p : (ℤ[X])[X]) (hp : p.natDegree < M) (d : Fin M) :
    interpolationNumeratorPolynomial M
      (fun r => p.eval (C (r.val:ℤ))) d = C (commonDenominator M : ℤ)*p.coeff d.val := by
  let mapZQ : ℤ[X] →+* ℚ[X] := Polynomial.mapRingHom (Int.castRingHom ℚ)
  have hmap : Function.Injective mapZQ := Polynomial.map_injective _ Int.cast_injective
  apply hmap
  have hdeg : (p.map mapZQ).natDegree < M := Polynomial.natDegree_map_le.trans_lt hp
  have h := interpolateChunks_correct M hM (p.map mapZQ) hdeg
  have hc := congrArg (fun q : (ℚ[X])[X] => q.coeff d.val) h
  rw [interpolateChunks_coeff, Polynomial.coeff_map] at hc
  have hsum : (∑ r : Fin M, C (interpolationWeight M d r)*
      mapZQ (p.eval (C (r.val:ℤ)))) = mapZQ (p.coeff d.val) := by
    simpa [mapZQ, Polynomial.eval_map, Polynomial.eval₂_hom, nodes] using hc
  unfold interpolationNumeratorPolynomial
  simp only [map_sum, map_mul, mapZQ, Polynomial.coe_mapRingHom, Polynomial.map_C]
  calc
    (∑ r : Fin M, C ((integerWeight M d r : ℤ):ℚ)*
        (p.eval (C (r.val:ℤ))).map (Int.castRingHom ℚ)) =
      C (commonDenominator M : ℚ)*
        ∑ r : Fin M, C (interpolationWeight M d r)*mapZQ (p.eval (C (r.val:ℤ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [integerWeight_cast, Polynomial.C_mul]
      simp only [mapZQ, Polynomial.coe_mapRingHom, mul_assoc]
    _ = C (commonDenominator M : ℚ)*mapZQ (p.coeff d.val) := by rw [hsum]

theorem integerInterpolateCoefficient_correct (M : ℕ) (hM : 0 < M)
    (p : (ℤ[X])[X]) (hp : p.natDegree < M) (d : Fin M) :
    integerInterpolateCoefficient M (fun r => p.eval (C (r.val:ℤ))) d = p.coeff d.val := by
  unfold integerInterpolateCoefficient
  rw [integer_interpolation_numerator M hM p hp d]
  exact divideCoefficients_exact _ (Int.natCast_ne_zero.mpr (Nat.ne_of_gt (commonDenominator_pos M))) _

/-- Integer-valued evaluated chunks: nodes are literal distinct integers. -/
def evaluatedIntegerChunk (k h : ℕ) (f : ℤ[X]) (r : Fin (2*k-1)) : ℤ[X] :=
  (blockPolynomial k h f).eval (C (r.val:ℤ))

theorem evaluatedIntegerChunk_natDegree (k h : ℕ) (hh : 0 < h) (f : ℤ[X]) (r : Fin (2*k-1)) :
    (evaluatedIntegerChunk k h f r).natDegree < h := by
  unfold evaluatedIntegerChunk blockPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hbound := Polynomial.natDegree_sum_le_of_forall_le
    (fun i => chunk h i f*(C (r.val:ℤ))^i)
    (s := Finset.range k) (n := h-1) (by
      intro i hi
      apply (Polynomial.natDegree_mul_le).trans
      have hc : ((C (r.val:ℤ) : ℤ[X])^i).natDegree = 0 := by rw [← Polynomial.C_pow]; simp
      rw [hc, add_zero]
      exact Nat.le_pred_of_lt (chunk_natDegree h i hh f))
  exact hbound.trans_lt (by omega)

/-- The genuine integer recursive algorithm. Interpolation accumulates
integer numerators and then uses coefficientwise exact integer division. -/
def multiplyInteger (k : ℕ) : ℕ → ℤ[X] → ℤ[X] → ℤ[X]
  | 0, f, g => C (f.coeff 0*g.coeff 0)
  | s+1, f, g =>
      let values := fun r => multiplyInteger k s
        (evaluatedIntegerChunk k (k^s) f r) (evaluatedIntegerChunk k (k^s) g r)
      (∑ d : Fin (2*k-1), C (integerInterpolateCoefficient (2*k-1) values d)*X^d.val).eval (X^(k^s))

theorem multiplyInteger_correct (k s : ℕ) (hk : 2 ≤ k) (f g : ℤ[X])
    (hf : f.natDegree < k^s) (hg : g.natDegree < k^s) :
    multiplyInteger k s f g = f*g := by
  induction s generalizing f g with
  | zero =>
    have hf0 : f.natDegree = 0 := by simpa using hf
    have hg0 : g.natDegree = 0 := by simpa using hg
    rw [Polynomial.eq_C_of_natDegree_eq_zero hf0, Polynomial.eq_C_of_natDegree_eq_zero hg0]
    simp [multiplyInteger]
  | succ s ih =>
    have hk0 : 0 < k := by omega
    have hh : 0 < k^s := pow_pos hk0 _
    have hM : 0 < 2*k-1 := by omega
    let p := blockPolynomial k (k^s) f*blockPolynomial k (k^s) g
    have hp : p.natDegree < 2*k-1 := by
      change (blockPolynomial k (k^s) f*blockPolynomial k (k^s) g).natDegree < 2*k-1
      have h := Polynomial.natDegree_mul_le (p := blockPolynomial k (k^s) f)
        (q := blockPolynomial k (k^s) g)
      have hfa := blockPolynomial_natDegree k (k^s) hk0 f
      have hga := blockPolynomial_natDegree k (k^s) hk0 g
      omega
    have hvals : (fun r => multiplyInteger k s (evaluatedIntegerChunk k (k^s) f r)
        (evaluatedIntegerChunk k (k^s) g r)) = (fun r => p.eval (C (r.val:ℤ))) := by
      funext r
      rw [ih _ _ (evaluatedIntegerChunk_natDegree k (k^s) hh f r)
        (evaluatedIntegerChunk_natDegree k (k^s) hh g r)]
      exact Polynomial.eval_mul.symm
    simp only [multiplyInteger]
    rw [hvals]
    have hpoly : (∑ d : Fin (2*k-1),
        C (integerInterpolateCoefficient (2*k-1) (fun r => p.eval (C (r.val:ℤ))) d)*X^d.val) = p := by
      simp only [integerInterpolateCoefficient_correct (2*k-1) hM p hp]
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => C (p.coeff i)*X^i) (2*k-1)]
      exact (p.as_sum_range_C_mul_X_pow' hp).symm
    rw [hpoly]
    dsimp [p]
    rw [Polynomial.eval_mul,
      blockPolynomial_recombine k (k^s) f (by simpa [pow_succ, mul_comm] using hf),
      blockPolynomial_recombine k (k^s) g (by simpa [pow_succ, mul_comm] using hg)]


/-- A bitwise long-division state. All arithmetic in a step is shift,
addition, comparison and subtraction; no quotient operation occurs. -/
structure DivisionState where
  quotient : ℕ
  remainder : ℕ
  steps : ℕ

def bitsValue : List Bool → ℕ
  | [] => 0
  | b::bs => 2*bitsValue bs+b.toNat

def divideBits (D : ℕ) : List Bool → DivisionState
  | [] => ⟨0,0,0⟩
  | b::bs =>
      let child := divideBits D bs
      let v := 2*child.remainder+b.toNat
      if D ≤ v then ⟨2*child.quotient+1,v-D,child.steps+8⟩
      else ⟨2*child.quotient,v,child.steps+8⟩

/-- Each list bit executes at most eight elementary integer operations. -/
theorem divideBits_steps (D : ℕ) (bs : List Bool) :
    (divideBits D bs).steps = 8*bs.length := by
  induction bs with
  | nil => simp [divideBits]
  | cons b bs ih =>
    simp only [divideBits]
    split_ifs <;> simp only <;> rw [ih] <;> simp [Nat.mul_succ, Nat.add_comm]

/-- Exact quotient/remainder invariant of the division program. -/
theorem divideBits_correct (D : ℕ) (hD : 0 < D) (bs : List Bool) :
    bitsValue bs = D*(divideBits D bs).quotient+(divideBits D bs).remainder ∧
      (divideBits D bs).remainder < D := by
  induction bs with
  | nil => simp [divideBits, bitsValue, hD]
  | cons b bs ih =>
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    simp only [divideBits, bitsValue]
    split_ifs with h
    · simp only
      have hsub : 2*(divideBits D bs).remainder+b.toNat-D+D =
          2*(divideBits D bs).remainder+b.toNat := Nat.sub_add_cancel h
      constructor <;> nlinarith [ih.1, ih.2]
    · simp only
      constructor <;> nlinarith [ih.1, ih.2]

theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
    have hh : n=0 → b=true := by
      intro h
      subst n
      cases b <;> simp_all
    rw [Nat.bits_append_bit n b hh]
    simp only [bitsValue, ih, Nat.bit_val]

def binaryDivide (D n : ℕ) : DivisionState := divideBits D n.bits

theorem binaryDivide_correct (D n : ℕ) (hD : 0 < D) :
    (binaryDivide D n).quotient = n/D ∧ (binaryDivide D n).remainder = n%D := by
  have h := divideBits_correct D hD n.bits
  rw [bitsValue_bits] at h
  have hh := (Nat.div_mod_unique hD).2 (show
      (binaryDivide D n).remainder+D*(binaryDivide D n).quotient=n ∧
        (binaryDivide D n).remainder<D by
      constructor
      · dsimp [binaryDivide]; nlinarith [h.1]
      · exact h.2)
  exact ⟨hh.1.symm,hh.2.symm⟩

/-- Division by the fixed denominator costs linearly many word steps
in the actual input's binary length, rather than one unit-cost division. -/
theorem binaryDivide_steps (D n : ℕ) : (binaryDivide D n).steps = 8*n.size := by
  rw [binaryDivide, divideBits_steps, Nat.size_eq_bits_len]

/-- Quotient and remainder registers fit in the original magnitude
budget. The fixed divisor contributes its own constant register width. -/
theorem binaryDivide_registers (D n : ℕ) (hD : 0 < D) :
    (binaryDivide D n).quotient ≤ n ∧ (binaryDivide D n).remainder ≤ n := by
  rw [(binaryDivide_correct D n hD).1, (binaryDivide_correct D n hD).2]
  exact ⟨Nat.div_le_self _ _, Nat.mod_le _ _⟩


/-- Signed refinement of exact division, using the proved bitwise
natural-number routine and only a final sign correction. -/
def signedBinaryDivide (D : ℕ) (z : ℤ) : ℤ :=
  if z < 0 then -((binaryDivide D z.natAbs).quotient:ℤ)
  else ((binaryDivide D z.natAbs).quotient:ℤ)

theorem signedBinaryDivide_exact (D : ℕ) (hD : 0 < D) (z w : ℤ)
    (hz : z=(D:ℤ)*w) : signedBinaryDivide D z = w := by
  have hq : (binaryDivide D z.natAbs).quotient = w.natAbs := by
    rw [(binaryDivide_correct D z.natAbs hD).1, hz, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_div_right _ hD
  unfold signedBinaryDivide
  rw [hq]
  split_ifs with hneg
  · have hd : (0:ℤ)<D := by exact_mod_cast hD
    have hw : w<0 := by nlinarith [hz]
    rw [Int.natCast_natAbs, abs_of_neg hw]
    ring
  · have hd : (0:ℤ)<D := by exact_mod_cast hD
    have hw : 0≤w := by nlinarith [hz]
    rw [Int.natCast_natAbs, abs_of_nonneg hw]

/-- Each genuine interpolation quotient has a bitwise implementation
with a proved linear binary-length step count. -/
theorem interpolation_binary_division (M : ℕ) (values : Fin M → ℤ) (d : Fin M) (z : ℤ)
    (hz : (z:ℚ)=∑r : Fin M, interpolationWeight M d r*(values r:ℚ)) :
    signedBinaryDivide (commonDenominator M) (interpolationNumerator M values d)=z ∧
    (binaryDivide (commonDenominator M) (interpolationNumerator M values d).natAbs).steps =
      8*(interpolationNumerator M values d).natAbs.size := by
  have hq : (interpolationNumerator M values d : ℚ)=(commonDenominator M:ℚ)*(z:ℚ) := by
    rw [interpolationNumerator_cast, hz]
  have hi : interpolationNumerator M values d=(commonDenominator M:ℤ)*z := by exact_mod_cast hq
  exact ⟨signedBinaryDivide_exact _ (commonDenominator_pos M) _ _ hi, binaryDivide_steps _ _⟩

/-- Absolute-row-sum bound, also valid for every partial accumulator. -/
theorem integer_linear_combination_bound {α : Type*} (s : Finset α) (w v : α → ℤ) (A : ℤ)
    (hv : ∀ i ∈ s, |v i|≤A) :
    |∑i∈s,w i*v i|≤(∑i∈s,|w i|)*A := by
  calc
    |∑i∈s,w i*v i|≤∑i∈s,|w i*v i| := Finset.abs_sum_le_sum_abs _ _
    _≤∑i∈s,|w i| *A := Finset.sum_le_sum (fun i hi => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv i hi) (abs_nonneg _))
    _=_ := (Finset.sum_mul _ _ _).symm

/-- A fixed arity-dependent bound for every evaluation/interpolation
row; its exact integer value is never normalized. -/
def growthConstant (k : ℕ) : ℕ := 1+
  (∑r : Fin (2*k-1), ∑i∈Finset.range k, (r.val^i : ℕ))+
  (∑d : Fin (2*k-1), ∑r : Fin (2*k-1), (integerWeight (2*k-1) d r).natAbs)

theorem growthConstant_pos (k : ℕ) : 0<growthConstant k := by unfold growthConstant; omega

theorem evaluation_row_le_growth (k : ℕ) (r : Fin (2*k-1)) :
    (∑i∈Finset.range k, |(r.val:ℤ)^i|) ≤ (growthConstant k:ℤ) := by
  have h : (∑i∈Finset.range k, r.val^i) ≤
      ∑r : Fin (2*k-1), ∑i∈Finset.range k, r.val^i :=
    Finset.single_le_sum (f := fun r : Fin (2*k-1) => ∑i∈Finset.range k,r.val^i)
      (a := r) (fun r hr => Nat.zero_le _) (Finset.mem_univ r)
  have hh : (∑i∈Finset.range k,r.val^i)≤growthConstant k := by unfold growthConstant; omega
  exact_mod_cast (by simpa using hh : (∑i∈Finset.range k,r.val^i)≤growthConstant k)

theorem interpolation_row_le_growth (k : ℕ) (d : Fin (2*k-1)) :
    (∑r : Fin (2*k-1), |integerWeight (2*k-1) d r|)≤(growthConstant k:ℤ) := by
  have h : (∑r : Fin (2*k-1), (integerWeight (2*k-1) d r).natAbs) ≤
      ∑d : Fin (2*k-1), ∑r : Fin (2*k-1), (integerWeight (2*k-1) d r).natAbs :=
    Finset.single_le_sum (f := fun d : Fin (2*k-1) => ∑r : Fin (2*k-1),(integerWeight (2*k-1) d r).natAbs)
      (a := d) (fun d hd => Nat.zero_le _) (Finset.mem_univ d)
  have hh : (∑r : Fin (2*k-1),(integerWeight (2*k-1) d r).natAbs)≤growthConstant k := by
    unfold growthConstant; omega
  have hhcast : ((∑r : Fin (2*k-1),(integerWeight (2*k-1) d r).natAbs):ℤ)≤(growthConstant k:ℤ) := by
    exact_mod_cast hh
  simpa only [Nat.cast_sum,Int.natCast_natAbs] using hhcast

theorem chunk_coeff (h i : ℕ) (f : ℤ[X]) (j : ℕ) :
    (chunk h i f).coeff j = if j<h then f.coeff (i*h+j) else 0 := by
  simp [chunk, Polynomial.finsetSum_coeff]

def CoeffBound (p : ℤ[X]) (A : ℤ) : Prop := ∀j,|p.coeff j|≤A

theorem evaluatedIntegerChunk_bound (k h : ℕ) (f : ℤ[X]) (r : Fin (2*k-1)) (A : ℤ)
    (hA : 0≤A) (hf : CoeffBound f A) :
    CoeffBound (evaluatedIntegerChunk k h f r) ((growthConstant k:ℤ)*A) := by
  intro j
  unfold evaluatedIntegerChunk blockPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, ←Polynomial.C_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C]
  have hrow := integer_linear_combination_bound (Finset.range k)
    (fun i => (r.val:ℤ)^i) (fun i => (chunk h i f).coeff j) A (by
      intro i hi; rw [chunk_coeff]; split_ifs <;> simp_all [CoeffBound])
  have hr := mul_le_mul_of_nonneg_right (evaluation_row_le_growth k r) hA
  calc
    |∑i∈Finset.range k,(chunk h i f).coeff j*(r.val:ℤ)^i| =
        |∑i∈Finset.range k,(r.val:ℤ)^i*(chunk h i f).coeff j| := by congr 1; apply Finset.sum_congr rfl; intros; ring
    _≤_ := hrow
    _≤_ := hr

theorem product_coefficient_bound (f g : ℤ[X]) (n : ℕ) (A : ℤ) (hA : 0≤A)
    (hfdeg : f.natDegree<n) (hf : CoeffBound f A) (hg : CoeffBound g A) :
    CoeffBound (f*g) ((n:ℤ)*A^2) := by
  intro j
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun x => f.coeff x.1*g.coeff x.2) j]
  let s := (Finset.range (j+1)).filter (fun i=>i<n)
  have hs : s.card≤n := by
    calc
      s.card≤(Finset.range n).card := Finset.card_le_card (by
        intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
      _=n := Finset.card_range n
  calc
    |∑i∈Finset.range (j+1),f.coeff i*g.coeff (j-i)|≤
        ∑i∈Finset.range (j+1),|f.coeff i*g.coeff (j-i)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑i∈Finset.range (j+1),if i<n then A^2 else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with hin
      · rw [abs_mul,pow_two]; exact mul_le_mul (hf i) (hg (j-i)) (abs_nonneg _) hA
      · have hfi : f.coeff i=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hfi]
    _=(s.card:ℤ)*A^2 := by rw [←Finset.sum_filter]; simp [s]
    _≤(n:ℤ)*A^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg A)

theorem interpolationNumeratorPolynomial_bound (k : ℕ) (values : Fin (2*k-1)→ℤ[X])
    (d : Fin (2*k-1)) (A : ℤ) (hA : 0≤A) (hv : ∀r,CoeffBound (values r) A) :
    CoeffBound (interpolationNumeratorPolynomial (2*k-1) values d) ((growthConstant k:ℤ)*A) := by
  intro j
  unfold interpolationNumeratorPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  exact (integer_linear_combination_bound Finset.univ _ _ A (fun r _=>hv r j)).trans
    (mul_le_mul_of_nonneg_right (interpolation_row_le_growth k d) hA)



/-- Every partial interpolation accumulator obeys the same row budget
as the complete numerator, even when cancellation occurs in the latter. -/
theorem partialInterpolation_bound (k : ℕ) (values : Fin (2*k-1)→ℤ[X])
    (d : Fin (2*k-1)) (T : Finset (Fin (2*k-1))) (A : ℤ)
    (hA : 0≤A) (hv : ∀r,CoeffBound (values r) A) :
    CoeffBound (∑r∈T,C (integerWeight (2*k-1) d r)*values r) ((growthConstant k:ℤ)*A) := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  have hrow : (∑r∈T,|integerWeight (2*k-1) d r|)≤(growthConstant k:ℤ) := by
    apply le_trans _ (interpolation_row_le_growth k d)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun r _ _=>abs_nonneg _)
  exact (integer_linear_combination_bound T _ _ A (fun r _=>hv r j)).trans
    (mul_le_mul_of_nonneg_right hrow hA)

/-- Every partial evaluation dot product has the same fixed row budget. -/
theorem partialEvaluation_bound (k h : ℕ) (f : ℤ[X]) (r : Fin (2*k-1))
    (T : Finset ℕ) (hT : T⊆Finset.range k) (A : ℤ) (hA : 0≤A) (hf : CoeffBound f A) :
    CoeffBound (∑i∈T,C ((r.val:ℤ)^i)*chunk h i f) ((growthConstant k:ℤ)*A) := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  have hrow : (∑i∈T,|(r.val:ℤ)^i|)≤(growthConstant k:ℤ) := by
    apply le_trans _ (evaluation_row_le_growth k r)
    exact Finset.sum_le_sum_of_subset_of_nonneg hT (fun i _ _=>abs_nonneg _)
  exact (integer_linear_combination_bound T _ _ A (by
    intro i hi;rw [chunk_coeff];split_ifs <;>simp_all [CoeffBound])).trans
      (mul_le_mul_of_nonneg_right hrow hA)

/-- Literal integer loop instrumentation. Primitive integer additions
and constant multiplications are counted separately from division steps. -/
structure Counted (α : Type*) where
  value : α
  operations : ℕ

namespace Counted

def scalarAdd {R : Type*} [Add R] (x y : R) : Counted R := ⟨x+y,1⟩
def scalarMul {R : Type*} [Mul R] (x y : R) : Counted R := ⟨x*y,1⟩
def sequence {α β : Type*} (f : α→Counted β) : List α→Counted (List β)
  | [] => ⟨[],0⟩
  | x::xs => let a:=f x; let b:=sequence f xs; ⟨a.value::b.value,a.operations+b.operations⟩

theorem sequence_value {α β : Type*} (f : α→Counted β) (xs : List α) :
    (sequence f xs).value=xs.map (fun x=>(f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sequence,ih]

theorem sequence_operations {α β : Type*} (f : α→Counted β) (xs : List α) (c : ℕ)
    (h : ∀x∈xs,(f x).operations=c) : (sequence f xs).operations=c*xs.length := by
  induction xs with
  | nil => simp [sequence]
  | cons x xs ih =>
    rw [sequence,List.length_cons]
    dsimp
    rw [h x (by simp),ih (fun y hy=>h y (by simp [hy]))]
    simp [Nat.mul_succ,Nat.add_comm]

theorem sequence_operations_sum {α β : Type*} (f : α→Counted β) (xs : List α) :
    (sequence f xs).operations=(xs.map (fun x=>(f x).operations)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sequence,ih]
end Counted

def dotCounted {R ι : Type*} [Semiring R] (w a : ι→R) : List ι→Counted R
  | [] => ⟨0,0⟩
  | i::is =>
    let product:=Counted.scalarMul (w i) (a i)
    let tail:=dotCounted w a is
    let total:=Counted.scalarAdd product.value tail.value
    ⟨total.value,product.operations+tail.operations+total.operations⟩

theorem dotCounted_value {R ι : Type*} [Semiring R] (w a : ι→R) (xs : List ι) :
    (dotCounted w a xs).value=(xs.map (fun i=>w i*a i)).sum := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [dotCounted,Counted.scalarMul,Counted.scalarAdd,ih]

theorem dotCounted_operations {R ι : Type*} [Semiring R] (w a : ι→R) (xs : List ι) :
    (dotCounted w a xs).operations=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [dotCounted,Counted.scalarMul,Counted.scalarAdd,ih]; omega

def linearTransformCounted {R : Type*} [Semiring R] (rows cols n : ℕ)
    (w : Fin rows→Fin cols→R) (a : Fin cols→Fin n→R) : Counted (List (List R)) :=
  Counted.sequence (fun r : Fin rows=>Counted.sequence (fun j : Fin n=>
    dotCounted (w r) (fun i=>a i j) (List.ofFn (id : Fin cols→Fin cols)))
      (List.ofFn (id : Fin n→Fin n))) (List.ofFn (id : Fin rows→Fin rows))

theorem linearTransformCounted_value {R : Type*} [Semiring R] (rows cols n : ℕ)
    (w : Fin rows→Fin cols→R) (a : Fin cols→Fin n→R) :
    (linearTransformCounted rows cols n w a).value=
      List.ofFn (fun r=>List.ofFn (fun j=>∑i,w r i*a i j)) := by
  simp [linearTransformCounted,Counted.sequence_value,dotCounted_value,
    List.sum_ofFn]

theorem linearTransformCounted_operations {R : Type*} [Semiring R] (rows cols n : ℕ)
    (w : Fin rows→Fin cols→R) (a : Fin cols→Fin n→R) :
    (linearTransformCounted rows cols n w a).operations=2*cols*n*rows := by
  unfold linearTransformCounted
  rw [Counted.sequence_operations _ _ (2*cols*n)]
  · simp
  · intro r hr
    rw [Counted.sequence_operations _ _ (2*cols)]
    · simp
    · intro j hj; simp [dotCounted_operations]

theorem numerator_coefficient_bridge (M n : ℕ) (values : Fin M→ℤ[X]) :
    (linearTransformCounted M M n (integerWeight M) (fun r j=>(values r).coeff j.val)).value=
      List.ofFn (fun d=>List.ofFn (fun j : Fin n=>
        (interpolationNumeratorPolynomial M values d).coeff j.val)) := by
  rw [linearTransformCounted_value]
  congr 1
  funext d
  congr 1
  funext j
  simp [interpolationNumeratorPolynomial,Polynomial.finsetSum_coeff]

theorem evaluation_coefficient_bridge (k h : ℕ) (f : ℤ[X]) :
    (linearTransformCounted (2*k-1) k h (fun r i=>(r.val:ℤ)^i.val)
      (fun i j=>f.coeff (i.val*h+j.val))).value=
      List.ofFn (fun r=>List.ofFn (fun j : Fin h=>(evaluatedIntegerChunk k h f r).coeff j.val)) := by
  rw [linearTransformCounted_value]
  congr 1
  funext r
  congr 1
  funext j
  unfold evaluatedIntegerChunk blockPolynomial
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,←Polynomial.C_pow,Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C]
  simp only [chunk_coeff,if_pos j.isLt]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ=>(r.val:ℤ)^i*f.coeff (i*h+j.val)) k]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Counted execution of every natural long-division coefficient call. -/
def divideVectorCounted (D n : ℕ) (a : Fin n→ℕ) : Counted (List ℕ) :=
  Counted.sequence (fun j : Fin n=>let d:=binaryDivide D (a j); ⟨d.quotient,d.steps⟩)
    (List.ofFn (id : Fin n→Fin n))

theorem divideVector_steps (D n : ℕ) (a : Fin n→ℕ) :
    (divideVectorCounted D n a).operations=8*∑j,(a j).size := by
  simp [divideVectorCounted,Counted.sequence_operations_sum,binaryDivide_steps,List.sum_ofFn,Finset.mul_sum]

theorem divideVector_steps_le (D n B : ℕ) (a : Fin n→ℕ) (ha : ∀j,(a j).size≤B) :
    (divideVectorCounted D n a).operations≤8*n*B := by
  rw [divideVector_steps]
  calc
    8*∑j,(a j).size≤8*∑_j : Fin n,B := Nat.mul_le_mul_left 8 (Finset.sum_le_sum (fun j _=>ha j))
    _=8*n*B := by simp; ring


/-- Every actual downward path is a sequence of the concrete evaluated
chunk maps. Its coefficient growth is exponential only in the depth. -/
def evaluationPath (k : ℕ) (f : ℤ[X]) : List (ℕ×Fin (2*k-1))→ℤ[X]
  | [] => f
  | (h,r)::xs => evaluationPath k (evaluatedIntegerChunk k h f r) xs

theorem evaluationPath_bound (k : ℕ) (f : ℤ[X]) (xs : List (ℕ×Fin (2*k-1))) (A : ℤ)
    (hA : 0≤A) (hf : CoeffBound f A) :
    CoeffBound (evaluationPath k f xs) ((growthConstant k:ℤ)^xs.length*A) := by
  induction xs generalizing f A with
  | nil => simpa [evaluationPath] using hf
  | cons x xs ih =>
    have hC : (0:ℤ)≤growthConstant k := by positivity
    have h := ih (evaluatedIntegerChunk k x.1 f x.2) ((growthConstant k:ℤ)*A)
      (mul_nonneg hC hA) (evaluatedIntegerChunk_bound k x.1 f x.2 A hA hf)
    simpa only [evaluationPath,List.length_cons,pow_succ,mul_assoc,mul_comm,mul_left_comm] using h


/-- At every recursive node, returned products are bounded using their
proved exact semantics; interpolation numerator bounds are not recursively
squared. -/
theorem recursive_numerator_bound (k s : ℕ) (hk : 2≤k) (f g : ℤ[X]) (A : ℤ)
    (hA : 0≤A) (hf : CoeffBound f A) (hg : CoeffBound g A) (d : Fin (2*k-1)) :
    CoeffBound (interpolationNumeratorPolynomial (2*k-1) (fun r=>multiplyInteger k s
      (evaluatedIntegerChunk k (k^s) f r) (evaluatedIntegerChunk k (k^s) g r)) d)
      ((k:ℤ)^s*(growthConstant k:ℤ)^3*A^2) := by
  have hh : 0<k^s := pow_pos (by omega) _
  have hC : (0:ℤ)≤growthConstant k := by positivity
  have hca : 0≤(growthConstant k:ℤ)*A := mul_nonneg hC hA
  have hval : ∀r,CoeffBound (multiplyInteger k s (evaluatedIntegerChunk k (k^s) f r)
      (evaluatedIntegerChunk k (k^s) g r)) ((k^s:ℕ)*( (growthConstant k:ℤ)*A)^2) := by
    intro r
    rw [multiplyInteger_correct k s hk _ _
      (evaluatedIntegerChunk_natDegree k (k^s) hh f r)
      (evaluatedIntegerChunk_natDegree k (k^s) hh g r)]
    exact product_coefficient_bound _ _ (k^s) _ hca
      (evaluatedIntegerChunk_natDegree k (k^s) hh f r)
      (evaluatedIntegerChunk_bound k (k^s) f r A hA hf)
      (evaluatedIntegerChunk_bound k (k^s) g r A hA hg)
  have h := interpolationNumeratorPolynomial_bound k _ d _ (by positivity) hval
  convert h using 1
  push_cast
  ring

/-- Explicit bit-length estimate for every fixed product of powers. -/
theorem size_powerProduct_bound (k C A s d e : ℕ) :
    (k^s*C^d*A^e).size≤k.size*s+C.size*d+A.size*e+1 := by
  have hk : k≤2^k.size := (Nat.lt_size_self k).le
  have hC : C≤2^C.size := (Nat.lt_size_self C).le
  have hA : A≤2^A.size := (Nat.lt_size_self A).le
  have hp : k^s*C^d*A^e≤2^(k.size*s+C.size*d+A.size*e) := by
    calc
      k^s*C^d*A^e≤(2^k.size)^s*(2^C.size)^d*(2^A.size)^e :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hk _) (Nat.pow_le_pow_left hC _))
          (Nat.pow_le_pow_left hA _)
      _=_ := by rw [←pow_mul,←pow_mul,←pow_mul,←pow_add,←pow_add]
  apply Nat.size_le.mpr
  exact hp.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- Coefficients at every actual recursive numerator path fit in a
linear-in-depth bit budget. Arity-dependent constants are fixed. -/
theorem recursive_numerator_path_bits (k s : ℕ) (hk : 2≤k) (f g : ℤ[X])
    (xs ys : List (ℕ×Fin (2*k-1))) (hlen : ys.length=xs.length) (A : ℕ)
    (hf : CoeffBound f A) (hg : CoeffBound g A) (d : Fin (2*k-1)) (j : ℕ) :
    ((interpolationNumeratorPolynomial (2*k-1) (fun r=>multiplyInteger k s
      (evaluatedIntegerChunk k (k^s) (evaluationPath k f xs) r)
      (evaluatedIntegerChunk k (k^s) (evaluationPath k g ys) r)) d).coeff j).natAbs.size ≤
      k.size*s+(growthConstant k).size*(2*xs.length+3)+A.size*2+1 := by
  have hfx := evaluationPath_bound k f xs A (by positivity) hf
  have hgy := evaluationPath_bound k g ys A (by positivity) hg
  rw [hlen] at hgy
  have h := recursive_numerator_bound k s hk (evaluationPath k f xs) (evaluationPath k g ys)
    ((growthConstant k:ℤ)^xs.length*A) (by positivity) hfx hgy d j
  have heq : (k:ℤ)^s*(growthConstant k:ℤ)^3*((growthConstant k:ℤ)^xs.length*A)^2 =
      ((k^s*(growthConstant k)^(2*xs.length+3)*A^2:ℕ):ℤ) := by
    push_cast
    rw [mul_pow,←pow_mul]
    rw [show 2*xs.length+3=3+xs.length*2 by omega,pow_add]
    ring
  rw [heq] at h
  have hn : ((interpolationNumeratorPolynomial (2*k-1) (fun r=>multiplyInteger k s
      (evaluatedIntegerChunk k (k^s) (evaluationPath k f xs) r)
      (evaluatedIntegerChunk k (k^s) (evaluationPath k g ys) r)) d).coeff j).natAbs ≤
      k^s*(growthConstant k)^(2*xs.length+3)*A^2 := by
    have hc : (((interpolationNumeratorPolynomial (2*k-1) (fun r=>multiplyInteger k s
      (evaluatedIntegerChunk k (k^s) (evaluationPath k f xs) r)
      (evaluatedIntegerChunk k (k^s) (evaluationPath k g ys) r)) d).coeff j).natAbs:ℤ) ≤ ((k^s*(growthConstant k)^(2*xs.length+3)*A^2:ℕ):ℤ) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hc
  exact (Nat.size_le_size hn).trans (size_powerProduct_bound k (growthConstant k) A s (2*xs.length+3) 2)

/-- A conservative literal node schedule: two evaluation coefficient
matrices, one interpolation numerator matrix, coefficient quotient slots,
and writes/recombination. A quotient slot expands to at most `8*B` word
steps for a B-bit numerator, by `divideVector_steps_le`. -/
def localSchedule (k h : ℕ) : ℕ :=
  4*k*h*(2*k-1)+4*(2*k-1)*(2*k-1)*h+8*(2*k-1)*h+1

def overheadFactor (k : ℕ) : ℕ :=
  4*k*(2*k-1)+4*(2*k-1)*(2*k-1)+8*(2*k-1)+1

theorem localSchedule_le (k h : ℕ) (hk : 2≤k) (hh : 0<h) :
    localSchedule k h≤overheadFactor k*k*h := by
  have heq : localSchedule k h+h=overheadFactor k*h+1 := by
    unfold localSchedule overheadFactor
    ring
  calc
    localSchedule k h≤overheadFactor k*h := by omega
    _≤overheadFactor k*k*h := by
      have hh := Nat.mul_le_mul_right (overheadFactor k*h) (show 1≤k by omega)
      simpa only [Nat.one_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh


/-- A finite memoized execution: each child result is tabulated in an
array once, and interpolation reads the stored values. Its operation slots
include the concrete linear loops certified above. -/
def multiplyCounted (k : ℕ) : ℕ→ℤ[X]→ℤ[X]→Counted ℤ[X]
  | 0,f,g => ⟨C (f.coeff 0*g.coeff 0),1⟩
  | s+1,f,g =>
    let children:=Array.ofFn (fun r : Fin (2*k-1)=>multiplyCounted k s
      (evaluatedIntegerChunk k (k^s) f r) (evaluatedIntegerChunk k (k^s) g r))
    let child:=fun r : Fin (2*k-1)=>children[r.val]'(by dsimp [children]; simpa only [Array.size_ofFn] using r.isLt)
    let values:=fun r=>(child r).value
    ⟨(∑d : Fin (2*k-1),C (integerInterpolateCoefficient (2*k-1) values d)*X^d.val).eval (X^(k^s)),
      (∑r : Fin (2*k-1),(child r).operations)+localSchedule k (k^s)⟩

theorem multiplyCounted_value (k s : ℕ) (f g : ℤ[X]) :
    (multiplyCounted k s f g).value=multiplyInteger k s f g := by
  induction s generalizing f g with
  | zero => rfl
  | succ s ih =>
    simp only [multiplyCounted,multiplyInteger,Array.getElem_ofFn]
    simp only [ih]

/-- Arithmetic recurrence at padded length `k^s`. Each node executes
`2k-1` recursive products and a fixed linear amount of coefficient work. -/
def recurrence (r k a : ℕ) : ℕ → ℕ
  | 0 => 1
  | s+1 => r*recurrence r k a s+a*k^(s+1)

theorem recurrence_sharp (r k a : ℕ) (hk : 3*k ≤ 2*r) (s : ℕ) :
    recurrence r k a s+2*a*k^s ≤ (2*a+1)*r^s := by
  induction s with
  | zero => simp [recurrence]; omega
  | succ s ih =>
    calc
      recurrence r k a (s+1)+2*a*k^(s+1) =
          r*recurrence r k a s+(3*k)*(a*k^s) := by rw [recurrence, pow_succ]; ring
      _ ≤ r*recurrence r k a s+(2*r)*(a*k^s) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (a*k^s) hk) _
      _ = r*(recurrence r k a s+2*a*k^s) := by ring
      _ ≤ r*((2*a+1)*r^s) := Nat.mul_le_mul_left r ih
      _ = (2*a+1)*r^(s+1) := by rw [pow_succ]; ring


/-- The memoized recursive schedule is bounded by the derived
fixed-arity recurrence. No recurrence is assumed as an algorithm axiom. -/
theorem multiplyCounted_operations (k s : ℕ) (hk : 2≤k) (f g : ℤ[X]) :
    (multiplyCounted k s f g).operations≤recurrence (2*k-1) k (overheadFactor k) s := by
  induction s generalizing f g with
  | zero => rfl
  | succ s ih =>
    simp only [multiplyCounted,Array.getElem_ofFn,recurrence]
    calc
      (∑r : Fin (2*k-1),(multiplyCounted k s (evaluatedIntegerChunk k (k^s) f r)
          (evaluatedIntegerChunk k (k^s) g r)).operations)+localSchedule k (k^s) ≤
        (∑_r : Fin (2*k-1),recurrence (2*k-1) k (overheadFactor k) s)+
          overheadFactor k*k*(k^s) := by
        exact Nat.add_le_add (Finset.sum_le_sum (fun r _=>ih _ _))
          (localSchedule_le k (k^s) hk (pow_pos (by omega) _))
      _=(2*k-1)*recurrence (2*k-1) k (overheadFactor k) s+
          overheadFactor k*k^(s+1) := by simp [pow_succ]; ring

theorem toom_recurrence_bound (k a : ℕ) (hk : 2 ≤ k) (s : ℕ) :
    recurrence (2*k-1) k a s ≤ (2*a+1)*(2*k)^s := by
  have h := recurrence_sharp (2*k-1) k a (by omega) s
  calc
    recurrence (2*k-1) k a s ≤ (2*a+1)*(2*k-1)^s := by omega
    _ ≤ (2*a+1)*(2*k)^s :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

theorem padded_power_identity (B s : ℕ) (hB : 0 < B) :
    (((2:ℝ)^B)^s)^(1+1/(B:ℝ)) = (2*(2:ℝ)^B)^s := by
  have hkpos : (0:ℝ)<2^B := pow_pos (by norm_num) _
  rw [← Real.rpow_pow_comm hkpos.le, Real.rpow_add hkpos, Real.rpow_one]
  rw [one_div, Real.pow_rpow_inv_natCast (by norm_num) (Nat.ne_of_gt hB)]
  ring

theorem toom_recurrence_rpow (B s a : ℕ) (hB : 0 < B) :
    (recurrence (2*(2^B)-1) (2^B) a s : ℝ) ≤
      (2*a+1:ℝ)*((((2^B)^s:ℕ):ℝ)^(1+1/(B:ℝ))) := by
  have hk : 2 ≤ 2^B := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^B := Nat.pow_le_pow_right (by omega) hB
  have hc : (recurrence (2*(2^B)-1) (2^B) a s : ℝ) ≤ (2*a+1:ℝ)*(2*(2:ℝ)^B)^s := by
    exact_mod_cast toom_recurrence_bound (2^B) a hk s
  rw [← padded_power_identity B s hB] at hc
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hc


theorem two_le_two_pow (B : ℕ) (hB : 0<B) : 2≤2^B := by
  calc
    2=2^1 := by norm_num
    _≤2^B := Nat.pow_le_pow_right (by omega) hB

/-- Symbolic fixed arity: no reduction of the enormous power is performed. -/
theorem fixed_exponent_recurrence (s a : ℕ) :
    (recurrence (2*(2^100000000)-1) (2^100000000) a s : ℝ) ≤
      (2*a+1:ℝ)*((((2^100000000)^s:ℕ):ℝ)^(1.00000001:ℝ)) := by
  have h := toom_recurrence_rpow 100000000 s a (by norm_num)
  have he : (1:ℝ)+1/(100000000:ℕ) = 1.00000001 := by norm_num
  rwa [he] at h


/-- Padding arbitrary positive lengths to the next arity power costs
only a fixed factor `k`; this includes small lengths. -/
theorem padded_length_bounds (k q : ℕ) (hk : 2≤k) (hq : 0<q) :
    q<k^(Nat.log k q+1) ∧ k^(Nat.log k q+1)≤k*q := by
  constructor
  · exact Nat.lt_pow_succ_log_self (by omega) q
  · rw [pow_succ']
    exact Nat.mul_le_mul_left k (Nat.pow_log_le_self k (Nat.ne_of_gt hq))

/-- The proved memoized arithmetic-slot bound at the symbolic fixed
arity. Divisions expand through the separate bit-length-dependent bound. -/
theorem multiplyCounted_fixed_bound (s : ℕ) (f g : ℤ[X]) :
    ((multiplyCounted (2^100000000) s f g).operations:ℝ) ≤
      (2*(overheadFactor (2^100000000))+1:ℝ)*
        ((((2^100000000)^s:ℕ):ℝ)^(1.00000001:ℝ)) := by
  have hk : 2≤2^100000000 := two_le_two_pow 100000000 (by omega)
  have h := multiplyCounted_operations (2^100000000) s hk f g
  have hr := fixed_exponent_recurrence s (overheadFactor (2^100000000))
  have hc : ((multiplyCounted (2^100000000) s f g).operations:ℝ) ≤
      (recurrence (2*(2^100000000)-1) (2^100000000) (overheadFactor (2^100000000)) s:ℝ) := by
    exact_mod_cast h
  exact hc.trans hr


/-- One fixed-arity multiplication at any positive input length. -/
def multiplyAtLength (B q : ℕ) (f g : ℤ[X]) : Counted ℤ[X] :=
  multiplyCounted (2^B) (Nat.log (2^B) q+1) f g

theorem multiplyAtLength_correct (B q : ℕ) (hB : 0<B) (hq : 0<q) (f g : ℤ[X])
    (hf : f.natDegree<q) (hg : g.natDegree<q) :
    (multiplyAtLength B q f g).value=f*g := by
  unfold multiplyAtLength
  rw [multiplyCounted_value]
  have hk := two_le_two_pow B hB
  have hp := (padded_length_bounds (2^B) q hk hq).1
  exact multiplyInteger_correct _ _ hk f g (hf.trans hp) (hg.trans hp)

/-- Near-linear all-coefficient arithmetic schedule for arbitrary q.
The multiplicative factor depends only on the chosen fixed arity. -/
theorem multiplyAtLength_operations (B q : ℕ) (hB : 0<B) (hq : 0<q) (f g : ℤ[X]) :
    ((multiplyAtLength B q f g).operations:ℝ) ≤
      (2*(overheadFactor (2^B))+1:ℝ)*((2:ℝ)^B)^(1+1/(B:ℝ))*(q:ℝ)^(1+1/(B:ℝ)) := by
  let k : ℕ:=2^B
  let s : ℕ:=Nat.log k q+1
  have hk : 2≤k := two_le_two_pow B hB
  have hslots := multiplyCounted_operations k s hk f g
  have hr := toom_recurrence_rpow B s (overheadFactor k) hB
  have hfirst : ((multiplyCounted k s f g).operations:ℝ) ≤
      (2*(overheadFactor k)+1:ℝ)*((k^s:ℕ):ℝ)^(1+1/(B:ℝ)) :=
    (show ((multiplyCounted k s f g).operations:ℝ)≤
      (recurrence (2*k-1) k (overheadFactor k) s:ℝ) by exact_mod_cast hslots).trans hr
  have hp := (padded_length_bounds k q hk hq).2
  have hpow : ((k^s:ℕ):ℝ)^(1+1/(B:ℝ))≤((k*q:ℕ):ℝ)^(1+1/(B:ℝ)) := by
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hp) (by positivity)
  change ((multiplyCounted k s f g).operations:ℝ)≤_
  calc
    _≤(2*(overheadFactor k)+1:ℝ)*((k^s:ℕ):ℝ)^(1+1/(B:ℝ)) := hfirst
    _≤(2*(overheadFactor k)+1:ℝ)*((k*q:ℕ):ℝ)^(1+1/(B:ℝ)) := by gcongr
    _=(2*(overheadFactor (2^B))+1:ℝ)*((2:ℝ)^B)^(1+1/(B:ℝ))*(q:ℝ)^(1+1/(B:ℝ)) := by
      rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
      simp only [k,Nat.cast_pow,Nat.cast_ofNat,mul_assoc]

/-- Fixed symbolic overhead epsilon. Enormous arity constants are kept
symbolic, and all variable-size divisions have a separate bitwise charge. -/
theorem multiplyAtLength_fixed_operations (q : ℕ) (hq : 0<q) (f g : ℤ[X]) :
    ((multiplyAtLength 100000000 q f g).operations:ℝ) ≤
      (2*(overheadFactor (2^100000000))+1:ℝ)*
        ((2:ℝ)^100000000)^(1.00000001:ℝ)*(q:ℝ)^(1.00000001:ℝ) := by
  have h:=multiplyAtLength_operations 100000000 q (by omega) hq f g
  have he : (1:ℝ)+1/(100000000:ℕ)=1.00000001 := by norm_num
  rwa [he] at h

/-!
The recurrence counts arithmetic slots, with a quotient slot refined by the
proved `binaryDivide` program and its `8*size` word-step bound. The primitive
integer additions/multiplications and word-level shifts/comparisons still need
the separate bit-operation refinement in `IntegerArithmetic`; no unit-cost
rational division or floating-point operation is assumed here. The path bound
`recursive_numerator_path_bits` supplies a linear bit budget for genuine
recursive interpolation numerators, with constants depending only on arity.
-/

#print axioms multiplyAtLength_correct
#print axioms multiplyAtLength_fixed_operations
#print axioms multiply_correct
#print axioms multiplyInteger_correct
#print axioms integer_interpolation_numerator
#print axioms recursive_numerator_path_bits
#print axioms padded_length_bounds
#print axioms multiplyCounted_fixed_bound
#print axioms multiplyCounted_value
#print axioms multiplyCounted_operations
#print axioms evaluationPath_bound
#print axioms partialInterpolation_bound
#print axioms partialEvaluation_bound
#print axioms linearTransformCounted_operations
#print axioms evaluation_coefficient_bridge
#print axioms numerator_coefficient_bridge
#print axioms divideVector_steps_le
#print axioms evaluatedIntegerChunk_bound
#print axioms product_coefficient_bound
#print axioms interpolationNumeratorPolynomial_bound
#print axioms interpolation_binary_division
#print axioms binaryDivide_correct
#print axioms binaryDivide_steps
#print axioms commonDenominator_pos
#print axioms integer_product_exact_division
#print axioms fixed_exponent_recurrence
end
end ThinMatrix.ToomCook
