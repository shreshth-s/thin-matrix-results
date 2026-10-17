import PolynomialCyclicFold
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Exact radix-two Fourier arithmetic

This module counts exact scalar additions and multiplications. Complex scalar
arithmetic is not a word-RAM instruction: bounded precision and exact integer
reconstruction require separate proofs. In particular this module does not
claim quasi-linear bit or word-RAM complexity for integer convolution.
-/

namespace ThinMatrix.FastConvolution

open Finset

/-- The unnormalized polynomial form of the length-`2^k` discrete transform. -/
def polynomialDFT {R : Type*} [CommRing R] (k : ℕ) (ω : R) (a : ℕ → R) (j : ℕ) : R :=
  ∑ i ∈ range (2 ^ k), a i * ω ^ (i * j)

/-- Decimation in time. Only the first `2^k` input cells are used. Child
outputs are stored once and indexed modulo their length. -/
def radixFFT {R : Type*} [CommRing R] : ℕ → R → (ℕ → R) → ℕ → R
  | 0, _, a, _ => a 0
  | k + 1, ω, a, j =>
      let even := radixFFT k (ω ^ 2) (fun i => a (2 * i))
      let odd := radixFFT k (ω ^ 2) (fun i => a (2 * i + 1))
      even (j % 2 ^ k) + ω ^ j * odd (j % 2 ^ k)

/-- Splitting a finite array into its even and odd entries is exact. -/
theorem sum_range_even_odd {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    (∑ i ∈ range (2 * n), f i) =
      (∑ i ∈ range n, f (2 * i)) + ∑ i ∈ range n, f (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h, sum_range_succ, sum_range_succ, ih, sum_range_succ, sum_range_succ]
    ac_rfl

/-- Squaring a length-`2^(k+1)` root gives a length-`2^k` root. -/
theorem square_root {R : Type*} [CommRing R] (k : ℕ) (ω : R)
    (hω : ω ^ (2 ^ (k + 1)) = 1) : (ω ^ 2) ^ (2 ^ k) = 1 := by
  rw [← pow_mul]
  convert hω using 1
  congr 1
  omega

/-- Exact radix-two transform correctness; primitivity is not needed for
this forward identity. -/
theorem radixFFT_eq_polynomialDFT {R : Type*} [CommRing R] (k : ℕ) (ω : R)
    (a : ℕ → R) (hω : ω ^ (2 ^ k) = 1) (j : ℕ) :
    radixFFT k ω a j = polynomialDFT k ω a j := by
  induction k generalizing ω a j with
  | zero => simp [radixFFT, polynomialDFT]
  | succ k ih =>
    have hsq := square_root k ω hω
    have hperiod : (ω ^ 2) ^ (j % 2 ^ k) = (ω ^ 2) ^ j :=
      (pow_eq_pow_mod j hsq).symm
    have heven (i : ℕ) : (ω ^ 2) ^ (i * (j % 2 ^ k)) = ω ^ ((2 * i) * j) := by
      rw [mul_comm i, pow_mul, hperiod, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hodd (i : ℕ) : ω ^ j * (ω ^ 2) ^ (i * (j % 2 ^ k)) =
        ω ^ ((2 * i + 1) * j) := by
      rw [heven, ← pow_add]
      congr 1
      ring
    simp only [radixFFT]
    rw [ih _ _ hsq, ih _ _ hsq]
    unfold polynomialDFT
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by omega, sum_range_even_odd]
    rw [mul_sum]
    apply congrArg₂ (· + ·)
    · apply sum_congr rfl
      intro i hi
      rw [heven]
    · apply sum_congr rfl
      intro i hi
      rw [mul_left_comm, hodd]

/-- A scalar-arithmetic computation, with its number of scalar additions
and multiplications. Indexing, memory and integer control are not charged by
this scalar model. -/
structure Counted (α : Type*) where
  value : α
  operations : ℕ

namespace Counted

def bind {α β : Type*} (x : Counted α) (f : α → Counted β) : Counted β :=
  ⟨(f x.value).value, x.operations + (f x.value).operations⟩

def scalarAdd {R : Type*} [Add R] (x y : R) : Counted R := ⟨x + y, 1⟩
def scalarMul {R : Type*} [Mul R] (x y : R) : Counted R := ⟨x * y, 1⟩

/-- Sequential finite tabulation; its scalar operation count is accumulated. -/
def sequence {α β : Type*} (f : α → Counted β) : List α → Counted (List β)
  | [] => ⟨[], 0⟩
  | x :: xs =>
      let head := f x
      let tail := sequence f xs
      ⟨head.value :: tail.value, head.operations + tail.operations⟩

theorem sequence_value {α β : Type*} (f : α → Counted β) (xs : List α) :
    (sequence f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sequence, ih]

theorem sequence_operations {α β : Type*} (f : α → Counted β) (xs : List α)
    (c : ℕ) (h : ∀ x ∈ xs, (f x).operations = c) :
    (sequence f xs).operations = c * xs.length := by
  induction xs with
  | nil => simp [sequence]
  | cons x xs ih =>
    rw [sequence, List.length_cons]
    dsimp
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    simp [Nat.mul_succ, Nat.add_comm]

end Counted

/-- Successive twiddles are formed by one multiplication each, rather than
by independently exponentiating at every output position. -/
def powerList {R : Type*} [Monoid R] (ω current : R) : ℕ → Counted (List R)
  | 0 => ⟨[], 0⟩
  | n + 1 =>
      let next := Counted.scalarMul current ω
      let tail := powerList ω next.value n
      ⟨current :: tail.value, next.operations + tail.operations⟩

theorem powerList_length {R : Type*} [Monoid R] (ω current : R) (n : ℕ) :
    (powerList ω current n).value.length = n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp [powerList, ih]

theorem powerList_operations {R : Type*} [Monoid R] (ω current : R) (n : ℕ) :
    (powerList ω current n).operations = n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp [powerList, Counted.scalarMul, ih, Nat.add_comm]

theorem powerList_getD {R : Type*} [MonoidWithZero R] (ω current : R) (n j : ℕ)
    (hj : j < n) : (powerList ω current n).value.getD j 0 = current * ω ^ j := by
  induction n generalizing current j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [powerList]
    | succ j =>
      simp only [powerList, Counted.scalarMul, List.getD_cons_succ]
      rw [ih _ _ (by omega), pow_succ']
      exact mul_assoc current ω (ω ^ j)

/-- A finite memoized radix-two transform. Each child array is computed
once, twiddles are generated successively, and each output uses one scalar
multiplication and one scalar addition. -/
def fftCounted {R : Type*} [CommRing R] : ℕ → R → (ℕ → R) → Counted (List R)
  | 0, _, a => ⟨[a 0], 0⟩
  | k + 1, ω, a =>
      let square := Counted.scalarMul ω ω
      let even := fftCounted k square.value (fun i => a (2 * i))
      let odd := fftCounted k square.value (fun i => a (2 * i + 1))
      let twiddles := powerList ω 1 (2 ^ (k + 1))
      let output := Counted.sequence (fun j =>
        Counted.bind (Counted.scalarMul (twiddles.value.getD j 0)
            (odd.value.getD (j % 2 ^ k) 0))
          (fun t => Counted.scalarAdd (even.value.getD (j % 2 ^ k) 0) t))
        (List.range (2 ^ (k + 1)))
      ⟨output.value, square.operations + even.operations + odd.operations +
        twiddles.operations + output.operations⟩

theorem fftCounted_length {R : Type*} [CommRing R] (k : ℕ) (ω : R) (a : ℕ → R) :
    (fftCounted k ω a).value.length = 2 ^ k := by
  cases k with
  | zero => rfl
  | succ k => simp [fftCounted, Counted.sequence_value]

/-- The finite stored-array algorithm agrees with the functional butterfly definition. -/
theorem fftCounted_getD {R : Type*} [CommRing R] (k : ℕ) (ω : R) (a : ℕ → R)
    (j : ℕ) (hj : j < 2 ^ k) :
    (fftCounted k ω a).value.getD j 0 = radixFFT k ω a j := by
  induction k generalizing ω a j with
  | zero =>
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | succ k ih =>
    simp only [fftCounted, Counted.sequence_value, Counted.bind, Counted.scalarMul,
      Counted.scalarAdd]
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_map, List.getElem_range]
    rw [powerList_getD _ _ _ _ hj]
    have hm : j % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    rw [ih _ _ _ hm, ih _ _ _ hm]
    simp [radixFFT, pow_two]

/-- An explicit exact scalar-operation bound. This is an arithmetic-circuit
bound, not a bounded-precision or word-RAM running-time statement. -/
theorem fftCounted_operations_le {R : Type*} [CommRing R] (k : ℕ) (ω : R)
    (a : ℕ → R) : (fftCounted k ω a).operations ≤ 4 * k * 2 ^ k := by
  induction k generalizing ω a with
  | zero => simp [fftCounted]
  | succ k ih =>
    have he := ih (ω * ω) (fun i => a (2 * i))
    have ho := ih (ω * ω) (fun i => a (2 * i + 1))
    have hc : ∀ j ∈ List.range (2 ^ (k + 1)),
        (Counted.bind (Counted.scalarMul
          ((powerList ω 1 (2 ^ (k + 1))).value.getD j 0)
          ((fftCounted k (ω * ω) (fun i => a (2 * i + 1))).value.getD (j % 2 ^ k) 0))
          (fun t => Counted.scalarAdd
            ((fftCounted k (ω * ω) (fun i => a (2 * i))).value.getD (j % 2 ^ k) 0) t)).operations = 2 :=
      by intros; rfl
    have hseq := Counted.sequence_operations _ _ 2 hc
    simp only [Counted.scalarMul, List.length_range] at hseq
    simp only [fftCounted, Counted.scalarMul]
    rw [powerList_operations, hseq]
    have hp : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    nlinarith

/-- The actual finite scalar algorithm returns the exact DFT. -/
theorem fftCounted_correct {R : Type*} [CommRing R] (k : ℕ) (ω : R)
    (a : ℕ → R) (hω : ω ^ (2 ^ k) = 1) (j : ℕ) (hj : j < 2 ^ k) :
    (fftCounted k ω a).value.getD j 0 = polynomialDFT k ω a j := by
  rw [fftCounted_getD k ω a j hj]
  exact radixFFT_eq_polynomialDFT k ω a hω j

/-- The positive standard complex character root. Mathlib's DFT uses
negative frequency, so this transform equals its DFT at `-j`. -/
noncomputable def complexRoot (k : ℕ) : ℂ :=
  ZMod.stdAddChar (1 : ZMod (2 ^ k))

theorem complexRoot_pow (k : ℕ) : complexRoot k ^ (2 ^ k) = 1 := by
  unfold complexRoot
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

theorem complexRoot_power (k n : ℕ) :
    complexRoot k ^ n = ZMod.stdAddChar (n : ZMod (2 ^ k)) := by
  unfold complexRoot
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

theorem finEquiv_val (n : ℕ) [NeZero n] (i : Fin n) :
    (ZMod.finEquiv n i).val = i.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The polynomial transform is the existing Mathlib complex DFT, with
its documented sign convention converted explicitly. -/
theorem polynomialDFT_eq_mathlib (k : ℕ) (a : ℕ → ℂ) (j : ℕ) :
    polynomialDFT k (complexRoot k) a j =
      ZMod.dft (fun i : ZMod (2 ^ k) => a i.val) (-(j : ZMod (2 ^ k))) := by
  unfold polynomialDFT
  rw [Finset.sum_range, ZMod.dft_apply]
  simp only [smul_eq_mul]
  apply Fintype.sum_equiv (ZMod.finEquiv (2 ^ k)).toEquiv
  intro i
  change a i.val * complexRoot k ^ (i.val * j) =
    ZMod.stdAddChar (-(ZMod.finEquiv (2 ^ k) i * -(j : ZMod (2 ^ k)))) *
      a (ZMod.finEquiv (2 ^ k) i).val
  rw [complexRoot_power, finEquiv_val]
  have hi : (i.val : ZMod (2 ^ k)) = ZMod.finEquiv (2 ^ k) i := by
    rw [← finEquiv_val (2 ^ k) i]
    exact ZMod.natCast_zmod_val _
  simp only [Nat.cast_mul, hi, mul_neg, neg_neg]
  exact mul_comm _ _

/-- The counted finite algorithm computes Mathlib's DFT exactly. -/
theorem fftCounted_eq_mathlib (k : ℕ) (a : ℕ → ℂ) (j : ℕ) (hj : j < 2 ^ k) :
    (fftCounted k (complexRoot k) a).value.getD j 0 =
      ZMod.dft (fun i : ZMod (2 ^ k) => a i.val) (-(j : ZMod (2 ^ k))) := by
  rw [fftCounted_correct k _ a (complexRoot_pow k) j hj]
  exact polynomialDFT_eq_mathlib k a j

/-- The inverse character root has the same power-of-two period. -/
theorem complexRoot_inv_pow (k : ℕ) : (complexRoot k)⁻¹ ^ (2 ^ k) = 1 := by
  rw [inv_pow, complexRoot_pow, inv_one]

/-- Converting inverse-root polynomial evaluation to Mathlib's DFT. -/
theorem polynomialDFT_inv_eq_mathlib (k : ℕ) (a : ℕ → ℂ) (j : ℕ) :
    polynomialDFT k (complexRoot k)⁻¹ a j =
      ZMod.dft (fun i : ZMod (2 ^ k) => a i.val) (j : ZMod (2 ^ k)) := by
  unfold polynomialDFT
  rw [Finset.sum_range, ZMod.dft_apply]
  simp only [smul_eq_mul]
  apply Fintype.sum_equiv (ZMod.finEquiv (2 ^ k)).toEquiv
  intro i
  change a i.val * (complexRoot k)⁻¹ ^ (i.val * j) =
    ZMod.stdAddChar (-(ZMod.finEquiv (2 ^ k) i * (j : ZMod (2 ^ k)))) *
      a (ZMod.finEquiv (2 ^ k) i).val
  rw [inv_pow, complexRoot_power, ← AddChar.map_neg_eq_inv, finEquiv_val]
  have hi : (i.val : ZMod (2 ^ k)) = ZMod.finEquiv (2 ^ k) i := by
    rw [← finEquiv_val (2 ^ k) i]
    exact ZMod.natCast_zmod_val _
  simp only [Nat.cast_mul, hi]
  exact mul_comm _ _

/-- Forward followed by inverse-root transform returns `N` times each
input coefficient. The scalar `1/N` is applied only after this identity. -/
theorem inverse_transform (k : ℕ) (a : ℕ → ℂ) (j : ℕ) (hj : j < 2 ^ k) :
    polynomialDFT k (complexRoot k)⁻¹ (fun i => polynomialDFT k (complexRoot k) a i) j =
      (2 ^ k : ℂ) * a j := by
  rw [polynomialDFT_inv_eq_mathlib]
  have hf : (fun i : ZMod (2 ^ k) => polynomialDFT k (complexRoot k) a i.val) =
      fun i : ZMod (2 ^ k) => ZMod.dft (fun t : ZMod (2 ^ k) => a t.val) (-i) := by
    funext i
    rw [polynomialDFT_eq_mathlib, ZMod.natCast_zmod_val]
  rw [hf, ZMod.dft_comp_neg, ZMod.dft_dft]
  simp [smul_eq_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

/-- A zero-padded coefficient vector transforms to polynomial evaluations. -/
theorem fftCounted_polynomial_eval (k : ℕ) (ω : ℂ) (P : Polynomial ℂ)
    (hω : ω ^ (2 ^ k) = 1) (hP : P.natDegree < 2 ^ k) (j : ℕ) (hj : j < 2 ^ k) :
    (fftCounted k ω P.coeff).value.getD j 0 = P.eval (ω ^ j) := by
  rw [fftCounted_correct k ω P.coeff hω j hj]
  unfold polynomialDFT
  rw [Polynomial.eval_eq_sum_range' hP]
  apply sum_congr rfl
  intro i hi
  rw [← pow_mul]
  congr 2
  ring

/-- Pointwise frequency products, one scalar multiplication per entry. -/
def pointwiseProduct (n : ℕ) (a b : List ℂ) : Counted (List ℂ) :=
  Counted.sequence (fun j => Counted.scalarMul (a.getD j 0) (b.getD j 0)) (List.range n)

theorem pointwiseProduct_operations (n : ℕ) (a b : List ℂ) :
    (pointwiseProduct n a b).operations = n := by
  unfold pointwiseProduct
  rw [Counted.sequence_operations _ _ 1 (by intros; rfl), List.length_range, one_mul]

theorem pointwiseProduct_getD (n : ℕ) (a b : List ℂ) (j : ℕ) (hj : j < n) :
    (pointwiseProduct n a b).value.getD j 0 = a.getD j 0 * b.getD j 0 := by
  rw [pointwiseProduct, Counted.sequence_value]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp [Counted.scalarMul]

/-- Scaling an array by a supplied exact scalar costs one scalar
multiplication per entry in the scalar-arithmetic model. -/
def scaleVector (n : ℕ) (c : ℂ) (a : List ℂ) : Counted (List ℂ) :=
  Counted.sequence (fun j => Counted.scalarMul c (a.getD j 0)) (List.range n)

theorem scaleVector_operations (n : ℕ) (c : ℂ) (a : List ℂ) :
    (scaleVector n c a).operations = n := by
  unfold scaleVector
  rw [Counted.sequence_operations _ _ 1 (by intros; rfl), List.length_range, one_mul]

theorem scaleVector_getD (n : ℕ) (c : ℂ) (a : List ℂ) (j : ℕ) (hj : j < n) :
    (scaleVector n c a).value.getD j 0 = c * a.getD j 0 := by
  rw [scaleVector, Counted.sequence_value]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp [Counted.scalarMul]

/-- Three FFTs, one pointwise product and final normalization. The exact
root and `1/N` are supplied constants in this scalar model. -/
noncomputable def convolutionCounted (k : ℕ) (a b : ℕ → ℂ) : Counted (List ℂ) :=
  let left := fftCounted k (complexRoot k) a
  let right := fftCounted k (complexRoot k) b
  let frequencies := pointwiseProduct (2 ^ k) left.value right.value
  let inverse := fftCounted k (complexRoot k)⁻¹ (fun i => frequencies.value.getD i 0)
  let output := scaleVector (2 ^ k) ((2 ^ k : ℂ)⁻¹) inverse.value
  ⟨output.value, left.operations + right.operations + frequencies.operations +
    inverse.operations + output.operations⟩

/-- A fully explicit scalar-arithmetic count for all coefficients. -/
theorem convolutionCounted_operations_le (k : ℕ) (a b : ℕ → ℂ) :
    (convolutionCounted k a b).operations ≤ 12 * k * 2 ^ k + 2 * 2 ^ k := by
  have hl := fftCounted_operations_le k (complexRoot k) a
  have hr := fftCounted_operations_le k (complexRoot k) b
  have hi := fftCounted_operations_le k (complexRoot k)⁻¹
    (fun i => (pointwiseProduct (2 ^ k) (fftCounted k (complexRoot k) a).value
      (fftCounted k (complexRoot k) b).value).value.getD i 0)
  simp only [convolutionCounted, pointwiseProduct_operations, scaleVector_operations]
  nlinarith

/-- Zero padding beyond the product's degree makes FFT multiplication an
exact ordinary polynomial product, with no cyclic aliasing. -/
theorem convolutionCounted_polynomial (k : ℕ) (P Q : Polynomial ℂ)
    (hP : P.natDegree < 2 ^ k) (hQ : Q.natDegree < 2 ^ k)
    (hPQ : (P * Q).natDegree < 2 ^ k) (j : ℕ) (hj : j < 2 ^ k) :
    (convolutionCounted k P.coeff Q.coeff).value.getD j 0 = (P * Q).coeff j := by
  have hfrequency (i : ℕ) (hi : i < 2 ^ k) :
      (pointwiseProduct (2 ^ k) (fftCounted k (complexRoot k) P.coeff).value
        (fftCounted k (complexRoot k) Q.coeff).value).value.getD i 0 =
        polynomialDFT k (complexRoot k) (P * Q).coeff i := by
    rw [pointwiseProduct_getD _ _ _ i hi]
    rw [fftCounted_polynomial_eval k _ P (complexRoot_pow k) hP i hi,
      fftCounted_polynomial_eval k _ Q (complexRoot_pow k) hQ i hi]
    have heval := fftCounted_polynomial_eval k (complexRoot k) (P * Q)
      (complexRoot_pow k) hPQ i hi
    rw [fftCounted_correct k _ _ (complexRoot_pow k) i hi] at heval
    rw [heval, Polynomial.eval_mul]
  change (scaleVector (2 ^ k) ((2 ^ k : ℂ)⁻¹)
    (fftCounted k (complexRoot k)⁻¹ (fun i =>
      (pointwiseProduct (2 ^ k) (fftCounted k (complexRoot k) P.coeff).value
        (fftCounted k (complexRoot k) Q.coeff).value).value.getD i 0)).value).value.getD j 0 = _
  rw [scaleVector_getD _ _ _ j hj,
    fftCounted_correct k _ _ (complexRoot_inv_pow k) j hj]
  have htransform : polynomialDFT k (complexRoot k)⁻¹ (fun i =>
      (pointwiseProduct (2 ^ k) (fftCounted k (complexRoot k) P.coeff).value
        (fftCounted k (complexRoot k) Q.coeff).value).value.getD i 0) j =
      polynomialDFT k (complexRoot k)⁻¹
        (fun i => polynomialDFT k (complexRoot k) (P * Q).coeff i) j := by
    unfold polynomialDFT
    apply sum_congr rfl
    intro i hi
    exact congrArg (fun x => x * (complexRoot k)⁻¹ ^ (i * j))
      (hfrequency i (mem_range.mp hi))
  rw [htransform, inverse_transform k _ j hj]
  have hn : (2 ^ k : ℂ) ≠ 0 := pow_ne_zero k (by norm_num)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The zero-padded theorem applies to arbitrary integer coefficients,
cast exactly into the complex scalar arithmetic model. -/
theorem convolutionCounted_integer (k : ℕ) (P Q : Polynomial ℤ)
    (hP : P.natDegree < 2 ^ k) (hQ : Q.natDegree < 2 ^ k)
    (hPQ : (P * Q).natDegree < 2 ^ k) (j : ℕ) (hj : j < 2 ^ k) :
    (convolutionCounted k (fun i => (P.coeff i : ℂ))
      (fun i => (Q.coeff i : ℂ))).value.getD j 0 = ((P * Q).coeff j : ℂ) := by
  let f : ℤ →+* ℂ := Int.castRingHom ℂ
  have hp : (P.map f).natDegree < 2 ^ k := lt_of_le_of_lt Polynomial.natDegree_map_le hP
  have hq : (Q.map f).natDegree < 2 ^ k := lt_of_le_of_lt Polynomial.natDegree_map_le hQ
  have hpq : (P.map f * Q.map f).natDegree < 2 ^ k := by
    rw [← Polynomial.map_mul]
    exact lt_of_le_of_lt Polynomial.natDegree_map_le hPQ
  have hcP : (P.map f).coeff = fun i => (P.coeff i : ℂ) := by
    funext i
    simp [f, Polynomial.coeff_map]
  have hcQ : (Q.map f).coeff = fun i => (Q.coeff i : ℂ) := by
    funext i
    simp [f, Polynomial.coeff_map]
  have h := convolutionCounted_polynomial k (P.map f) (Q.map f) hp hq hpq j hj
  rw [hcP, hcQ, ← Polynomial.map_mul, Polynomial.coeff_map] at h
  simpa [f] using h

/-- Direct zero padding of a genuine finite integer coefficient vector. -/
def zeroPad {q : ℕ} (a : CyclicRing.Cyclic q) (i : ℕ) : ℂ :=
  if h : i < q then (a ⟨i, h⟩ : ℂ) else 0

theorem zeroPad_eq_polynomial {q : ℕ} (a : CyclicRing.Cyclic q) :
    zeroPad a = fun i => ((PolynomialCyclicFold.toPolynomial a).coeff i : ℂ) := by
  funext i
  by_cases hi : i < q
  · simp only [zeroPad, dif_pos hi]
    rw [PolynomialCyclicFold.coeff_toPolynomial a ⟨i, hi⟩]
  · simp only [zeroPad, dif_neg hi,
      PolynomialCyclicFold.coeff_toPolynomial_eq_zero a i (by omega), Int.cast_zero]

/-- Fold exactly the two possible ordinary product degrees at each residue. -/
noncomputable def cyclicFFTCounted {q : ℕ} (k : ℕ) (a b : CyclicRing.Cyclic q) :
    Counted (List ℂ) :=
  let product := convolutionCounted k (zeroPad a) (zeroPad b)
  let output := Counted.sequence (fun j => Counted.scalarAdd
    (product.value.getD j 0) (product.value.getD (j + q) 0)) (List.range q)
  ⟨output.value, product.operations + output.operations⟩

/-- Degree conversion for the zero-padded input arrays, including zero polynomials. -/
theorem toPolynomial_natDegree_lt {q : ℕ} [NeZero q] (a : CyclicRing.Cyclic q) :
    (PolynomialCyclicFold.toPolynomial a).natDegree < q := by
  by_cases h : PolynomialCyclicFold.toPolynomial a = 0
  · simpa [h] using NeZero.pos q
  · exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr
      (PolynomialCyclicFold.toPolynomial_degree_lt a)

/-- Exact cyclic integer convolution for any positive modulus, obtained by
power-of-two zero padding and two-term coefficient folding. -/
theorem cyclicFFTCounted_correct {q : ℕ} [NeZero q] (k : ℕ)
    (a b : CyclicRing.Cyclic q) (hN : 2 * q ≤ 2 ^ k) (j : Fin q) :
    (cyclicFFTCounted k a b).value.getD j.val 0 =
      (CyclicRing.convolution a b j : ℂ) := by
  let P := PolynomialCyclicFold.toPolynomial a
  let Q := PolynomialCyclicFold.toPolynomial b
  have hp : P.natDegree < 2 ^ k := lt_of_lt_of_le (toPolynomial_natDegree_lt a) (by omega)
  have hq : Q.natDegree < 2 ^ k := lt_of_lt_of_le (toPolynomial_natDegree_lt b) (by omega)
  have hpq : (P * Q).natDegree < 2 ^ k := by
    have hpd := toPolynomial_natDegree_lt a
    have hqd := toPolynomial_natDegree_lt b
    exact lt_of_le_of_lt Polynomial.natDegree_mul_le (by dsimp [P, Q]; omega)
  have hj : j.val < 2 ^ k := lt_of_lt_of_le j.isLt (by omega)
  have hjq : j.val + q < 2 ^ k := by have := j.isLt; omega
  change (Counted.sequence (fun i => Counted.scalarAdd
    ((convolutionCounted k (zeroPad a) (zeroPad b)).value.getD i 0)
    ((convolutionCounted k (zeroPad a) (zeroPad b)).value.getD (i + q) 0))
      (List.range q)).value.getD j.val 0 = _
  rw [Counted.sequence_value, List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range, Counted.scalarAdd]
  rw [zeroPad_eq_polynomial a, zeroPad_eq_polynomial b]
  rw [convolutionCounted_integer k P Q hp hq hpq j.val hj,
    convolutionCounted_integer k P Q hp hq hpq (j.val + q) hjq]
  rw [PolynomialCyclicFold.convolution_eq_coeff_fold]
  push_cast
  rfl

/-- Complete cyclic multiplication costs three FFTs and linear scalar
work in this exact-complex scalar-arithmetic model. -/
theorem cyclicFFTCounted_operations_le {q : ℕ} (k : ℕ) (a b : CyclicRing.Cyclic q) :
    (cyclicFFTCounted k a b).operations ≤ 12 * k * 2 ^ k + 2 * 2 ^ k + q := by
  have hc := convolutionCounted_operations_le k (zeroPad a) (zeroPad b)
  have ho : ∀ i ∈ List.range q,
      (Counted.scalarAdd
        ((convolutionCounted k (zeroPad a) (zeroPad b)).value.getD i 0)
        ((convolutionCounted k (zeroPad a) (zeroPad b)).value.getD (i + q) 0)).operations = 1 :=
    by intros; rfl
  simp only [cyclicFFTCounted]
  rw [Counted.sequence_operations _ _ 1 ho, List.length_range, one_mul]
  omega

/-- A power-of-two padding exponent with a constant-factor length increase. -/
def paddedExponent (q : ℕ) : ℕ := q.log2 + 2

theorem padded_length_bounds (q : ℕ) (hq : 0 < q) :
    2 * q ≤ 2 ^ paddedExponent q ∧ 2 ^ paddedExponent q ≤ 4 * q := by
  have hl : q < 2 ^ (q.log2 + 1) := Nat.lt_log2_self
  have hu : 2 ^ q.log2 ≤ q := Nat.log2_self_le (by omega)
  simp only [paddedExponent, pow_add, pow_one] at hl ⊢
  norm_num
  constructor <;> nlinarith

/-- Explicit `O(q log q)` all-coefficient scalar arithmetic, for arbitrary
positive q. This theorem makes no bit-operation or RAM-time assertion. -/
theorem cyclicFFTCounted_padded_operations {q : ℕ} [NeZero q]
    (a b : CyclicRing.Cyclic q) :
    (cyclicFFTCounted (paddedExponent q) a b).operations ≤
      60 * q * (q.log2 + 3) := by
  have hc := cyclicFFTCounted_operations_le (paddedExponent q) a b
  have hu := (padded_length_bounds q (NeZero.pos q)).2
  have hm := Nat.mul_le_mul_left (12 * paddedExponent q) hu
  unfold paddedExponent at hc hu hm ⊢
  nlinarith

/-- Padded all-coefficient correctness paired with the preceding proved count. -/
theorem cyclicFFTCounted_padded_correct {q : ℕ} [NeZero q]
    (a b : CyclicRing.Cyclic q) (j : Fin q) :
    (cyclicFFTCounted (paddedExponent q) a b).value.getD j.val 0 =
      (CyclicRing.convolution a b j : ℂ) :=
  cyclicFFTCounted_correct _ a b (padded_length_bounds q (NeZero.pos q)).1 j

end ThinMatrix.FastConvolution

#print axioms ThinMatrix.FastConvolution.radixFFT_eq_polynomialDFT
#print axioms ThinMatrix.FastConvolution.fftCounted_getD
#print axioms ThinMatrix.FastConvolution.fftCounted_operations_le
#print axioms ThinMatrix.FastConvolution.fftCounted_eq_mathlib
#print axioms ThinMatrix.FastConvolution.inverse_transform
#print axioms ThinMatrix.FastConvolution.convolutionCounted_polynomial
#print axioms ThinMatrix.FastConvolution.convolutionCounted_integer
#print axioms ThinMatrix.FastConvolution.cyclicFFTCounted_correct
#print axioms ThinMatrix.FastConvolution.cyclicFFTCounted_padded_operations
#print axioms ThinMatrix.FastConvolution.cyclicFFTCounted_padded_correct
