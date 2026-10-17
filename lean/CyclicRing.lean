import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exact cyclic integer coefficient vectors

A vector has exactly `q` integer coefficients. Multiplication is cyclic
convolution, transported from the additive monoid algebra of `Fin q`.
The sole modulus assumption is `[NeZero q]`, so `q = 1` is included.
Normalization divides only a complete numerator with its proved scale.

These are semantic and magnitude theorems, not execution-cost theorems.
The definition `convolution` gives a length-`q` dot product per coefficient;
evaluating it independently for all coefficients uses `q^2` scalar products.
The quasi-linear exact integer cyclic multiplication required by the research
preprocessing bounds remains a separate algorithm-and-bit-cost obligation.
-/

namespace ThinMatrix.CyclicRing

/-- A cyclic vector is a function on the `q` residue representatives. -/
def Cyclic (q : ℕ) := Fin q → ℤ

/-- The finite coefficient vector and its additive monoid algebra are equivalent. -/
noncomputable def algebraEquiv (q : ℕ) : Cyclic q ≃ AddMonoidAlgebra ℤ (Fin q) :=
  Finsupp.equivFunOnFinite.symm.trans AddMonoidAlgebra.coeffEquiv.symm

noncomputable instance (q : ℕ) [NeZero q] : CommRing (Cyclic q) :=
  (algebraEquiv q).commRing

/-- The ring equivalence certifies every ring axiom of cyclic convolution. -/
noncomputable def cyclicRingEquiv (q : ℕ) [NeZero q] :
    Cyclic q ≃+* AddMonoidAlgebra ℤ (Fin q) :=
  (algebraEquiv q).ringEquiv

/-- Cyclic convolution. Subtraction in `Fin q` is subtraction modulo `q`. -/
def convolution {q : ℕ} [NeZero q] (a b : Cyclic q) : Cyclic q :=
  fun k => ∑ i : Fin q, a i * b (k - i)

@[simp] theorem algebraEquiv_apply (q : ℕ) (a : Cyclic q) (i : Fin q) :
    algebraEquiv q a i = a i := rfl

@[simp] theorem algebraEquiv_symm_apply (q : ℕ)
    (a : AddMonoidAlgebra ℤ (Fin q)) (i : Fin q) :
    (algebraEquiv q).symm a i = a i := rfl

/-- One selected coefficient needs exactly the corresponding length-`q` dot product. -/
theorem mul_coeff {q : ℕ} [NeZero q] (a b : Cyclic q) (k : Fin q) :
    (a * b) k = ∑ i : Fin q, a i * b (k - i) := by
  change (algebraEquiv q a * algebraEquiv q b) k = _
  rw [AddMonoidAlgebra.mul_apply_left]
  rw [Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [sub_eq_add_neg, add_comm]
  · intro i
    simp

/-- The transported ring multiplication is the stated cyclic convolution. -/
theorem mul_eq_convolution {q : ℕ} [NeZero q] (a b : Cyclic q) :
    a * b = convolution a b := by
  funext k
  exact mul_coeff a b k

@[simp] theorem add_coeff {q : ℕ} [NeZero q] (a b : Cyclic q) (k : Fin q) :
    (a + b) k = a k + b k := rfl

@[simp] theorem neg_coeff {q : ℕ} [NeZero q] (a : Cyclic q) (k : Fin q) :
    (-a) k = -a k := rfl

@[simp] theorem zero_coeff {q : ℕ} [NeZero q] (k : Fin q) :
    (0 : Cyclic q) k = 0 := rfl

/-- Finite sums of cyclic vectors are coefficientwise sums. -/
@[simp] theorem sum_coeff {q : ℕ} [NeZero q] {ι : Type*}
    (s : Finset ι) (a : ι → Cyclic q) (k : Fin q) :
    (∑ i ∈ s, a i) k = ∑ i ∈ s, a i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- A single integer coefficient at one residue. -/
def monomial {q : ℕ} (i : Fin q) (c : ℤ) : Cyclic q :=
  fun k => if k = i then c else 0

@[simp] theorem monomial_coeff {q : ℕ} (i k : Fin q) (c : ℤ) :
    monomial i c k = if k = i then c else 0 := rfl

@[simp] theorem algebraEquiv_monomial {q : ℕ} (i : Fin q) (c : ℤ) :
    algebraEquiv q (monomial i c) = AddMonoidAlgebra.single i c := by
  ext k
  simp [monomial, AddMonoidAlgebra.single_apply, eq_comm]

/-- Monomial exponents add modulo `q`, including when `q = 1`. -/
theorem monomial_mul {q : ℕ} [NeZero q] (i j : Fin q) (c d : ℤ) :
    monomial i c * monomial j d = monomial (i + j) (c * d) := by
  apply (cyclicRingEquiv q).injective
  rw [map_mul]
  change algebraEquiv q (monomial i c) * algebraEquiv q (monomial j d) =
    algebraEquiv q (monomial (i + j) (c * d))
  simp [AddMonoidAlgebra.single_mul_single]

/-- Selected monomial-product coefficients are exact modular equality tests. -/
@[simp] theorem monomial_mul_coeff {q : ℕ} [NeZero q]
    (i j k : Fin q) (c d : ℤ) :
    (monomial i c * monomial j d) k = if k = i + j then c * d else 0 := by
  rw [monomial_mul]
  rfl

/-- Integer scaling acts coefficientwise, without reducing coefficients modulo `q`. -/
def scale {q : ℕ} (c : ℤ) (a : Cyclic q) : Cyclic q := fun k => c * a k

/-- Multiplication by an integer constant scales every coefficient. -/
theorem intCast_mul_coeff {q : ℕ} [NeZero q] (c : ℤ) (a : Cyclic q) (k : Fin q) :
    ((c : Cyclic q) * a) k = c * a k := by
  change cyclicRingEquiv q ((c : Cyclic q) * a) k = _
  rw [map_mul, map_intCast]
  rw [AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.single_zero_mul_apply]
  rfl

/-- The coefficientwise scaling operation agrees with multiplication in the ring. -/
theorem scale_eq_intCast_mul {q : ℕ} [NeZero q] (c : ℤ) (a : Cyclic q) :
    scale c a = (c : Cyclic q) * a := by
  funext k
  exact (intCast_mul_coeff c a k).symm

/-- Coefficientwise exact integer decoding, defined for the complete numerator. -/
def decode {q : ℕ} (L : ℕ) (numerator : Cyclic q) : Cyclic q :=
  fun k => numerator k / (4 : ℤ) ^ L

/-- A proved complete scale identity gives exact decoding of every coefficient. -/
theorem decode_complete {q : ℕ} (L : ℕ) (numerator product : Cyclic q)
    (h : numerator = scale ((4 : ℤ) ^ L) product) :
    decode L numerator = product := by
  subst numerator
  funext k
  simp [decode, scale]

/-- Residual and box terms are added before exact normalization. -/
theorem decode_residual_plus_boxes {q : ℕ} [NeZero q] (L : ℕ)
    (residual boxes product : Cyclic q)
    (h : residual + boxes = scale ((4 : ℤ) ^ L) product) :
    decode L (residual + boxes) = product :=
  decode_complete L (residual + boxes) product h

/-- Ring notation for the complete scaled-numerator normalization. -/
theorem decode_complete_ring {q : ℕ} [NeZero q] (L : ℕ)
    (numerator product : Cyclic q)
    (h : numerator = (((4 : ℤ) ^ L : ℤ) : Cyclic q) * product) :
    decode L numerator = product := by
  apply decode_complete
  rw [scale_eq_intCast_mul]
  exact h

/-- The scale identity certifies divisibility of the complete numerator. -/
theorem complete_coefficient_dvd {q : ℕ} (L : ℕ) (numerator product : Cyclic q)
    (h : numerator = scale ((4 : ℤ) ^ L) product) (k : Fin q) :
    (4 : ℤ) ^ L ∣ numerator k := by
  rw [h]
  exact ⟨product k, rfl⟩

/-- The integral vector satisfying the complete scale identity is unique. -/
theorem complete_normalization_unique {q : ℕ} (L : ℕ) (numerator : Cyclic q)
    (a b : Cyclic q)
    (ha : numerator = scale ((4 : ℤ) ^ L) a)
    (hb : numerator = scale ((4 : ℤ) ^ L) b) : a = b := by
  have h₁ := decode_complete L numerator a ha
  have h₂ := decode_complete L numerator b hb
  exact h₁.symm.trans h₂

/-- A scale witness supplies the unique exact integral normalization. -/
theorem complete_normalization_existsUnique {q : ℕ} (L : ℕ)
    (numerator product : Cyclic q)
    (h : numerator = scale ((4 : ℤ) ^ L) product) :
    ∃! a : Cyclic q, numerator = scale ((4 : ℤ) ^ L) a := by
  refine ⟨product, h, ?_⟩
  intro a ha
  exact complete_normalization_unique L numerator a product ha h

/-- The single-residue case uses ordinary integer multiplication. -/
theorem mul_modulus_one (a b : Cyclic 1) : (a * b) 0 = a 0 * b 0 := by
  rw [mul_coeff]
  simp

/-- Uniform coefficient magnitudes give the full length-`q` convolution charge. -/
theorem convolution_abs_le {q : ℕ} [NeZero q] (a b : Cyclic q)
    (A B : ℤ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ i, |a i| ≤ A) (hb : ∀ i, |b i| ≤ B) (k : Fin q) :
    |convolution a b k| ≤ (q : ℤ) * A * B := by
  calc
    |convolution a b k| ≤ ∑ i : Fin q, |a i * b (k - i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin q, |a i| * |b (k - i)| := by simp only [abs_mul]
    _ ≤ ∑ _i : Fin q, A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (ha i) (hb (k - i)) (abs_nonneg _) hA
    _ = (q : ℤ) * A * B := by simp [mul_assoc]

/-- The same magnitude statement for ring multiplication. -/
theorem mul_abs_le {q : ℕ} [NeZero q] (a b : Cyclic q)
    (A B : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, |a i| ≤ A) (hb : ∀ i, |b i| ≤ B) (k : Fin q) :
    |(a * b) k| ≤ (q : ℤ) * A * B := by
  rw [mul_eq_convolution]
  exact convolution_abs_le a b A B hA hB ha hb k

/-- An integer linear transform of a family of cyclic vectors. -/
def linearCombination {q : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (a : ι → Cyclic q) : Cyclic q :=
  fun k => ∑ i ∈ s, c i * a i k

/-- A row's integer `ℓ₁` weight controls coefficient growth. -/
theorem linearCombination_abs_le {q : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (a : ι → Cyclic q) (A C : ℤ)
    (hA : 0 ≤ A) (ha : ∀ i ∈ s, ∀ k, |a i k| ≤ A)
    (hc : ∑ i ∈ s, |c i| ≤ C) (k : Fin q) :
    |linearCombination s c a k| ≤ C * A := by
  calc
    |linearCombination s c a k| ≤ ∑ i ∈ s, |c i * a i k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |c i| * |a i k| := by simp only [abs_mul]
    _ ≤ ∑ i ∈ s, |c i| * A := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (ha i hi k) (abs_nonneg _)
    _ = (∑ i ∈ s, |c i|) * A := by rw [Finset.sum_mul]
    _ ≤ C * A := mul_le_mul_of_nonneg_right hc hA

/-- Logarithmic magnitude budgets add under convolution, with the modulus budget. -/
theorem mul_pow_two_bound {q : ℕ} [NeZero q] (a b : Cyclic q)
    (qa ab bb : ℕ) (hq : (q : ℤ) ≤ 2 ^ qa)
    (ha : ∀ i, |a i| ≤ 2 ^ ab) (hb : ∀ i, |b i| ≤ 2 ^ bb)
    (k : Fin q) : |(a * b) k| ≤ 2 ^ (qa + ab + bb) := by
  calc
    |(a * b) k| ≤ (q : ℤ) * 2 ^ ab * 2 ^ bb :=
      mul_abs_le a b _ _ (by positivity) (by positivity) ha hb k
    _ ≤ (2 : ℤ) ^ qa * 2 ^ ab * 2 ^ bb := by gcongr
    _ = 2 ^ (qa + ab + bb) := by simp [pow_add]

/-- A bounded integer transform adds its row-weight budget to the input budget. -/
theorem linearCombination_pow_two_bound {q : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℤ) (a : ι → Cyclic q) (ab cb : ℕ)
    (ha : ∀ i ∈ s, ∀ k, |a i k| ≤ 2 ^ ab)
    (hc : ∑ i ∈ s, |c i| ≤ 2 ^ cb) (k : Fin q) :
    |linearCombination s c a k| ≤ 2 ^ (cb + ab) := by
  calc
    |linearCombination s c a k| ≤ (2 : ℤ) ^ cb * 2 ^ ab :=
      linearCombination_abs_le s c a _ _ (by positivity) ha hc k
    _ = 2 ^ (cb + ab) := by rw [pow_add]

end ThinMatrix.CyclicRing

#print axioms ThinMatrix.CyclicRing.cyclicRingEquiv
#print axioms ThinMatrix.CyclicRing.mul_coeff
#print axioms ThinMatrix.CyclicRing.monomial_mul
#print axioms ThinMatrix.CyclicRing.decode_complete
#print axioms ThinMatrix.CyclicRing.decode_residual_plus_boxes
#print axioms ThinMatrix.CyclicRing.complete_normalization_existsUnique
#print axioms ThinMatrix.CyclicRing.mul_abs_le
#print axioms ThinMatrix.CyclicRing.linearCombination_abs_le
#print axioms ThinMatrix.CyclicRing.mul_pow_two_bound
#print axioms ThinMatrix.CyclicRing.linearCombination_pow_two_bound
