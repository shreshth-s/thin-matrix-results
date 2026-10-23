import CWInterpolationCosts

set_option autoImplicit false

/-! Polynomial bit envelopes for the retained linear forms, products and
output numerators. These bounds do not constitute a binary machine simulator. -/
namespace ThinMatrix.CWInterpolationWidths
open CWPowerSpecialization CWInterpolationProgram CWInterpolationCosts
open IntegerInterpolationWeights IntegerInterpolationRows

def weightExponent (d : ℕ) : ℕ := envelope d*((d+1)*(d+2))
def linearExponent (n B : ℕ) : ℕ := 18*n+CWCoefficientBounds.bound (10*n)*n+B
def numeratorExponent (n B : ℕ) : ℕ :=
  (10*n+1)+54*n+weightExponent (10*n)+3*CWCoefficientBounds.bound (10*n)*n+2*B

theorem nat_pow_envelope (a n : ℕ) : a^n≤2^(a*n) := by
  calc
    _ ≤ (2^a)^n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le n
    _ = _ := (pow_mul _ _ _).symm

theorem weight_envelope (d : ℕ) : coefficientBound d≤2^(weightExponent d) := by
  unfold coefficientBound rowBound weightExponent
  rw [← pow_mul]
  exact nat_pow_envelope _ _

theorem linear_envelope (n B : ℕ) : linearBound n (2^B)≤2^(linearExponent n B) := by
  unfold linearBound linearExponent
  calc
    _ ≤ 2^(18*n)*(2^(CWCoefficientBounds.bound (10*n)*n)*2^B) :=
      Nat.mul_le_mul (nat_pow_envelope 18 n) (Nat.mul_le_mul_right _ (nat_pow_envelope _ n))
    _ = _ := by simp only [pow_add];ring

theorem numerator_envelope (n B : ℕ) : numeratorBound n (2^B)≤2^(numeratorExponent n B) := by
  unfold numeratorBound
  calc
    _ ≤ (2^(10*n+1)*2^(18*n))*(2^(weightExponent (10*n))*
        (2^(CWCoefficientBounds.bound (10*n)*n)*(2^(linearExponent n B))^2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.lt_two_pow_self).le (nat_pow_envelope 18 n))
        (Nat.mul_le_mul (weight_envelope (10*n))
          (Nat.mul_le_mul (nat_pow_envelope _ n) (Nat.pow_le_pow_left (linear_envelope n B) 2)))
    _ = _ := by
      rw [← pow_mul]
      simp only [← pow_add]
      congr 1
      unfold numeratorExponent linearExponent
      ring

theorem size_of_envelope {z : ℤ} {e : ℕ} (h : z.natAbs≤2^e) : z.natAbs.size≤e+1 := by
  apply Nat.size_le.mpr
  exact h.trans_lt (by rw [pow_succ];have := Nat.two_pow_pos e;omega)

theorem dot_bits (side : Fin 3) (n B : ℕ) (a : Fin (10*n+1)) (s : TermIndex n)
    (x : Index n → ℤ) (hx : ∀ i,(x i).natAbs≤2^B) :
    (dot side n a.val s x).1.natAbs.size≤linearExponent n B+1 := by
  exact size_of_envelope ((dot_magnitude side n a s x (2^B) hx).trans (linear_envelope n B))

theorem product_bits (n B : ℕ) (x y : Index n → ℤ)
    (hx : ∀ i,(x i).natAbs≤2^B) (hy : ∀ i,(y i).natAbs≤2^B)
    (p : Request n × CountedCWCoefficients.Scalar) (hp : p ∈ products n x y) :
    p.2.1.natAbs.size≤2*linearExponent n B+1 := by
  apply size_of_envelope
  calc
    _ ≤ (linearBound n (2^B))^2 := products_magnitude n (2^B) x y hx hy p hp
    _ ≤ (2^(linearExponent n B))^2 := Nat.pow_le_pow_left (linear_envelope n B) 2
    _ = _ := by rw [← pow_mul];congr 1;omega

theorem collect_bits (n B : ℕ) (x y : Index n → ℤ)
    (hx : ∀ i,(x i).natAbs≤2^B) (hy : ∀ i,(y i).natAbs≤2^B) (k : Index n) :
    (collect n (prepare (10*n) (order n)) (products n x y) k).1.natAbs.size≤
      numeratorExponent n B+1 := by
  exact size_of_envelope ((collect_magnitude n (2^B) x y hx hy k).trans (numerator_envelope n B))

#print axioms nat_pow_envelope
#print axioms weight_envelope
#print axioms linear_envelope
#print axioms numerator_envelope
#print axioms size_of_envelope
#print axioms dot_bits
#print axioms product_bits
#print axioms collect_bits
end ThinMatrix.CWInterpolationWidths
