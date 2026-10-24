import BinaryAddressedRecovery

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false

/-! Uniform binary work for the rational-base evaluator with addressed
recursive and recovery tables. The extra address work is polynomial in depth;
it preserves the exponential recurrence base. -/
namespace ThinMatrix.BinaryAddressedUniform
open BinaryCell BinaryAddressedRecursion
open RecursiveTable (Table prod fin)
open RetainedEqualCopy (Base)
variable {a b c r t : ℕ}

def constant (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ) :=
  BinaryRecursiveUniform.constant d+
    131072*(RetainedEqualCopyCosts.levelConstant r t (a*b) (b*c) (c*a)+2*t)*
      (BinaryAddressedWidth.slope a b c r t+1)^2

theorem execute_bits (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (k B : ℕ) (hB : 1≤B) (x : Cells t a b k) (y : Cells t b c k)
    (hx : BinaryRetainedBounds.Bounded x B) (hy : BinaryRetainedBounds.Bounded y B) :
    (BinaryAddressedRecovery.execute ha hb hc ht d k x y).bitSteps≤
      constant d*(k+B.size+2)^5*M^k := by
  let P := k+B.size+2
  let L := RetainedEqualCopyCosts.levelConstant r t (a*b) (b*c) (c*a)
  let S := BinaryAddressedWidth.slope a b c r t+1
  have hP : 1≤P := by dsimp [P];omega
  have hkp : k+2≤P := by dsimp [P];omega
  have hrec := BinaryRecursiveUniform.recurrence_bounds ht d M hM hg hAB hBC hCA k
  simp only [prod,fin] at hrec
  have hcontrol : RetainedEqualCopyCosts.control r t (a*b) (b*c) (c*a) k≤L*(k+1)*M^k :=
    (Nat.le_add_left _ _).trans hrec
  have houtput := Nat.pow_le_pow_left hCA k
  have hfactor : RetainedEqualCopyCosts.control r t (a*b) (b*c) (c*a) k+2*t*(c*a)^k≤
      (L+2*t)*(k+2)*M^k := by
    have hh := Nat.mul_le_mul_left (2*t) houtput
    have he : M^k≤(k+2)*M^k := Nat.le_mul_of_pos_left _ (by omega)
    have hh' := Nat.mul_le_mul_left (2*t) he
    nlinarith
  have hu := BinaryAddressedWidth.unit_bound a b c r t k
  change _≤131072*S^2*(k+2)^4 at hu
  have hover := Nat.mul_le_mul hfactor hu
  have hover' : (RetainedEqualCopyCosts.control r t (a*b) (b*c) (c*a) k+2*t*(c*a)^k)*
      BinaryAddressedCosts.unit k (BinaryAddressedWidth.commonWidth a b c r t k)≤
      131072*(L+2*t)*S^2*P^5*M^k := by
    calc
      _≤((L+2*t)*(k+2)*M^k)*(131072*S^2*(k+2)^4) := hover
      _=131072*(L+2*t)*S^2*(k+2)^5*M^k := by ring
      _≤131072*(L+2*t)*S^2*P^5*M^k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkp 5))
  have hold := BinaryRecursiveUniform.execute_bits ht d M hM hg hAB hBC hCA k B hB x y hx hy
  have hP3 : (k+B.size+1)^3≤P^5 := by
    calc
      _≤P^3 := Nat.pow_le_pow_left (by dsimp [P];omega) 3
      _≤P^5 := Nat.pow_le_pow_right hP (by decide)
  have hold' := hold.trans (Nat.mul_le_mul_right (M^k) (Nat.mul_le_mul_left _ hP3))
  have hh := BinaryAddressedRecovery.execute_overhead ha hb hc ht d k x y
  change _≤constant d*P^5*M^k
  dsimp only [constant]
  change _≤(BinaryRecursiveUniform.constant d+131072*(L+2*t)*S^2)*P^5*M^k
  nlinarith

#print axioms execute_bits
end ThinMatrix.BinaryAddressedUniform
