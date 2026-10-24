import BinaryAddressedMatrix

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! The explicit indexed-control counter of the addressed matrix program is
bounded independently of the scalar magnitudes. Combining it with the actual
binary work preserves the fixed-base growth rate. -/
namespace ThinMatrix.BinaryAddressedControl
open scoped BigOperators
open RecursiveTable (Table fin prod power)
open BinaryCell RetainedEqualCopy
variable {a b c r t n m p : ℕ}

def constant (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ) :=
  2*(BinaryRecursiveUniform.controlConstant d+216*t+120)

theorem execute_control (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (k : ℕ) (hn : n≤a^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell) :
    (BinaryAddressedMatrix.execute ha hb hc ht d k hn hp x y).control≤constant d*(k+2)^2*M^k := by
  have hrec := BinaryRecursiveUniform.execute_control ht d M hM hg hAB hBC hCA k
    (BinaryMatrixPowers.toWords (fin a) (fin b) k
      (PaddedMatrix.pad (power (fin a) k) (power (fin b) k) t n m x).value).value
    (BinaryMatrixPowers.toWords (fin b) (fin c) k
      (PaddedMatrix.pad (power (fin b) k) (power (fin c) k) t m p y).value).value
  have hm : 1≤M^k := one_le_pow₀ hM
  have hab := Nat.pow_le_pow_left hAB k
  have hbc := Nat.pow_le_pow_left hBC k
  have hca := Nat.pow_le_pow_left hCA k
  have hnp0 : n*p≤(c*a)^k := by simpa only [mul_pow,mul_comm] using Nat.mul_le_mul hn hp
  have hnp : n*p≤M^k := hnp0.trans hca
  have hpoly : 1≤(k+1)*M^k := by nlinarith
  have hlegacy : (PaddedMatrix.execute (fin a) (fin b) (fin c) ht d k hn hp x y).control≤
      (BinaryRecursiveUniform.controlConstant d+216*t+120)*(k+1)*M^k := by
    rw [BinaryAddressedMatrix.legacy_control]
    have ha' := Nat.mul_le_mul_left (88*t) hab
    have hb' := Nat.mul_le_mul_left (88*t) hbc
    have hc' := Nat.mul_le_mul_left (40*t) hca
    have hsum : 88*t*((a*b)^k+(b*c)^k)+40*t*(c*a)^k+40*n*p+80≤
        (216*t+120)*M^k := by nlinarith
    have hsum' := hsum.trans (Nat.le_mul_of_pos_left _ (show 1≤k+1 by omega))
    nlinarith
  have hh := (BinaryAddressedMatrix.execute_control ha hb hc ht d k hn hp x y).trans
    (Nat.mul_le_mul_left (2*(k+2)) hlegacy)
  apply hh.trans
  have hk : (k+2)*(k+1)≤(k+2)^2 := by nlinarith
  have hh' := Nat.mul_le_mul_right (M^k) (Nat.mul_le_mul_left
    (2*(BinaryRecursiveUniform.controlConstant d+216*t+120)) hk)
  simpa only [constant,mul_assoc,mul_left_comm,mul_comm] using hh'

def workConstant (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ) :=
  BinaryAddressedMatrix.constant d+constant d

theorem execute_work (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (k B : ℕ) (hB : 1≤B) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell)
    (hx : BinaryRetainedBounds.Bounded x B) (hy : BinaryRetainedBounds.Bounded y B) :
    (BinaryAddressedMatrix.execute ha hb hc ht d k hn hp x y).bitSteps+
      (BinaryAddressedMatrix.execute ha hb hc ht d k hn hp x y).control≤
      workConstant d*(k+B.size+2)^5*M^k := by
  have hbits := BinaryAddressedMatrix.execute_bits ha hb hc ht d M hM hg hAB hBC hCA k B hB hn hm hp x y hx hy
  have hcontrol := execute_control ha hb hc ht d M hM hg hAB hBC hCA k hn hp x y
  have hpow : (k+2)^2≤(k+B.size+2)^5 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hc' := hcontrol.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (constant d) hpow))
  unfold workConstant
  nlinarith

#print axioms execute_control
#print axioms execute_work
end ThinMatrix.BinaryAddressedControl
