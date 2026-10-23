import BinaryRecursiveCost

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Uniform bounds for the complete scalar binary evaluator. The fixed base,
cleared coefficient encodings, denominator powers, partial sums and exact
output divisions are included. Native indexed controls are bounded separately;
this module does not equate those controls to binary address work. -/
namespace ThinMatrix.BinaryRecursiveUniform
open scoped BigOperators
open RecursiveTable (Layout Table read store)
open RetainedEqualCopy (Base copies)
open RetainedEqualCopyCosts BinaryRecursiveCost
open BinaryCell BinaryRetainedBounds
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K] {r t : ℕ}

def slope {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) : ℕ :=
  4*(growth (ClearedRecursiveBase.encode d).value).size+(ClearedRecursiveBase.common d^3).size+4

theorem width_bound {a : Layout I} {b : Layout J} {c : Layout K}
    (d : Base r t a b c ℚ) (k B : ℕ) : width d k B+1 ≤ slope d*(k+B.size+1) := by
  unfold width slope
  nlinarith

def constant {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) :=
  (ClearedRecursiveBase.encode d).bitSteps+
    (BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)).bitSteps+
    800*(levelConstant r t a.size b.size c.size+1)*(slope d)^2+1024*t*(slope d)^2

theorem recurrence_bounds {a : Layout I} {b : Layout J} {c : Layout K}
    (ht : 0 < t) (d : Base r t a b c ℚ) (M : ℕ) (hM : 1 ≤ M)
    (hg : (r+t-1)/t ≤ M) (ha : a.size ≤ M) (hb : b.size ≤ M) (hc : c.size ≤ M) (k : ℕ) :
    arithmetic r t a.size b.size c.size k+control r t a.size b.size c.size k ≤
      levelConstant r t a.size b.size c.size*(k+1)*M^k := by
  have hh := run_work_bound a b c ht d M hM hg ha hb hc k
    (store (copies t a k) (fun _ => (0:ℚ))) (store (copies t b k) (fun _ => (0:ℚ)))
  simpa only [run_arithmetic,run_control] using hh

theorem bits_bound {a : Layout I} {b : Layout J} {c : Layout K}
    (ht : 0 < t) (d : Base r t a b c ℚ) (M : ℕ) (hM : 1 ≤ M)
    (hg : (r+t-1)/t ≤ M) (ha : a.size ≤ M) (hb : b.size ≤ M) (hc : c.size ≤ M)
    (k B : ℕ) : bits d k B ≤ constant d*(k+B.size+1)^3*M^k := by
  let P := k+B.size+1
  let L := levelConstant r t a.size b.size c.size
  have hP : 1 ≤ P := by dsimp [P];omega
  have hm : 1 ≤ M^k := one_le_pow₀ hM
  have har : arithmetic r t a.size b.size c.size k ≤ L*(k+1)*M^k :=
    (Nat.le_add_right _ _).trans (recurrence_bounds ht d M hM hg ha hb hc k)
  have hsum : arithmetic r t a.size b.size c.size k+k ≤ (L+1)*P*M^k := by
    have hkP : k+1 ≤ P := by dsimp [P];omega
    have hmain := har.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left L hkP))
    have hk : k ≤ P*M^k := (show k ≤ P by dsimp [P];omega).trans (Nat.le_mul_of_pos_right _ hm)
    nlinarith
  have hw : (width d k B+1)^2 ≤ (slope d)^2*P^2 := by
    simpa only [mul_pow] using Nat.pow_le_pow_left (width_bound d k B) 2
  have hmout := Nat.pow_le_pow_left hc k
  have hP23 : P^2 ≤ P^3 := Nat.pow_le_pow_right hP (by decide)
  have hP3 : 1 ≤ P^3*M^k := by simpa only [one_mul] using Nat.mul_le_mul (one_le_pow₀ hP : 1 ≤ P^3) hm
  have hfixed := Nat.mul_le_mul_left ((ClearedRecursiveBase.encode d).bitSteps+
    (BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)).bitSteps) hP3
  simp only [mul_one] at hfixed
  have hmiddle := Nat.mul_le_mul hsum (Nat.mul_le_mul_left 800 hw)
  have hout := Nat.mul_le_mul (Nat.mul_le_mul_left t hmout) (Nat.mul_le_mul_left 1024 hw)
  have hout' := Nat.mul_le_mul_left (1024*t*(slope d)^2*M^k) hP23
  dsimp only [bits,constant]
  simp only [BackendScalarBits.backendScalarUnit,BackendScalarBits.scalarUnit]
  change _ ≤ _*P^3*M^k
  nlinarith

theorem execute_bits {a : Layout I} {b : Layout J} {c : Layout K}
    (ht : 0 < t) (d : Base r t a b c ℚ) (M : ℕ) (hM : 1 ≤ M)
    (hg : (r+t-1)/t ≤ M) (ha : a.size ≤ M) (hb : b.size ≤ M) (hc : c.size ≤ M)
    (k B : ℕ) (hB : 1 ≤ B) (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell)
    (hx : Bounded x B) (hy : Bounded y B) :
    (BinaryRecursiveRecovery.execute ht d k x y).bitSteps ≤ constant d*(k+B.size+1)^3*M^k :=
  (BinaryRecursiveCost.execute_bits ht d k B hB x y hx hy).trans
    (bits_bound ht d M hM hg ha hb hc k B)

def controlConstant {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) :=
  (ClearedRecursiveBase.encode d).control+levelConstant r t a.size b.size c.size+40*t+34

theorem execute_control {a : Layout I} {b : Layout J} {c : Layout K}
    (ht : 0 < t) (d : Base r t a b c ℚ) (M : ℕ) (hM : 1 ≤ M)
    (hg : (r+t-1)/t ≤ M) (ha : a.size ≤ M) (hb : b.size ≤ M) (hc : c.size ≤ M)
    (k : ℕ) (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell) :
    (BinaryRecursiveRecovery.execute ht d k x y).control ≤ controlConstant d*(k+1)*M^k := by
  have hm : 1 ≤ M^k := one_le_pow₀ hM
  have hrec : control r t a.size b.size c.size k ≤
      levelConstant r t a.size b.size c.size*(k+1)*M^k :=
    (Nat.le_add_left _ _).trans (recurrence_bounds ht d M hM hg ha hb hc k)
  have hout := Nat.pow_le_pow_left hc k
  have hh : 1 ≤ (k+1)*M^k := by nlinarith
  have hk : k ≤ (k+1)*M^k := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hm)
  have hf := Nat.mul_le_mul_left ((ClearedRecursiveBase.encode d).control+26+40*t) hh
  have hout' : 40*t*M^k ≤ 40*t*(k+1)*M^k := by
    simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using
      Nat.mul_le_mul_left (40*t*M^k) (show 1 ≤ k+1 by omega)
  simp only [BinaryRecursiveRecovery.execute,BinaryRecursiveRecovery.power_control,
    BinaryRecursiveRecovery.recover_control,BinaryRetainedEqualCopy.run_control,copies,
    RecursiveTable.prod,RecursiveTable.fin,RecursiveTable.power_size,controlConstant]
  nlinarith

#print axioms width_bound
#print axioms recurrence_bounds
#print axioms bits_bound
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.BinaryRecursiveUniform
