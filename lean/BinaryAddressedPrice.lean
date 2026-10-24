import BinaryAddressedStorage

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Closed pricing of the retained recursive matrix's bounded indexed
controls, using the same layout-majorant model as BinaryAlignedAPSPTheorem.
The public widths are derived from the fixed base, selected depth and original
input magnitude. They do not assert a compiler/allocator realization. -/
namespace ThinMatrix.BinaryAddressedPrice
open BinaryCell RetainedEqualCopy
open RecursiveTable (Table prod fin)
open BinaryAddressedStorage
variable {a b c r t n m p : ℕ}

def scalarWork (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M k H : ℕ) := BinaryAddressedControl.workConstant d*(k+H.size+2)^5*M^k

def storageSlope (r t a b c M : ℕ) := (matrixConstant r t a b c).size+M.size+3

theorem matrix_width (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (n m p k : ℕ) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k) :
    (matrixCells r t a b c n m p k).size≤ storageSlope r t a b c M*(k+1) := by
  have hh := matrix_size ht d M hM hg hAB hBC hCA n m p k hn hm hp
  have hk : (k+1).size≤k+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold storageSlope
  nlinarith

def fieldWidth (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M k H : ℕ) :=
  (scalarWork d M k H).size+BinaryRecursiveCost.width d k H+
    BinaryAddressedWidth.commonWidth a b c r t k+k+8

def fieldSlope (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) :=
  (BinaryAddressedControl.workConstant d).size+M.size+7+
    BinaryRecursiveUniform.slope d+BinaryAddressedWidth.slope a b c r t+9

theorem field_width (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M k H : ℕ) : fieldWidth d M k H≤fieldSlope d M*(k+H.size+2) := by
  let P := k+H.size+2
  have hP : 1≤P := by dsimp [P];omega
  have hs : P.size≤P := Nat.size_le.mpr Nat.lt_two_pow_self
  have hpow := BinaryRetainedBounds.size_power P 5
  have hMpow := BinaryRetainedBounds.size_power M k
  have hprod := BinaryMultiplierAdapter.size_mul (BinaryAddressedControl.workConstant d*P^5) (M^k)
  have hinner := BinaryMultiplierAdapter.size_mul (BinaryAddressedControl.workConstant d) (P^5)
  have hbudget : (scalarWork d M k H).size≤
      ((BinaryAddressedControl.workConstant d).size+M.size+7)*P := by
    unfold scalarWork
    change (BinaryAddressedControl.workConstant d*P^5*M^k).size≤_
    have hk : k≤P := by dsimp [P];omega
    nlinarith [Nat.mul_le_mul_right M.size hk]
  have hscalar := BinaryRecursiveUniform.width_bound d k H
  have hsmall : k+H.size+1≤P := by dsimp [P];omega
  have hscalar' := hscalar.trans (Nat.mul_le_mul_left (BinaryRecursiveUniform.slope d) hsmall)
  have haddr : BinaryAddressedWidth.commonWidth a b c r t k≤
      BinaryAddressedWidth.slope a b c r t*P := by
    unfold BinaryAddressedWidth.commonWidth
    have hh : k+2≤P := by dsimp [P];omega
    simpa only [mul_comm] using Nat.mul_le_mul_right (BinaryAddressedWidth.slope a b c r t) hh
  unfold fieldWidth fieldSlope
  change _≤_*P
  have hk : k+8≤9*P := by dsimp [P];omega
  nlinarith

def addressWidth (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M n m p k H : ℕ) :=
  8+(matrixCells r t a b c n m p k).size+(fieldWidth d M k H).size

theorem address_width (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (n m p k H : ℕ) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k) :
    addressWidth d M n m p k H≤(storageSlope r t a b c M+fieldSlope d M+8)*(k+H.size+2) := by
  have hc := matrix_width ht d M hM hg hAB hBC hCA n m p k hn hm hp
  have hf := field_width d M k H
  have hs : (fieldWidth d M k H).size≤fieldWidth d M k H := Nat.size_le.mpr Nat.lt_two_pow_self
  have hc' := hc.trans (Nat.mul_le_mul_left (storageSlope r t a b c M) (show k+1≤k+H.size+2 by omega))
  unfold addressWidth
  nlinarith

def price (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M n m p k H : ℕ) :=
  BackendScalarBits.addressedUnit (fieldWidth d M k H) (addressWidth d M n m p k H)

def priceConstant (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) := 100*(storageSlope r t a b c M+2*fieldSlope d M+10)^2

theorem price_bound (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (n m p k H : ℕ) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k) :
    price d M n m p k H≤priceConstant d M*(k+H.size+2)^2 := by
  have hf := field_width d M k H
  have ha := address_width ht d M hM hg hAB hBC hCA n m p k H hn hm hp
  have hsum : fieldWidth d M k H+addressWidth d M n m p k H+2≤
      (storageSlope r t a b c M+2*fieldSlope d M+10)*(k+H.size+2) := by nlinarith
  have hh := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hsum 2)
  simpa only [price,BackendScalarBits.addressedUnit,BackendScalarBits.scalarUnit,
    priceConstant,mul_pow,mul_assoc,Nat.add_assoc,Nat.reduceAdd] using hh

theorem execute_priced_work (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (k H : ℕ) (hH : 1≤H) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (BinaryAddressedMatrix.execute ha hb hc ht d k hn hp x y).bitSteps+
      price d M n m p k H*(BinaryAddressedMatrix.execute ha hb hc ht d k hn hp x y).control≤
      (priceConstant d M+1)*BinaryAddressedControl.workConstant d*(k+H.size+2)^7*M^k := by
  let out := BinaryAddressedMatrix.execute ha hb hc ht d k hn hp x y
  let P := k+H.size+2
  have hw := BinaryAddressedControl.execute_work ha hb hc ht d M hM hg hAB hBC hCA k H hH hn hm hp x y hx hy
  have hp' := price_bound ht d M hM hg hAB hBC hCA n m p k H hn hm hp
  have hP : 1≤P^2 := one_le_pow₀ (by dsimp [P];omega)
  have hprice : price d M n m p k H+1≤(priceConstant d M+1)*P^2 := by
    change price d M n m p k H≤priceConstant d M*P^2 at hp'
    nlinarith
  have hh := Nat.mul_le_mul hprice hw
  change out.bitSteps+price d M n m p k H*out.control≤_
  have hstart : out.bitSteps+price d M n m p k H*out.control≤
      (price d M n m p k H+1)*(out.bitSteps+out.control) := by nlinarith
  apply hstart.trans
  apply hh.trans_eq
  change ((priceConstant d M+1)*P^2)*(BinaryAddressedControl.workConstant d*P^5*M^k)=
    (priceConstant d M+1)*BinaryAddressedControl.workConstant d*P^7*M^k
  ring

#print axioms matrix_width
#print axioms field_width
#print axioms address_width
#print axioms price_bound
#print axioms execute_priced_work
end ThinMatrix.BinaryAddressedPrice
