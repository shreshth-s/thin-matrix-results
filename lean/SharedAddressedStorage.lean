import BinaryAddressedStorage

set_option autoImplicit false
set_option maxHeartbeats 1400000

/-! Whole-batch retained address width. Every chunk and recursive product
workspace is counted, including inactive final padding; no single-product
address bound is substituted for the combined collection. -/
namespace ThinMatrix.SharedAddressedStorage
open BinaryAddressedStorage
open CompactBlocks (blockCount)

/-- Coarse polynomial storage is sufficient for address width; it does not
change the finer running-time budget or allocate this majorant. -/
theorem batch_bound (N D P A C R X : ℕ) (hX : 1≤X) (hA : 0<A) (hC : 0<C)
    (hN : N≤X) (hD : D≤X) (hP : P≤X) (ha : A≤X) (hc : C≤X) :
    batchCells N D P A C R≤8*X^4*(R+1) := by
  have hr : blockCount N A≤N := (ceilDiv_le_iff_le_mul hA).mpr (Nat.le_mul_of_pos_left _ hA)
  have hs : blockCount P C≤P := (ceilDiv_le_iff_le_mul hC).mpr (Nat.le_mul_of_pos_left _ hC)
  have hp2 : N*P≤X^2 := by simpa only [pow_two] using Nat.mul_le_mul hN hP
  have hnd : N*D≤X^2 := by simpa only [pow_two] using Nat.mul_le_mul hN hD
  have hdp : D*P≤X^2 := by simpa only [pow_two] using Nat.mul_le_mul hD hP
  have hleft : blockCount N A*A*D≤X^3 := by
    calc
      _≤X*X*X := Nat.mul_le_mul (Nat.mul_le_mul (hr.trans hN) ha) hD
      _=_ := by ring
  have hright : blockCount P C*D*C≤X^3 := by
    calc
      _≤X*X*X := Nat.mul_le_mul (Nat.mul_le_mul (hs.trans hP) hD) hc
      _=_ := by ring
  have hproducts : blockCount N A*blockCount P C*A*C≤X^4 := by
    calc
      _≤X*X*X*X := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hr.trans hN) (hs.trans hP)) ha) hc
      _=_ := by ring
  have htrees : blockCount N A*blockCount P C*(R+1)≤X^2*(R+1) :=
    Nat.mul_le_mul_right _ ((Nat.mul_le_mul hr hs).trans hp2)
  have h24 : X^2≤X^4 := Nat.pow_le_pow_right hX (by decide)
  have h34 : X^3≤X^4 := Nat.pow_le_pow_right hX (by decide)
  have h1 : 1≤X^4 := one_le_pow₀ hX
  have htrees' := htrees.trans (Nat.mul_le_mul_right (R+1) h24)
  unfold batchCells SharedFullyAddressedBatch.outerCells
  nlinarith

theorem batch_pow (N D P A C R W V : ℕ) (hA : 0<A) (hC : 0<C)
    (hN : N≤2^W) (hD : D≤2^W) (hP : P≤2^W) (ha : A≤2^W) (hc : C≤2^W)
    (hR : R≤2^V) : batchCells N D P A C R≤2^(4*W+V+4) := by
  have hb := batch_bound N D P A C R (2^W) (one_le_pow₀ (by decide)) hA hC hN hD hP ha hc
  have hV : 1≤2^V := one_le_pow₀ (by decide)
  have hR' : R+1≤2^(V+1) := by rw [pow_succ];omega
  calc
    _≤8*(2^W)^4*(R+1) := hb
    _≤8*(2^W)^4*2^(V+1) := Nat.mul_le_mul_left _ hR'
    _=_ := by rw [show (8:ℕ)=2^3 by decide,←pow_mul,←pow_add,←pow_add];congr 1;ring

theorem bit_heap_pow (N D P A C R bitWidth W V F : ℕ) (hA : 0<A) (hC : 0<C)
    (hN : N≤2^W) (hD : D≤2^W) (hP : P≤2^W) (ha : A≤2^W) (hc : C≤2^W)
    (hR : R≤2^V) (hF : bitWidth≤2^F) :
    bitCells (batchCells N D P A C R) bitWidth≤2^(4*W+V+F+11) := by
  have hb := batch_pow N D P A C R W V hA hC hN hD hP ha hc hR
  have hbp : batchCells N D P A C R+1≤2^(4*W+V+5) := by
    have h1 : 1≤2^(4*W+V+4) := one_le_pow₀ (by decide)
    have he : 4*W+V+5=(4*W+V+4)+1 := by omega
    rw [he,pow_succ];omega
  have hfp : bitWidth+1≤2^(F+1) := by
    have h1 : 1≤2^F := one_le_pow₀ (by decide)
    rw [pow_succ];omega
  unfold bitCells
  calc
    _≤32*2^(4*W+V+5)*2^(F+1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hbp) hfp
    _=_ := by rw [show (32:ℕ)=2^5 by decide,←pow_add,←pow_add];congr 1;ring

theorem address_width (N D P A C R bitWidth W V F j : ℕ) (hA : 0<A) (hC : 0<C)
    (hN : N≤2^W) (hD : D≤2^W) (hP : P≤2^W) (ha : A≤2^W) (hc : C≤2^W)
    (hR : R≤2^V) (hF : bitWidth≤2^F)
    (hj : j<bitCells (batchCells N D P A C R) bitWidth) : j.size≤4*W+V+F+12 := by
  have hh := (Nat.size_le_size (hj.le.trans
    (bit_heap_pow N D P A C R bitWidth W V F hA hC hN hD hP ha hc hR hF))).trans_eq Nat.size_pow
  omega

#print axioms batch_bound
#print axioms batch_pow
#print axioms bit_heap_pow
#print axioms address_width
end ThinMatrix.SharedAddressedStorage
