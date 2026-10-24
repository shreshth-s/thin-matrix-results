import SharedPrefixStorageBounds

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ThinMatrix.SharedCompletionWidths
open CompactBlocks (blockCount)

theorem span_bound (M D Q A Z X : ℕ) (hX : 1 ≤ X) (hA : 0 < A) (hZ : 0 < Z)
    (hM : M ≤ X) (hD : D ≤ X) (hQ : Q ≤ X) (ha : A ≤ X) (hz : Z ≤ X) :
    SharedFullyAddressedBatch.addressSpan M D Q A Z ≤ 12*X := by
  have hr : blockCount M A ≤ M := (ceilDiv_le_iff_le_mul hA).mpr (Nat.le_mul_of_pos_left _ hA)
  have hc : blockCount Q Z ≤ Q := (ceilDiv_le_iff_le_mul hZ).mpr (Nat.le_mul_of_pos_left _ hZ)
  have hpr := SharedFullyPrefixSchedule.chunk_rows M A
  have hpc := SharedFullyPrefixSchedule.chunk_rows Q Z
  change SharedAddressedBatch.addressSpan M D Q A Z ≤ _
  unfold SharedAddressedBatch.addressSpan
  omega

theorem span_size (M D Q A Z U : ℕ) (hA : 0 < A) (hZ : 0 < Z)
    (hM : M ≤ 2^U) (hD : D ≤ 2^U) (hQ : Q ≤ 2^U) (ha : A ≤ 2^U) (hz : Z ≤ 2^U) :
    (SharedFullyAddressedBatch.addressSpan M D Q A Z).size ≤ U+5 := by
  have hh := span_bound M D Q A Z (2^U) (one_le_pow₀ (by decide)) hA hZ hM hD hQ ha hz
  have hpow : 12*2^U ≤ 2^(U+4) := by rw [pow_add];norm_num;nlinarith
  have hs := (Nat.size_le_size (hh.trans hpow)).trans_eq Nat.size_pow
  omega

/-- Register values ≤2^U may have U+1 bits. The inclusive endpoint is
retained separately from the heap-address bound. -/
def controlPrice (U : ℕ) := BackendScalarBits.addressedUnit (U+1) (10*U+29)

theorem price_polynomial (U : ℕ) : controlPrice U ≤ 108900*(U+1)^2 := by
  unfold controlPrice BackendScalarBits.addressedUnit BackendScalarBits.scalarUnit
  have hh : (U+1)+(10*U+29)+1+1 ≤ 33*(U+1) := by omega
  have hp := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hh 2)
  nlinarith

theorem covers (U x j : ℕ) (hx : x ≤ 2^U) (hj : j.size ≤ 10*U+29) :
    BackendScalarBits.addressedUnit x.size j.size ≤ controlPrice U := by
  have hs := (Nat.size_le_size hx).trans_eq Nat.size_pow
  unfold controlPrice BackendScalarBits.addressedUnit BackendScalarBits.scalarUnit
  gcongr

#print axioms span_bound
#print axioms span_size
#print axioms price_polynomial
#print axioms covers
end ThinMatrix.SharedCompletionWidths
