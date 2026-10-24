import HalfSourcePrefixVolume

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThinMatrix.HalfSourceBatchCopyVolume
open HalfSourcePrefixVolume GraphAdaptiveBatchSources

 theorem matrix_control (P ell r C : ℕ) (hC : 1 ≤ C) :
    2^ell*PrefixCompletionMatrices.controlBudget P (CappedSubsetList.count ell r) C ≤
      groups P ell r*C*(P+1)*240 := by
  have hs : 1 ≤ CappedSubsetList.count ell r := Nat.one_le_of_lt (CappedSubsetList.count_pos _ _)
  have h1 := Nat.mul_le_mul_right 100 hC
  have h2 := Nat.mul_le_mul_right 100 (Nat.mul_le_mul hs hC)
  have hh : CappedSubsetList.count ell r*(40*C+100)+100 ≤ CappedSubsetList.count ell r*C*240 := by nlinarith
  have hg := Nat.mul_le_mul_left (2^ell*(P+1)*4^P) hh
  unfold PrefixCompletionMatrices.controlBudget groups
  nlinarith

def batchControlUnit (P ell : ℕ) : ℕ :=
  (P+1)*240+2*((ell+1)*(8*ell+32)+4)+300

 theorem batch_control (B P ell r C : ℕ) (hC : 1 ≤ C) (hB : 1 ≤ B) :
    48*B+8+(B*(2^ell*(PrefixCompletionMatrices.controlBudget P (CappedSubsetList.count ell r) C+32)+40)+
      GroupedPreparation.keyBudget ell r+GroupedPreparation.keyBudget ell ell+28)+8 ≤
        B*C*groups P ell r*batchControlUnit P ell := by
  have hx : 1 ≤ 4^P := Nat.one_le_pow _ _ (by omega)
  have hy : 1 ≤ 2^ell := Nat.one_le_pow _ _ (by omega)
  have hz : 1 ≤ CappedSubsetList.count ell r := Nat.one_le_of_lt (CappedSubsetList.count_pos _ _)
  have hg := groups_pos P ell r
  have hm := Nat.mul_le_mul_left B (matrix_control P ell r C hC)
  have hbC := Nat.mul_le_mul hB hC
  have hzc := Nat.mul_le_mul hz hC
  have hgroup := Nat.mul_le_mul hbC hg
  have hk := Nat.mul_le_mul_left (((ell+1)*(8*ell+32)+4)*CappedSubsetList.count ell r) (Nat.mul_le_mul hbC (Nat.mul_le_mul hx hy))
  have hk2 := Nat.mul_le_mul_left (((ell+1)*(8*ell+32)+4)*2^ell) (Nat.mul_le_mul hbC (Nat.mul_le_mul hx hz))
  have hrest := Nat.mul_le_mul_left (B*2^ell) (Nat.mul_le_mul hx hzc)
  have hBrest := Nat.mul_le_mul_left B (Nat.mul_le_mul hC hg)
  unfold GroupedPreparation.keyBudget
  rw [GroupedPreparation.count_full]
  unfold groups batchControlUnit at *
  nlinarith

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
  (stored : Stored f p) (hc : Correct f p hm input bandL bandR stored)

 theorem actual_bits (index : GraphPrefixCompletion.Index p.L p.m p.t) :
    (prepare f p hm input bandL bandR stored hc index).bitSteps ≤
      CompactBlocks.blockCount n h*((p.m+1)*f.cyclic)*groups (P f p index) (S f p index) (R f p index)*
        BackendScalarBits.backendScalarUnit (2^(P f p index)*windowMagnitude f p).size := by
  have hh := prepare_bits f p hm input bandL bandR stored hc index
  rw [completion_copy_bits] at hh
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

 theorem actual_control (index : GraphPrefixCompletion.Index p.L p.m p.t)
    (hB : 1 ≤ CompactBlocks.blockCount n h) :
    (prepare f p hm input bandL bandR stored hc index).control ≤
      CompactBlocks.blockCount n h*((p.m+1)*f.cyclic)*groups (P f p index) (S f p index) (R f p index)*
        batchControlUnit (P f p index) (S f p index) := by
  have hq : 1 ≤ f.cyclic := Nat.one_le_of_lt f.cyclic_pos
  exact (prepare_control f p hm input bandL bandR stored hc index).trans
    (batch_control _ _ _ _ _ (by nlinarith) hB)

#print axioms matrix_control
#print axioms batch_control
#print axioms actual_bits
#print axioms actual_control
end ThinMatrix.HalfSourceBatchCopyVolume
