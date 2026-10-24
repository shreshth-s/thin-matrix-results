import GraphAdaptivePrefixCosts
import GraphAdaptiveBatchSources
import ParameterExecution

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Explicit prefix and matrix-copy counters divided by their combinatorial
volume. Cyclic coefficient count remains linear; word magnitudes enter only
through bit length. These elementary bounds feed the channel-type sum. -/
namespace ThinMatrix.HalfSourcePrefixVolume
open BinaryGroupedCoordinates

def groups (P ell r : ℕ) : ℕ := 4^P*2^ell*CappedSubsetList.count ell r

theorem scalar_mono {a b : ℕ} (h : a≤b) :
    BackendScalarBits.backendScalarUnit a ≤ BackendScalarBits.backendScalarUnit b := by
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  gcongr

def bitUnit (P ell W : ℕ) : ℕ := addressBudget ell+addressBudget (P+ell)+
  BackendScalarBits.backendScalarUnit W+5*P*BackendScalarBits.backendScalarUnit (P+W+1)

theorem prefix_bits (P ell r C A W : ℕ) (hC : 1≤C) (hA : A.size≤W) :
    CappedPrefixProgram.bitBudget P ell r C A ≤ groups P ell r*C*bitUnit P ell W := by
  have hp : (3:ℕ)^P≤4^P := Nat.pow_le_pow_left (by omega) P
  have hw := (ParameterExecution.size_mul (2^P) A).trans
    (show (2^P).size+A.size≤P+W+1 by rw [Nat.size_pow]; omega)
  have ha := scalar_mono hA
  have he := scalar_mono hw
  have hd : RetainedCappedGroups.datumBitBudget P ell C A ≤
      C*(addressBudget ell+addressBudget (P+ell)+BackendScalarBits.backendScalarUnit W) := by
    unfold RetainedCappedGroups.datumBitBudget
    nlinarith
  have hh := Nat.mul_le_mul hp hd
  have hm := Nat.mul_le_mul_left (2^ell*CappedSubsetList.count ell r) hh
  have hq := Nat.mul_le_mul_left (2^ell*CappedSubsetList.count ell r*P*4^P*C*5) he
  unfold CappedPrefixProgram.bitBudget RetainedCappedGroups.bitBudget RetainedPrefixEncoder.bitBudget
    RetainedPrefixEncoder.unit groups bitUnit
  nlinarith

theorem address_polynomial (n : ℕ) : addressBudget n ≤ 20000*(n+1)^3 := by
  unfold addressBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  nlinarith [Nat.zero_le (n^3)]

theorem bitUnit_polynomial (P ell W : ℕ) (hP : P+ell≤W) : bitUnit P ell W ≤ 100000*(W+1)^3 := by
  have ha := address_polynomial ell
  have hb := address_polynomial (P+ell)
  have h1 := Nat.pow_le_pow_left (show ell+1≤W+1 by omega) 3
  have h2 := Nat.pow_le_pow_left (show P+ell+1≤W+1 by omega) 3
  have hh := scalar_mono (show P+W+1≤2*W+1 by omega)
  have hm := Nat.mul_le_mul_left (5*P) hh
  unfold bitUnit BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at *
  nlinarith

theorem prefix_polynomial_bits (P ell r C A W : ℕ) (hC : 1≤C) (hA : A.size≤W) (hP : P+ell≤W) :
    CappedPrefixProgram.bitBudget P ell r C A ≤ 100000*(W+1)^3*C*groups P ell r := by
  have h := (prefix_bits P ell r C A W hC hA).trans
    (Nat.mul_le_mul_left (groups P ell r*C) (bitUnit_polynomial P ell W hP))
  simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h

theorem completion_copy_bits (P ell r C A : ℕ) :
    2^ell*PrefixCompletionMatrices.bitBudget P (CappedSubsetList.count ell r) C A=
      groups P ell r*C*BackendScalarBits.backendScalarUnit A.size := by
  unfold PrefixCompletionMatrices.bitBudget groups
  ring

theorem groups_pos (P ell r : ℕ) : 1 ≤ groups P ell r := by
  unfold groups
  exact Nat.one_le_of_lt (Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)) (CappedSubsetList.count_pos _ _))

def controlUnit (P ell : ℕ) : ℕ :=
  2*((ell+1)*(8*ell+32)+4)+
  RetainedCappedGroups.datumControlBudget P ell 1+200*(P+1)+
  (P+1)*(112+1000*(P+1)^2)+500

theorem prefix_control (P ell r C : ℕ) (hC : 1 ≤ C) :
    CappedPrefixProgram.controlBudget P ell r C ≤ groups P ell r*C*controlUnit P ell := by
  have hx : 1 ≤ 4^P := Nat.one_le_pow _ _ (by omega)
  have hy : 1 ≤ 2^ell := Nat.one_le_pow _ _ (by omega)
  have hz : 1 ≤ CappedSubsetList.count ell r := Nat.one_le_of_lt (CappedSubsetList.count_pos _ _)
  have hp : 3^P ≤ 4^P := Nat.pow_le_pow_left (by omega) P
  have hd : RetainedCappedGroups.datumControlBudget P ell C ≤ C*RetainedCappedGroups.datumControlBudget P ell 1 := by
    unfold RetainedCappedGroups.datumControlBudget
    nlinarith
  have hdu := Nat.mul_le_mul hp (Nat.add_le_add hd (show 200*(P+1) ≤ C*(200*(P+1)) by nlinarith))
  have hm := Nat.mul_le_mul_left (2^ell*CappedSubsetList.count ell r) hdu
  have ht : 112*C+1000*(P+1)^2 ≤ C*(112+1000*(P+1)^2) := by nlinarith
  have htr := Nat.mul_le_mul_left (2^ell*CappedSubsetList.count ell r*(P+1)*4^P) ht
  have hg := groups_pos P ell r
  have hxy := Nat.mul_le_mul hx hy
  have hxyz := Nat.mul_le_mul hxy hz
  have hzC := Nat.mul_le_mul hz hC
  have hyzC := Nat.mul_le_mul hy hzC
  have hxC := Nat.mul_le_mul hx hC
  have hk := Nat.mul_le_mul_left (((ell+1)*(8*ell+32)+4)*CappedSubsetList.count ell r) (Nat.mul_le_mul hx (Nat.mul_le_mul hy hC))
  have hk2 := Nat.mul_le_mul_left (((ell+1)*(8*ell+32)+4)*2^ell) (Nat.mul_le_mul hx hzC)
  unfold CappedPrefixProgram.controlBudget RetainedCappedGroups.controlBudget
    GroupedPreparation.keyBudget RetainedPrefixEncoder.controlBudget
  rw [GroupedPreparation.count_full]
  unfold groups controlUnit
  nlinarith

theorem controlUnit_polynomial (P ell W : ℕ) (hP : P+ell ≤ W) :
    controlUnit P ell ≤ 10000*(W+1)^3 := by
  have h1 : P ≤ W := by omega
  have h2 : ell ≤ W := by omega
  have h3 := Nat.pow_le_pow_left (show P+1 ≤ W+1 by omega) 3
  unfold controlUnit RetainedCappedGroups.datumControlBudget
  nlinarith [Nat.zero_le (W^3)]

theorem prefix_polynomial_control (P ell r C W : ℕ) (hC : 1 ≤ C) (hP : P+ell ≤ W) :
    CappedPrefixProgram.controlBudget P ell r C ≤ 10000*(W+1)^3*C*groups P ell r := by
  exact (prefix_control P ell r C hC).trans (by
    have hh := Nat.mul_le_mul_left (groups P ell r*C) (controlUnit_polynomial P ell W hP)
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh)

#print axioms controlUnit_polynomial
#print axioms prefix_polynomial_control
#print axioms groups_pos
#print axioms prefix_control
#print axioms scalar_mono
#print axioms prefix_bits
#print axioms address_polynomial
#print axioms bitUnit_polynomial
#print axioms prefix_polynomial_bits
#print axioms completion_copy_bits
end ThinMatrix.HalfSourcePrefixVolume
