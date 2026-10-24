import HalfSourceHighVolume
import ParameterExecution

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace ThinMatrix.HalfSourceHighCounters
open BinaryCroppedHighEncoder BinaryCroppedHighInput BinaryHighTable
noncomputable section

 theorem base_pos (L m t : ℕ) : 1 ≤ HighBaseEncoder.baseCount L m t := by
  apply Nat.one_le_of_lt
  unfold HighBaseEncoder.baseCount
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨CappedEnumeration.zeroWord (2*L),HighBaseEncoder.zero_admissible L m t⟩⟩

 def encoderUnit (L cap A : ℕ) : ℕ :=
  10*(cap.size+1)^2+2+testBudget L cap+BackendScalarBits.backendScalarUnit A.size+
    14*L+14+BinaryHighCost.storedFactor L A*encoderShape L

 theorem encoder_budget (L m t q cap A : ℕ) (hq : 1 ≤ q) :
    BinaryCroppedHighEncoder.totalBudget L m t q cap A ≤ q*encoderUnit L cap A*HighBaseEncoder.baseCount L m t := by
  have hb := base_pos L m t
  have hsetup := Nat.mul_le_mul_right (10*(cap.size+1)^2+2) (Nat.mul_le_mul hq hb)
  have hrest := Nat.mul_le_mul_right (testBudget L cap+12*L+9) hq
  have hscaled := Nat.mul_le_mul_right (HighBaseEncoder.baseCount L m t) hrest
  unfold BinaryCroppedHighEncoder.totalBudget payloadBudget encoderUnit
  nlinarith

 def fftUnit (q A : ℕ) : ℕ := 295147905179352825856*(q.log2+3)*(q.log2+A.log2+102)^10
 def boxUnit (L q A : ℕ) : ℕ := (2*L+1)^2*
  (ArrayKeys.highLayerFactor L 1 0*arithmeticUnit (5^(2*L+1)*(q*A^2)).size+
    fftUnit q A+12*L+5+StoredHighDP.guardTests L)

 theorem layer_factor (L q : ℕ) (hq : 1 ≤ q) :
    ArrayKeys.highLayerFactor L q 0 ≤ q*ArrayKeys.highLayerFactor L 1 0 := by
  have hh := Nat.mul_le_mul_right (ArrayKeys.highLayerFactor L 0 0) hq
  unfold ArrayKeys.highLayerFactor at *
  nlinarith

 theorem base_budget (L q A : ℕ) (hq : 1 ≤ q) :
    baseBudget L q A ≤ q*(fftUnit q A+12*L+5+StoredHighDP.guardTests L) := by
  have hh := Nat.mul_le_mul_right (12*L+2+StoredHighDP.guardTests L) hq
  unfold baseBudget fftWorkBound fftUnit
  nlinarith

 theorem box_budget (L m t q A : ℕ) (hq : 1 ≤ q) :
    preparationBudget L m t q A ≤ q*HighBaseEncoder.baseCount L m t*boxUnit L q A := by
  have hf := Nat.mul_le_mul_right (arithmeticUnit (5^(2*L+1)*(q*A^2)).size) (layer_factor L q hq)
  have hb := base_budget L q A hq
  have hh := Nat.mul_le_mul_left ((2*L+1)^2*HighBaseEncoder.baseCount L m t) (Nat.add_le_add hf hb)
  unfold preparationBudget boxUnit HighBaseEncoder.baseCount at *
  nlinarith

 theorem table_width (L q A : ℕ) : (5^(2*L+1)*(q*A^2)).size ≤ 6*L+q.size+2*A.size+5 := by
  have h1 := ParameterExecution.size_mul (5^(2*L+1)) (q*A^2)
  have h2 := ParameterExecution.size_pow 5 (2*L+1)
  have h3 := ParameterExecution.size_mul q (A^2)
  have h4 := ParameterExecution.size_pow A 2
  rw [show (5:ℕ).size=3 by decide] at h2
  omega

 theorem magnitude_width (L A : ℕ) : (BinaryCroppedHighBoxes.magnitude L A).size ≤ 6*L+A.size+2 := by
  have hp : (8^(2*L)).size=6*L+1 := by
    rw [show (8:ℕ)=2^3 by decide,←pow_mul,Nat.size_pow]
    congr 1
    ring
  have h1 := ParameterExecution.size_mul (8^(2*L)) A
  have h2 := ParameterExecution.size_succ (8^(2*L)*A)
  unfold BinaryCroppedHighBoxes.magnitude
  omega

#print axioms base_pos
#print axioms encoder_budget
#print axioms layer_factor
#print axioms base_budget
#print axioms box_budget
#print axioms table_width
#print axioms magnitude_width
end
end ThinMatrix.HalfSourceHighCounters
