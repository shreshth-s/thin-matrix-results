import HalfSourcePrefixVolume

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Actual adaptive-entry counters factored into the dense retained-root
volume and the selected capped-prefix volume. Coefficient count occurs once.
All units contain only dimensions, bit lengths, and fixed-degree arithmetic. -/
namespace ThinMatrix.HalfSourceAdaptiveVolume
open HalfSourcePrefixVolume

variable {L m C : ℕ}

def entryGroups (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) : ℕ :=
  groups (WindowPrefixProgram.prefixLength (L-m) ell) (WindowPrefixProgram.length (L-m) ell)
    (WindowPrefixProgram.cap (L-m) ell (m/2) (RetainedRootWindows.weights root.channel).value.1
      (RetainedRootWindows.weights root.channel).value.2)

def denseBitUnit (k m cap W : ℕ) : ℕ :=
  4*RetainedRootWindows.countBudget m+HalfSourceSuffixProgram.bitBudget k cap.size+
  (k+2)*(m+1)*BackendScalarBits.backendScalarUnit W+
  (k+1)*k*(3*BinaryGroupedCoordinates.addressBudget (2*k)+(m+1)*(5*BackendScalarBits.backendScalarUnit W))+
  (k+1)*(BinaryGroupedCoordinates.addressBudget (2*k)+(m+1)*BackendScalarBits.backendScalarUnit W)

theorem slots_le (k : ℕ) : RetainedRootWindows.slots k ≤ k+1 := by
  cases k <;> simp [RetainedRootWindows.slots]

theorem entry_prefix_bits (ell : ℕ) (root : RetainedResidualFamily.Entry L m C)
    (A W : ℕ) (hC : 1 ≤ C) (hA : A.size ≤ W) :
    GraphPrefixProgram.entryBitBudget ell (RetainedRootWindows.execute ell root).value A ≤
      RetainedRootWindows.slots (L-m)*(m+1)*C*entryGroups ell root*
        bitUnit (WindowPrefixProgram.prefixLength (L-m) ell) (WindowPrefixProgram.length (L-m) ell) W := by
  have hh := prefix_bits (WindowPrefixProgram.prefixLength (L-m) ell) (WindowPrefixProgram.length (L-m) ell)
    (WindowPrefixProgram.cap (L-m) ell (m/2) (RetainedRootWindows.weights root.channel).value.1
      (RetainedRootWindows.weights root.channel).value.2) ((m+1)*C) A W (by nlinarith) hA
  have hs := Nat.mul_le_mul_left (RetainedRootWindows.slots (L-m)) hh
  simpa only [GraphPrefixProgram.entryBitBudget,WindowPrefixProgram.bitBudget,RetainedRootWindows.execute,
    entryGroups,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs

theorem entry_prefix_control (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) (hC : 1 ≤ C) :
    GraphPrefixProgram.entryControlBudget ell (RetainedRootWindows.execute ell root).value ≤
      RetainedRootWindows.slots (L-m)*((m+1)*C*entryGroups ell root*
        controlUnit (WindowPrefixProgram.prefixLength (L-m) ell) (WindowPrefixProgram.length (L-m) ell)+64)+8 := by
  have hh := prefix_control (WindowPrefixProgram.prefixLength (L-m) ell) (WindowPrefixProgram.length (L-m) ell)
    (WindowPrefixProgram.cap (L-m) ell (m/2) (RetainedRootWindows.weights root.channel).value.1
      (RetainedRootWindows.weights root.channel).value.2) ((m+1)*C) (by nlinarith)
  have hs := Nat.add_le_add_right (Nat.mul_le_mul_left (RetainedRootWindows.slots (L-m))
    (Nat.add_le_add_right hh 64)) 8
  simpa only [GraphPrefixProgram.entryControlBudget,WindowPrefixProgram.controlBudget,RetainedRootWindows.execute,
    entryGroups,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc] using hs

theorem shifted_size (k A : ℕ) : (2^k*A).size ≤ k+A.size+1 := by
  have hh := ParameterExecution.size_mul (2^k) A
  rw [Nat.size_pow] at hh
  omega

theorem entry_bits (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C)
    (A W : ℕ) (hC : 1 ≤ C) (hW : L-m+A.size+1 ≤ W) :
    GraphAdaptivePrefixCosts.entryBitBudget hm cap root A ≤
      C*(3^(2*(L-m))*denseBitUnit (L-m) m cap W+
        RetainedRootWindows.slots (L-m)*(m+1)*entryGroups (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value) root*
          bitUnit (WindowPrefixProgram.prefixLength (L-m) (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value))
            (WindowPrefixProgram.length (L-m) (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value)) W) := by
  let k := L-m
  let ell := GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value
  have hA : A.size ≤ W := by omega
  have hshift : (2^k*A).size ≤ W := (shifted_size k A).trans hW
  have hs := slots_le k
  have hpow : 1 ≤ 3^(2*k) := Nat.one_le_pow _ _ (by omega)
  have hpre := entry_prefix_bits ell root (2^k*A) W hC hshift
  have ha := scalar_mono hA
  have ht := scalar_mono hshift
  have hsetup := Nat.mul_le_mul (Nat.mul_le_mul hC hpow) (le_refl (4*RetainedRootWindows.countBudget m+HalfSourceSuffixProgram.bitBudget k cap.size))
  have hsrc := Nat.mul_le_mul_left (3^(2*k)*(m+1)*C) ha
  have hpar := Nat.mul_le_mul (Nat.mul_le_mul_right (3^(2*k)) hs) (Nat.mul_le_mul_left ((m+1)*C) ha)
  have hscalar := Nat.mul_le_mul_left ((m+1)*C) ht
  have haddr := Nat.mul_le_mul_right (BinaryGroupedCoordinates.addressBudget (2*k)) hC
  have htrans := Nat.mul_le_mul hs (Nat.mul_le_mul_left (k*3^(2*k))
    (show 3*BinaryGroupedCoordinates.addressBudget (2*k)+(m+1)*C*(5*BackendScalarBits.backendScalarUnit (2^k*A).size) ≤
      C*(3*BinaryGroupedCoordinates.addressBudget (2*k)+(m+1)*(5*BackendScalarBits.backendScalarUnit W)) by nlinarith))
  have hperm := Nat.mul_le_mul hs (Nat.mul_le_mul_left (3^(2*k))
    (show BinaryGroupedCoordinates.addressBudget (2*k)+(m+1)*C*BackendScalarBits.backendScalarUnit (2^k*A).size ≤
      C*(BinaryGroupedCoordinates.addressBudget (2*k)+(m+1)*BackendScalarBits.backendScalarUnit W) by nlinarith))
  unfold GraphAdaptivePrefixCosts.entryBitBudget GraphAdaptivePrefixCosts.fixedBitBudget
    RetainedRootWindows.bitBudget ResidualWindowSource.bitBudget RetainedRootWindows.partitionBitBudget
    GraphWindowTransforms.entryBitBudget RetainedOppositeTransform.bitBudget RetainedOppositeTransform.layerPrice
    GraphWindowPermutations.entryBitBudget RetainedWindowPermutation.bitBudget RetainedWindowPermutation.rowBitBudget
  change _ ≤ _
  dsimp only [k,ell] at *
  unfold denseBitUnit
  nlinarith

#print axioms slots_le
#print axioms entry_prefix_bits
#print axioms entry_prefix_control
#print axioms shifted_size
#print axioms entry_bits
end ThinMatrix.HalfSourceAdaptiveVolume
