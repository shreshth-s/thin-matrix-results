import ResidualPolynomialDegree

set_option autoImplicit false

/-! The degree-space choice is performed on the original retained mask using
binary counting, addition and decoding. No input premise supplies a sufficient
F, and the construction is charged before the complete residual array. -/
namespace ThinMatrix.BinaryResidualDegreeSpace
open BinaryCell BinaryGroupedCoordinates BinaryCroppedHighInput

theorem toList_get {A : Type} {L : ℕ} (v : Vector A L) : v.toList=List.ofFn v.get := by
  have h : Vector.ofFn v.get=v := by ext i; simp [Vector.get]
  exact (congrArg Vector.toList h).symm.trans Vector.toList_ofFn

theorem selected_ones {L : ℕ} (mask : Vector Bool L) :
    (ResidualLayout.selected mask).length=WalshEmbedding.ones mask.get := by
  rw [← List.toFinset_card_of_nodup (ResidualLayout.selected_nodup mask)]
  simp [ResidualLayout.selected,WalshEmbedding.ones,List.toFinset_filter]

def execute {L : ℕ} (mask : Vector Bool L) : Run ℕ :=
  let count := countBits mask.toList
  let next := add count.value BinaryModularCell.one
  let decoded := BinaryModularCell.decodeUnsigned next.value
  ⟨decoded.value,count.bitSteps+next.bitSteps+decoded.bitSteps,8*mask.toArray.size+12⟩

theorem execute_value {L : ℕ} (mask : Vector Bool L) :
    (execute mask).value=(ResidualLayout.selected mask).length+1 := by
  simp [execute,BinaryModularCell.decodeUnsigned_value,countBits_view,toList_get,
    bitCount_ofFn,selected_ones]
  omega

def bitBudget (L : ℕ) : ℕ :=
  L*(BackendScalarBits.backendScalarUnit (L.size+1)+4)+1+
    BackendScalarBits.backendScalarUnit ((L+1).size+1)+8*((L+1).size+1)^2

theorem execute_bits {L : ℕ} (mask : Vector Bool L) :
    (execute mask).bitSteps ≤ bitBudget L := by
  have hc := countBits_price mask.toList L (by simp)
  have hb : bitCount mask.toList ≤ L := by simpa using bitCount_le mask.toList
  have ha := add_price ((L+1).size+1) (countBits mask.toList).value BinaryModularCell.one
    (by rw [countBits_view,Int.natAbs_natCast]; exact (Nat.size_le_size (hb.trans (by omega : L≤L+1))).trans (by omega))
    (by simp)
  have hd := BinaryModularCell.decodeUnsigned_price (L+1).size
    (add (countBits mask.toList).value BinaryModularCell.one).value (by
      simp only [add_view,countBits_view,BinaryModularCell.one_view]
      rw [show (↑(bitCount mask.toList):ℤ)+1=((bitCount mask.toList+1:ℕ):ℤ) by omega,Int.natAbs_natCast]
      exact Nat.size_le_size (by omega))
  simp only [Vector.length_toList] at hc
  simp only [execute,bitBudget]
  omega

theorem execute_control {L : ℕ} (mask : Vector Bool L) :
    (execute mask).control=8*L+12 := by simp [execute]

#print axioms toList_get
#print axioms selected_ones
#print axioms execute_value
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.BinaryResidualDegreeSpace
