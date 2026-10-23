import ResidualRootBridge

set_option autoImplicit false

/-! Residual arrays with internally constructed sufficient degree space.
Binary mask counting selects F=mN+1; the stored rows represent complete
polynomials and refine the pre-existing physical-root specification. This
closes a representation boundary, not root-family or APSP cost integration. -/
namespace ThinMatrix.CompleteResidualArray
open WalshEmbedding BinaryGroupedCoordinates BinaryResidualPolynomial
open ResidualPolynomialDegree
open scoped BigOperators

abbrev Rows {L : ℕ} (maskN maskO : Vector Bool L) (C : ℕ) :=
  Vector (Block ((ResidualLayout.selected maskN).length+1) C)
    (3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length))

def execute {L C : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) : Run (Rows maskN maskO C) :=
  let space := BinaryResidualDegreeSpace.execute maskN
  let out := BinaryResidualArray.execute space.value cap raw maskN maskO cn co
  ⟨cast (congrArg (fun F => Vector (Block F C)
    (3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)))
      (BinaryResidualDegreeSpace.execute_value maskN)) out.value,
    space.bitSteps+out.bitSteps,space.control+out.control+4⟩

private theorem cast_apply {α : ℕ → Type} (f : (n : ℕ) → α n) {a b : ℕ} (h : a=b) :
    cast (congrArg α h) (f a)=f b := by
  cases h
  rfl

theorem execute_value {L C : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) :
    (execute cap raw maskN maskO cn co).value=
      (BinaryResidualArray.execute ((ResidualLayout.selected maskN).length+1) cap raw maskN maskO cn co).value := by
  exact cast_apply (fun F => (BinaryResidualArray.execute F cap raw maskN maskO cn co).value)
    (BinaryResidualDegreeSpace.execute_value maskN)

def bitBudget (L mN mO kN kO C cap A : ℕ) : ℕ :=
  BinaryResidualDegreeSpace.bitBudget L+BinaryResidualArray.bitBudget L mN mO kN kO C (mN+1) cap A

def controlBudget (L mN mO kN kO C : ℕ) : ℕ :=
  8*L+16+BinaryResidualArray.controlBudget L mN mO kN kO C (mN+1)

theorem execute_bits {L C : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    (execute cap raw maskN maskO cn co).bitSteps ≤
      bitBudget L (ResidualLayout.selected maskN).length (ResidualLayout.selected maskO).length
        (ResidualLayout.remaining maskN).length (ResidualLayout.remaining maskO).length C cap A := by
  have hs := BinaryResidualDegreeSpace.execute_bits maskN
  have ho := BinaryResidualArray.execute_bits (F:=(ResidualLayout.selected maskN).length+1) cap raw maskN maskO cn co A ha
  have he := congrArg (fun F => (BinaryResidualArray.execute F cap raw maskN maskO cn co).bitSteps)
    (BinaryResidualDegreeSpace.execute_value maskN)
  simp only [execute,bitBudget]
  omega

theorem execute_control {L C : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) :
    (execute cap raw maskN maskO cn co).control ≤
      controlBudget L (ResidualLayout.selected maskN).length (ResidualLayout.selected maskO).length
        (ResidualLayout.remaining maskN).length (ResidualLayout.remaining maskO).length C := by
  have hs := BinaryResidualDegreeSpace.execute_control maskN
  have ho := BinaryResidualArray.execute_control (F:=(ResidualLayout.selected maskN).length+1) cap raw maskN maskO cn co
  have he := congrArg (fun F => (BinaryResidualArray.execute F cap raw maskN maskO cn co).control)
    (BinaryResidualDegreeSpace.execute_value maskN)
  simp only [execute,controlBudget]
  omega

theorem execute_polynomial {L C : ℕ} [NeZero C] (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (w : CroppedGroupedSuffix.Word ((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)) :
    decode ((execute cap raw maskN maskO cn co).value.get (StoredGroupedCompletion.rawIndex _ w)) =
      polynomial cap raw maskN maskO cn co (Vector.ofFn (fun i => w (Fin.castAdd _ i)))
        (Vector.ofFn (fun i => w (Fin.natAdd _ i))) := by
  rw [execute_value,BinaryResidualArray.execute_get]
  exact row_complete cap raw maskN maskO cn co _ _ (by omega)

/-- The completed binary output is exactly the pre-existing distinguished
root on physical coordinates, including the full polynomial and cyclic ring. -/
theorem execute_root {L C : ℕ} [NeZero C] (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (he : (ResidualLayout.selected maskO).length=(ResidualLayout.selected maskN).length)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (w : CroppedGroupedSuffix.Word ((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)) :
    decode ((execute cap raw maskN maskO cn co).value.get (StoredGroupedCompletion.rawIndex _ w)) =
      DistinguishedResidualSupport.root (ResidualLayout.equivalence maskN)
        (ResidualRootBridge.transport (ResidualLayout.equivalence maskO) he (ResidualRootBridge.remaining_eq maskN maskO he))
        cn.get (fun i => co.get ((finCongr he).symm i)) Polynomial.X cap (ResidualRootBridge.rawPolynomial raw)
        (fun i => w (Fin.castAdd _ i))
        (fun i => w (Fin.natAdd _ ((finCongr (ResidualRootBridge.remaining_eq maskN maskO he)).symm i))) := by
  rw [execute_polynomial,ResidualRootBridge.polynomial_eq_root cap raw maskN maskO he]
  congr 1 <;> funext i <;> simp

/-- The existing rare-support theorem now applies to the actual complete
binary output. No support premise is supplied by the caller. -/
theorem execute_support {L C : ℕ} [NeZero C] (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (he : (ResidualLayout.selected maskO).length=(ResidualLayout.selected maskN).length)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (w : CroppedGroupedSuffix.Word ((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length))
    (h : decode ((execute cap raw maskN maskO cn co).value.get (StoredGroupedCompletion.rawIndex _ w))≠0) :
    ones cn.get+DistinguishedResidualSupport.rareCount (fun i => w (Fin.castAdd _ i)) ≤ cap ∧
      ones co.get+DistinguishedResidualSupport.rareCount (fun i => w (Fin.natAdd _ i)) ≤ cap := by
  rw [execute_root cap raw maskN maskO he] at h
  have hs := DistinguishedResidualSupport.remaining_caps _ _ _ _ _ _ _ _ _ h
  rw [ResidualRootBridge.ones_transport,ResidualRootBridge.rare_transport
    (ResidualRootBridge.remaining_eq maskN maskO he) (fun i => w (Fin.natAdd _ i))] at hs
  exact hs

theorem execute_width {L C : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A)
    (i : Fin (3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)))
    (d : Fin ((ResidualLayout.selected maskN).length+1)) (r : Fin C) :
    (cellView ((execute cap raw maskN maskO cn co).value.get i) d r).natAbs.size ≤
      (ResidualLayout.selected maskO).length+2*(ResidualLayout.selected maskN).length+A.size := by
  rw [execute_value]
  exact BinaryResidualArray.execute_width cap raw maskN maskO cn co A ha i d r

theorem coefficient_cells {L C : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) :
    (((execute cap raw maskN maskO cn co).value.toList.map
      (fun block => (block.toList.map (fun row => row.toArray.size)).sum)).sum) =
      3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)*
        ((ResidualLayout.selected maskN).length+1)*C := by
  rw [execute_value]
  exact BinaryResidualArray.coefficient_cells cap raw maskN maskO cn co

#print axioms cast_apply
#print axioms execute_value
#print axioms execute_bits
#print axioms execute_control
#print axioms execute_polynomial
#print axioms execute_root
#print axioms execute_support
#print axioms execute_width
#print axioms coefficient_cells
end ThinMatrix.CompleteResidualArray
