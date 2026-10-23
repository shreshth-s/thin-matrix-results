import StoredRootPolynomial
import ShiftedLowChannelFormula

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

/-! Actual retained root arrays are the shifted cache factors of their raw
physical input. The only reindexing is erased dimension transport; every
normal/opposite distinguished word and remaining ternary word is accounted for. -/
namespace ThinMatrix.RetainedShiftedFactor
open WalshEmbedding ResidualFamilyKeys DistinguishedResidualRoot DistinguishedResidualSupport
open CroppedGroupedSuffix
open scoped BigOperators

abbrev Data (m k : ℕ) := Word (2*k) × (Fin m → NormalLetter) × (Fin m → OppositeLetter)

def normalInput {L m : ℕ} (a b : Mask L m) (w : Word (2*(L-m))) (n : Fin m → NormalLetter) : Fin L → NormalLetter :=
  assemble (ResidualLayout.equivalence a.bits) (fun i => n (Fin.cast (selected_size a) i))
    (fun i => normalRemaining (w (Fin.cast (by rw [remaining_size,remaining_size,two_mul])
      (Fin.castAdd (ResidualLayout.remaining b.bits).length i))))

def oppositeInput {L m : ℕ} (a b : Mask L m) (w : Word (2*(L-m))) (o : Fin m → OppositeLetter) : Fin L → OppositeLetter :=
  assemble (ResidualLayout.equivalence b.bits) (fun i => o (Fin.cast (selected_size b) i))
    (fun i => SourceCoordinates.oppositeEquiv (w (Fin.cast (by rw [remaining_size,remaining_size,two_mul])
      (Fin.natAdd (ResidualLayout.remaining a.bits).length i))))

noncomputable def rawValue {L m q : ℕ} [NeZero q] (raw : BinarySourceFormation.RawStore L q)
    (a b : Mask L m) (w : Word (2*(L-m))) (n : Fin m → NormalLetter) (o : Fin m → OppositeLetter) :
    Polynomial (CyclicRing.Cyclic q) :=
  BinaryResidualRootProgram.sourcePolynomial (m/2) raw (normalInput a b w n) (oppositeInput a b w o)

noncomputable def source {L m q : ℕ} [NeZero q] (raw : BinarySourceFormation.RawStore L q)
    (a b : Mask L m) (forms : Fin (2*(L-m)) → Fin 3 → ℤ) (x : Data m (L-m)) : Polynomial (CyclicRing.Cyclic q) :=
  ((∏ i, forms i (x.1 i) : ℤ) : Polynomial (CyclicRing.Cyclic q))*rawValue raw a b x.1 x.2.1 x.2.2

theorem contract_cast {R : Type*} [CommRing R] {n m : ℕ} (h : n=m) (c : Vector Bool m) (z : R)
    (read : (Fin n → NormalLetter) → R) :
    contract (c.cast h.symm).get z read=∑ w : Fin m → NormalLetter, kernel c.get z w*read (fun i => w (Fin.cast h i)) := by
  cases h
  rfl

theorem integerScale_cast {n m : ℕ} (h : n=m) (c : Vector Bool m) :
    ResidualPolynomialDegree.integerScale (c.cast h.symm)=ResidualPolynomialDegree.integerScale c := by
  cases h; rfl

theorem row_dense {L m q : ℕ} [NeZero q] (raw : BinarySourceFormation.RawStore L q)
    (a b : Mask L m) (c : Channel m) (w : Word (2*(L-m))) :
    ResidualPolynomialDegree.decode ((ResidualWindowSource.rows (RetainedResidualFamily.produce raw a b c).value).get
      (StoredGroupedCompletion.rawIndex _ w))=
      ∑ n : Fin m → NormalLetter, ∑ o : Fin m → OppositeLetter,
        kernel (normal c).get Polynomial.X n*(∏ i, oppositeFactor ((opposite c).get i) (o i))*rawValue raw a b w n o := by
  rw [StoredRootPolynomial.produced_row]
  unfold ResidualPolynomialDegree.polynomial
  simp only [RetainedResidualFamily.normalKey,RetainedResidualFamily.oppositeKey]
  rw [integerScale_cast (selected_size b),contract_cast (selected_size a)]
  simp only [Vector.get_cast,Vector.get_ofFn]
  change ((ResidualPolynomialDegree.integerScale (opposite c) : ℤ) : Polynomial (CyclicRing.Cyclic q))*
    (∑ n : Fin m → NormalLetter, kernel (normal c).get Polynomial.X n*
      rawValue raw a b w n (fun i => oppositeLetter ((opposite c).get i)))=_
  rw [ResidualRootBridge.integerScale_cast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have ho := opposite_contract (R:=Polynomial (CyclicRing.Cyclic q)) (opposite c).get (fun o => rawValue raw a b w n o)
  calc
    _ = kernel (normal c).get Polynomial.X n*((∏ i, oppositeScale ((opposite c).get i))*
      rawValue raw a b w n (fun i => oppositeLetter ((opposite c).get i))) := by ring
    _ = kernel (normal c).get Polynomial.X n*(∑ o, (∏ i, oppositeFactor ((opposite c).get i) (o i))*rawValue raw a b w n o) := by rw [ho]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro o _; ring

theorem query_factor {L m q : ℕ} [NeZero q] (raw : BinarySourceFormation.RawStore L q)
    (a b : Mask L m) (c : Channel m) (forms : Fin (2*(L-m)) → Fin 3 → ℤ) :
    StoredRootPolynomial.query (ResidualWindowSource.rows (RetainedResidualFamily.produce raw a b c).value) forms=
      ShiftedLowChannelFormula.leftFactor c (source raw a b forms) (fun x => x.2.1) (fun x => x.2.2) := by
  unfold StoredRootPolynomial.query ShiftedLowChannelFormula.leftFactor
  simp only [row_dense,Fintype.sum_prod_type,source]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w _
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro o _
  ring

/-- The retained lookup is exactly the physically cropped raw polynomial. -/
theorem rawValue_cropped {L m q : ℕ} [NeZero q] (raw : BinarySourceFormation.RawStore L q)
    (a b : Mask L m) (w : Word (2*(L-m))) (n : Fin m → NormalLetter) (o : Fin m → OppositeLetter) :
    rawValue raw a b w n o=cropBoth (m/2) (ResidualRootBridge.rawPolynomial raw) (normalInput a b w n) (oppositeInput a b w o) :=
  ResidualRootBridge.sourcePolynomial_eq _ _ _ _

#print axioms contract_cast
#print axioms integerScale_cast
#print axioms row_dense
#print axioms query_factor
#print axioms rawValue_cropped
end ThinMatrix.RetainedShiftedFactor
