import BinaryFoldedFormation
import FoldedFormationArithmetic
import BinaryModularCell

/-! Semantic refinement of the binary folded source producer. Native
integer arithmetic occurs only in the proof-side reference formulas. -/

namespace ThinMatrix.BinaryFoldedFormationCorrect

open BinaryCell BinaryFoldedFormation StoredMinPlusAPSP
open FoldedBackendExecution FoldedFormationArithmetic

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem nativeRead_eq_tableRead {n : ℕ} (A : IntTable n) (i j : ℕ) :
    nativeRead A i j = tableRead A i j := by
  by_cases hi : i < n <;> by_cases hj : j < n <;>
    simp [nativeRead, tableRead, Array.getD, Vector.size_toArray, hi, hj, decode, Vector.get]

theorem scaledRead_left {n : ℕ} (A : IntTable n) (i g : ℕ) :
    3*nativeRead A i g = if g < n then 3*tableRead A i g else 0 := by
  by_cases hg : g < n
  · simp only [hg, if_true, nativeRead_eq_tableRead]
  · simp [nativeRead, hg]

theorem scaledRead_right {n : ℕ} (A : IntTable n) (g j : ℕ) :
    3*nativeRead A g j = if g < n then 3*tableRead A g j else 0 := by
  by_cases hg : g < n
  · simp only [hg, if_true, nativeRead_eq_tableRead]
  · simp [nativeRead, hg]

theorem split_nat_views (divisor input : Cell) (d x : ℕ) (hd : 0 < d)
    (hdivisor : view divisor = (d : ℤ)) (hinput : view input = (x : ℤ)) :
    view (BinaryModularCell.split divisor input).value.1 = ((x/d : ℕ) : ℤ) ∧
      view (BinaryModularCell.split divisor input).value.2 = ((x%d : ℕ) : ℤ) := by
  have hpos : 0 < view divisor := by rw [hdivisor]; exact_mod_cast hd
  constructor
  · rw [BinaryModularCell.split_quotient_view divisor input hpos.le, hdivisor, hinput]
    exact (Int.natCast_ediv x d).symm
  · rw [BinaryModularCell.split_remainder_view divisor input hpos, hdivisor, hinput]
    exact (Int.natCast_emod x d).symm

theorem coordinates_value {n h d q block : ℕ} (right : Bool) (g : Geometry n h d q block)
    (hn : 0<n) (hd : 0<d) (address : ℕ) :
    let middle:=middleAddress right n h d address
    let outer:=outerAddress right n h d address
    (coordinates right g address).value.original=outer/FoldedCounts.foldWidth d ∧
    (coordinates right g address).value.label=block*h+middle/d ∧
    view (coordinates right g address).value.sigma=((middle%d:ℕ):ℤ) ∧
    view (coordinates right g address).value.residue=((outer%FoldedCounts.foldWidth d:ℕ):ℤ) ∧
    (coordinates right g address).value.padded=decide (middle<rawMiddle h d) ∧
    (coordinates right g address).value.active=decide (block*h+middle/d<n) := by
  let M := middleAddress right n h d address
  let O := outerAddress right n h d address
  let flat := BinaryModularCell.split (if right then g.outerCell else g.middleCell)
    (publicNat address).value
  let middle := if right then flat.value.1 else flat.value.2
  let outer := if right then flat.value.2 else flat.value.1
  let mid := BinaryModularCell.split g.dCell middle
  let out := BinaryModularCell.split g.widthCell outer
  let originalLabel := BinaryCell.add g.offsetCell mid.value.1
  have hw : 0 < FoldedCounts.foldWidth d := FoldedCounts.foldWidth_pos d
  have hN : 0 < outerSize n d := Nat.mul_pos hn hw
  have hD : 0 < middleSize h d := by
    unfold middleSize PhaseGeometry.pad4
    positivity
  have hflat := split_nat_views (if right then g.outerCell else g.middleCell)
    (publicNat address).value (if right then outerSize n d else middleSize h d) address
    (by cases right <;> assumption)
    (by cases right <;> simp only [Bool.false_eq_true, if_false, if_true,
      Geometry.outer_view, Geometry.middle_view]) (publicNat_view address)
  have hm : view middle = (M : ℤ) := by
    cases right
    · simpa only [middle, flat, M, middleAddress, Bool.false_eq_true, if_false] using hflat.2
    · simpa only [middle, flat, M, middleAddress, if_true] using hflat.1
  have ho : view outer = (O : ℤ) := by
    cases right
    · simpa only [outer, flat, O, outerAddress, Bool.false_eq_true, if_false] using hflat.1
    · simpa only [outer, flat, O, outerAddress, if_true] using hflat.2
  have hmid : view mid.value.1 = ((M/d : ℕ) : ℤ) ∧
      view mid.value.2 = ((M%d : ℕ) : ℤ) :=
    split_nat_views g.dCell middle d M hd g.d_view hm
  have hout : view out.value.1 = ((O/FoldedCounts.foldWidth d : ℕ) : ℤ) ∧
      view out.value.2 = ((O%FoldedCounts.foldWidth d : ℕ) : ℤ) :=
    split_nat_views g.widthCell outer (FoldedCounts.foldWidth d) O hw g.width_view ho
  have hlabel : view originalLabel.value = ((block*h+M/d : ℕ) : ℤ) := by
    simp only [originalLabel, BinaryCell.add_view, Geometry.offset_view, hmid.1, Nat.cast_add]
  change
    (BinaryModularCell.decodeUnsigned out.value.1).value=O/FoldedCounts.foldWidth d ∧
    (BinaryModularCell.decodeUnsigned originalLabel.value).value=block*h+M/d ∧
    view mid.value.2=((M%d:ℕ):ℤ) ∧
    view out.value.2=((O%FoldedCounts.foldWidth d:ℕ):ℤ) ∧
    (BinaryModularCell.lessUnsigned middle g.rawCell).value=decide (M<rawMiddle h d) ∧
    (BinaryModularCell.lessUnsigned originalLabel.value g.nCell).value=decide (block*h+M/d<n)
  refine ⟨?_, ?_, hmid.2, hout.2, ?_, ?_⟩
  · rw [BinaryModularCell.decodeUnsigned_value, hout.1, Int.natAbs_natCast]
  · rw [BinaryModularCell.decodeUnsigned_value, hlabel, Int.natAbs_natCast]
  · rw [BinaryModularCell.lessUnsigned_view middle g.rawCell
      (by rw [hm]; positivity) (by rw [g.raw_view]; positivity), hm, g.raw_view]
    simp only [Int.ofNat_lt]
  · rw [BinaryModularCell.lessUnsigned_view originalLabel.value g.nCell
      (by rw [hlabel]; positivity) (by rw [g.n_view]; positivity), hlabel, g.n_view]
    simp only [Int.ofNat_lt]

theorem coefficient_left_native {n h d q block : ℕ} (g : Geometry n h d q block)
    (a : BinaryTable n) (hn : 0<n) (hd : 0<d) (hq : 0<q) (address coeff : ℕ) :
    view (coefficient false g a address coeff).value =
      let middle := address % middleSize h d
      let outer := address / middleSize h d
      let label := block*h+middle/d
      let value := 3*nativeRead (viewTable a) (outer/FoldedCounts.foldWidth d) label
      if middle < rawMiddle h d ∧ label < n ∧
        ((middle%d : ℕ) : ℤ) = (value+((outer%FoldedCounts.foldWidth d : ℕ) : ℤ)) % (d : ℤ) ∧
        (coeff : ℤ) = value % (q : ℤ) then 1 else 0 := by
  obtain ⟨horiginal,hlabel,hsigma,hresidue,hpadded,hactive⟩ :=
    coordinates_value false g hn hd address
  simp only [middleAddress, outerAddress, Bool.false_eq_true, if_false] at horiginal hlabel hsigma hresidue hpadded hactive
  have hdc : 0 < view g.dCell := by rw [g.d_view]; exact_mod_cast hd
  have hqc : 0 < view g.qCell := by rw [g.q_view]; exact_mod_cast hq
  simp only [BinaryFoldedFormation.coefficient, Bool.false_eq_true, if_false, apply_ite,
    BinaryModularCell.one_view, BinaryCell.zero_view, BinaryModularCell.equal_view,
    BinaryModularCell.remainder_view g.dCell _ hdc,
    BinaryModularCell.remainder_view g.qCell _ hqc,
    BinaryCell.add_view, BinaryCell.mul_view, three_view, readTable_view, publicNat_view,
    Geometry.d_view, Geometry.q_view, horiginal, hlabel, hsigma, hresidue, hpadded, hactive,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  split_ifs <;> rfl

theorem coefficient_right_native {n h d q block : ℕ} (g : Geometry n h d q block)
    (a : BinaryTable n) (hn : 0<n) (hd : 0<d) (hq : 0<q) (address coeff : ℕ) :
    view (coefficient true g a address coeff).value =
      let middle := address / outerSize n d
      let outer := address % outerSize n d
      let label := block*h+middle/d
      let value := 3*nativeRead (viewTable a) label (outer/FoldedCounts.foldWidth d)
      if middle < rawMiddle h d ∧
        ((middle%d : ℕ) : ℤ) = (-value-(FoldedCounts.foldWidth d : ℤ)*
          ((outer%FoldedCounts.foldWidth d : ℕ) : ℤ)) % (d : ℤ) ∧
        (coeff : ℤ) = value % (q : ℤ) then 1 else 0 := by
  obtain ⟨horiginal,hlabel,hsigma,hresidue,hpadded,hactive⟩ :=
    coordinates_value true g hn hd address
  simp only [middleAddress, outerAddress, if_true] at horiginal hlabel hsigma hresidue hpadded hactive
  have hdc : 0 < view g.dCell := by rw [g.d_view]; exact_mod_cast hd
  have hqc : 0 < view g.qCell := by rw [g.q_view]; exact_mod_cast hq
  simp only [BinaryFoldedFormation.coefficient, if_true, apply_ite,
    BinaryModularCell.one_view, BinaryCell.zero_view, BinaryModularCell.equal_view,
    BinaryModularCell.remainder_view g.dCell _ hdc,
    BinaryModularCell.remainder_view g.qCell _ hqc,
    rightResidue_view, BinaryCell.mul_view, three_view, readTable_view, publicNat_view,
    Geometry.d_view, Geometry.q_view, horiginal, hlabel, hsigma, hresidue, hpadded,
    Bool.and_eq_true, decide_eq_true_eq, and_true, and_assoc]
  split_ifs <;> rfl

theorem coefficient_left_reference {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h))
    (g : Geometry n h (physicalFold f) f.cyclic b.val) (a : BinaryTable n)
    (address : Fin (outerSize n (physicalFold f)*middleSize h (physicalFold f)))
    (coeff : Fin f.cyclic) :
    view (BinaryFoldedFormation.coefficient false g a address.val coeff.val).value =
      leftReference f b (viewTable a) address coeff := by
  have hn : 0<n := Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right
    (lt_of_le_of_lt (Nat.zero_le address.val) address.isLt))
  rw [coefficient_left_native g a hn (Nat.mul_pos (by decide) f.folded_pos) f.cyclic_pos]
  simp only [leftReference, rawMiddle, scaledRead_left]

theorem coefficient_right_reference {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h))
    (g : Geometry n h (physicalFold f) f.cyclic b.val) (a : BinaryTable n)
    (address : Fin (middleSize h (physicalFold f)*outerSize n (physicalFold f)))
    (coeff : Fin f.cyclic) :
    view (BinaryFoldedFormation.coefficient true g a address.val coeff.val).value =
      rightReference f b (viewTable a) address coeff := by
  have hn : 0<n := Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_left
    (lt_of_le_of_lt (Nat.zero_le address.val) address.isLt))
  rw [coefficient_right_native g a hn (Nat.mul_pos (by decide) f.folded_pos) f.cyclic_pos]
  simp only [rightReference, rawMiddle, scaledRead_right]

theorem formLeft_view {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h))
    (g : Geometry n h (physicalFold f) f.cyclic b.val) (a : BinaryTable n) :
    viewLeft (BinaryFoldedFormation.formLeft g a).value =
      FoldedBackendExecution.formLeft f b (viewTable a) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hv : view (((BinaryFoldedFormation.formLeft g a).value.get ⟨i,hi⟩).get ⟨j,hj⟩) =
      ((FoldedBackendExecution.formLeft f b (viewTable a)).get ⟨i,hi⟩).get ⟨j,hj⟩ := by
    rw [BinaryFoldedFormation.formLeft_get, coefficient_left_reference,
      FoldedFormationArithmetic.formLeft_arithmetic]
  simpa only [viewLeft, Vector.getElem_map, Vector.get, Fin.val_cast,
    Vector.getElem_toArray] using hv

theorem formRight_view {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h))
    (g : Geometry n h (physicalFold f) f.cyclic b.val) (a : BinaryTable n) :
    viewRight (BinaryFoldedFormation.formRight g a).value =
      FoldedBackendExecution.formRight f b (viewTable a) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hv : view (((BinaryFoldedFormation.formRight g a).value.get ⟨i,hi⟩).get ⟨j,hj⟩) =
      ((FoldedBackendExecution.formRight f b (viewTable a)).get ⟨i,hi⟩).get ⟨j,hj⟩ := by
    rw [BinaryFoldedFormation.formRight_get, coefficient_right_reference,
      FoldedFormationArithmetic.formRight_arithmetic]
  simpa only [viewRight, Vector.getElem_map, Vector.get, Fin.val_cast,
    Vector.getElem_toArray] using hv

theorem formSources_left_view {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n) :
    viewLeft (formSources f b input).value.left =
      FoldedBackendExecution.formLeft f b (viewTable input.left) := by
  exact formLeft_view f b (makeGeometry n h (physicalFold f) f.cyclic b.val).value input.left

theorem formSources_right_view {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n) :
    viewRight (formSources f b input).value.right =
      FoldedBackendExecution.formRight f b (viewTable input.right) := by
  exact formRight_view f b (makeGeometry n h (physicalFold f) f.cyclic b.val).value input.right

theorem formSources_encoded_views {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A B T : IntTable n) :
    viewLeft (formSources f b (encodeInputs A B T).value).value.left =
        FoldedBackendExecution.formLeft f b A ∧
      viewRight (formSources f b (encodeInputs A B T).value).value.right =
        FoldedBackendExecution.formRight f b B := by
  constructor
  · simpa only [encodeInputs, encodeTable_view] using
      formSources_left_view f b (encodeInputs A B T).value
  · simpa only [encodeInputs, encodeTable_view] using
      formSources_right_view f b (encodeInputs A B T).value

end ThinMatrix.BinaryFoldedFormationCorrect

#print axioms ThinMatrix.BinaryFoldedFormationCorrect.coordinates_value
#print axioms ThinMatrix.BinaryFoldedFormationCorrect.coefficient_left_reference
#print axioms ThinMatrix.BinaryFoldedFormationCorrect.coefficient_right_reference
#print axioms ThinMatrix.BinaryFoldedFormationCorrect.formLeft_view
#print axioms ThinMatrix.BinaryFoldedFormationCorrect.formRight_view
#print axioms ThinMatrix.BinaryFoldedFormationCorrect.formSources_encoded_views
