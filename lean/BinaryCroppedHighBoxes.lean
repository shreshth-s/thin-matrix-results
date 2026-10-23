import BinaryCroppedHighEncoder

set_option autoImplicit false

/-! Actual cropped HIGH path: two shifted shared encoders, a binary-derived
magnitude parameter, full cyclic base products, then the retained five-child
box recurrence. Inputs are original binary raw-source arrays. All preparation
premises of the generic HIGH table interface are discharged here. -/
namespace ThinMatrix.BinaryCroppedHighBoxes
open BinaryCell BinaryHighExecution BinaryCroppedHighEncoder
open scoped BigOperators

def magnitude (L A : ℕ) : ℕ := 8^(2*L)*A+1

theorem magnitude_pos (L A : ℕ) : 1 ≤ magnitude L A := by unfold magnitude; omega

def setup (L A : ℕ) : Result ℕ :=
  let encoded := BinaryMultiplierAdapter.encodeInteger (A : ℤ)
  let scaled := BinarySourceCells.shiftPower (6*L) encoded.value
  let padded := add scaled.value BinaryModularCell.one
  let decoded := BinaryModularCell.decodeUnsigned padded.value
  ⟨decoded.value,encoded.bitSteps+scaled.bitSteps+padded.bitSteps+decoded.bitSteps+6*L+32⟩

theorem setup_value (L A : ℕ) : (setup L A).value = magnitude L A := by
  change (BinaryModularCell.decodeUnsigned (add
    (BinarySourceCells.shiftPower (6*L) (BinaryMultiplierAdapter.encodeInteger (A : ℤ)).value).value
    BinaryModularCell.one).value).value = _
  rw [BinaryModularCell.decodeUnsigned_value,add_view,BinaryModularCell.one_view]
  change ((BinarySourceCells.shiftPower (6*L) (BinaryMultiplierAdapter.encodeInteger (A : ℤ)).value).value.view+1).natAbs = _
  rw [BinarySourceCells.shiftPower_view]
  change ((2 : ℤ)^(6*L)*(BinaryMultiplierAdapter.encodeInteger (A : ℤ)).value.view+1).natAbs = _
  rw [BinaryMultiplierAdapter.encodeInteger_view]
  have hp : (2 : ℤ)^(6*L) = ((8^(2*L) : ℕ) : ℤ) := by
    push_cast
    rw [show 6*L=3*(2*L) by omega,pow_mul]
    norm_num
  rw [hp,←Nat.cast_mul]
  change ((8^(2*L)*A+1 : ℕ) : ℤ).natAbs = magnitude L A
  rw [Int.natAbs_natCast]
  rfl

def setupWidth (L A : ℕ) : ℕ := A.log2+6*L+2

def setupBudget (L A : ℕ) : ℕ :=
  10*(A.size+1)^2+6*L*(200*(setupWidth L A)^2)+BackendScalarBits.backendScalarUnit (setupWidth L A)+
    8*(setupWidth L A+1)^2+6*L+32

theorem setup_price (L A : ℕ) : (setup L A).bitSteps ≤ setupBudget L A := by
  let encoded := BinaryMultiplierAdapter.encodeInteger (A : ℤ)
  let scaled := BinarySourceCells.shiftPower (6*L) encoded.value
  have he := BinaryMultiplierAdapter.encodeInteger_cost (A : ℤ)
  simp only [Int.natAbs_natCast] at he
  change encoded.bitSteps ≤ 10*(A.size+1)^2 at he
  have ha : |encoded.value.view| ≤ (A : ℤ) := by
    rw [BinaryMultiplierAdapter.encodeInteger_view,abs_of_nonneg (Int.natCast_nonneg A)]
  have hs := BinarySourceCells.shiftPower_bitSteps A (6*L) (6*L) encoded.value ha (le_refl _)
  have hw : (view scaled.value).natAbs.size ≤ setupWidth L A := by
    have h := BinarySourceCells.shiftPower_width A (6*L) (6*L) encoded.value ha (le_refl _)
    rw [scaled.value.canonical] at h
    change (view scaled.value).natAbs.size ≤ A.log2+6*L+1 at h
    unfold setupWidth
    omega
  have hp := add_price (setupWidth L A) scaled.value BinaryModularCell.one hw (by simp [setupWidth])
  have hscale : (view scaled.value).natAbs.size ≤ A.log2+6*L+1 := by
    have h := BinarySourceCells.shiftPower_width A (6*L) (6*L) encoded.value ha (le_refl _)
    rw [scaled.value.canonical] at h
    exact h
  have hadd := BinaryModularCell.add_size scaled.value BinaryModularCell.one
  have hout : (view (add scaled.value BinaryModularCell.one).value).natAbs.size ≤ setupWidth L A := by
    simp only [BinaryModularCell.one_view] at hadd
    change (view (add scaled.value BinaryModularCell.one).value).natAbs.size ≤ A.log2+6*L+2
    norm_num only [Int.natAbs_one, Nat.size_one] at hadd
    omega
  have hd := BinaryModularCell.decodeUnsigned_price (setupWidth L A) (add scaled.value BinaryModularCell.one).value hout
  change encoded.bitSteps+scaled.bitSteps+(add scaled.value BinaryModularCell.one).bitSteps+
    (BinaryModularCell.decodeUnsigned (add scaled.value BinaryModularCell.one).value).bitSteps+6*L+32 ≤ _
  change scaled.bitSteps ≤ 6*L*(200*(setupWidth L A)^2) at hs
  unfold setupBudget
  omega

structure Execution (L q : ℕ) where
  left : StoredEncoding q (2*L)
  right : StoredEncoding q (2*L)
  boxes : BinaryHighTable.Table q
  work : ℕ

def execute (L m t q cap A : ℕ) (X Y : BinarySourceFormation.RawStore L q) : Execution L q :=
  let size := setup L A
  let left := BinaryCroppedHighEncoder.execute L m t q cap true X
  let right := BinaryCroppedHighEncoder.execute L m t q cap false Y
  let out := BinaryHighTable.prepare (L:=L) (m:=m) (t:=t) size.value left.table right.table
  ⟨left,right,out.value,size.bitSteps+left.bitSteps+right.bitSteps+out.work+8⟩

theorem read_bound {L m t q : ℕ} (cap A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A) (w : HighBoxDP.BaseStates L m t) :
    BinaryHighTable.VectorBound (magnitude L A)
      (BinaryHighTable.readBase (BinaryCroppedHighEncoder.execute L m t q cap b raw).table w).1 := by
  intro j
  exact (readBase_bound cap A b raw hA w j).trans (by unfold magnitude; omega)

theorem execute_correct {L m t q : ℕ} [NeZero q] (cap A : ℕ)
    (X Y : BinarySourceFormation.RawStore L q) (hX : RawBound X A) (hY : RawBound Y A)
    (w : HighBoxDP.States L m t) (r : Fin q) :
    ((BinaryHighTable.lookup (execute L m t q cap A X Y).boxes (ArrayKeys.materialize w.val)).get r).view =
      HighBoxDP.boxValue w.val (fun v => CyclicRing.convolution
        (leafValues true cap X v).get (leafValues false cap Y v).get r) := by
  simp only [execute,setup_value]
  exact BinaryHighTable.prepare_source_complete (magnitude L A) (magnitude_pos L A) _ _ _ _
    (read_bound cap A true X hX) (read_bound cap A false Y hY)
    (readBase_values cap true X) (readBase_values cap false Y) w r

noncomputable def totalBudget (L m t q cap A : ℕ) : ℕ :=
  setupBudget L A+2*BinaryCroppedHighEncoder.totalBudget L m t q cap A+
    BinaryHighTable.preparationBudget L m t q (magnitude L A)+8

theorem execute_price {L m t q : ℕ} [NeZero q] (cap A : ℕ)
    (X Y : BinarySourceFormation.RawStore L q) (hX : RawBound X A) (hY : RawBound Y A) :
    (execute L m t q cap A X Y).work ≤ totalBudget L m t q cap A := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hs := setup_price L A
  have hl := BinaryCroppedHighEncoder.execute_price (m:=m) (t:=t) cap A true X hX hq
  have hr := BinaryCroppedHighEncoder.execute_price (m:=m) (t:=t) cap A false Y hY hq
  have hb := BinaryHighTable.prepare_work (L:=L) (m:=m) (t:=t) (magnitude L A) (magnitude_pos L A)
    (BinaryCroppedHighEncoder.execute L m t q cap true X).table
    (BinaryCroppedHighEncoder.execute L m t q cap false Y).table
    (read_bound cap A true X hX) (read_bound cap A false Y hY)
  simp only [execute,setup_value,totalBudget]
  omega

theorem correctness_and_work {L m t q : ℕ} [NeZero q] (cap A : ℕ)
    (X Y : BinarySourceFormation.RawStore L q) (hX : RawBound X A) (hY : RawBound Y A) :
    (∀ w : HighBoxDP.States L m t, ∀ r : Fin q,
      ((BinaryHighTable.lookup (execute L m t q cap A X Y).boxes (ArrayKeys.materialize w.val)).get r).view =
        HighBoxDP.boxValue w.val (fun v => CyclicRing.convolution
          (leafValues true cap X v).get (leafValues false cap Y v).get r)) ∧
      (execute L m t q cap A X Y).work ≤ totalBudget L m t q cap A :=
  ⟨fun w r => execute_correct cap A X Y hX hY w r,execute_price cap A X Y hX hY⟩

#print axioms magnitude_pos
#print axioms setup_value
#print axioms setup_price
#print axioms read_bound
#print axioms execute_correct
#print axioms execute_price
#print axioms correctness_and_work
end ThinMatrix.BinaryCroppedHighBoxes
