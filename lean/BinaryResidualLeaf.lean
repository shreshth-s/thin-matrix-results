import ResidualLayout
import BinaryResidualPolynomial
import BinaryCroppedHighInput

set_option autoImplicit false

/-! Distinguished-root leaves read the actual binary Walsh-source trie once,
test both rare caps with stored binary cells, and write a full constant
polynomial block. Every retained degree and column is allocated, including
all zero cells. This is leaf formation, not the complete recursive root. -/
namespace ThinMatrix.BinaryResidualLeaf
open WalshEmbedding SourceFormation BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open BinaryResidualPolynomial DistinguishedResidualSupport
open scoped BigOperators

def readRow {L C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) : Run (Vector Cell C) :=
  let nk := n.map normalIndex
  let ok := o.map oppositeIndex
  let normal := tableReadProgram 4 L raw nk.get
  let opposite := tableReadProgram 3 L normal.value ok.get
  ⟨opposite.value,0,normal.operations+opposite.operations+16*(L+1)^2⟩

theorem readRow_get {L C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) (r : Fin C) :
    (readRow raw n o).value.get r=BinarySourceFormation.readRaw raw n.get o.get r := by
  simp only [readRow,tableReadProgram_value,BinarySourceFormation.readRaw]
  have hn : (n.map normalIndex).get=(fun i => normalIndex (n.get i)) := by funext i; simp
  have ho : (o.map oppositeIndex).get=(fun i => oppositeIndex (o.get i)) := by funext i; simp
  rw [hn,ho]

theorem readRow_control {L C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) :
    (readRow raw n o).control=4*L+2+16*(L+1)^2 := by
  simp only [readRow,tableReadProgram_cost]
  omega

def constant (F : ℕ) {C : ℕ} (accepted : Bool) (row : Vector Cell C) : Run (Block F C) :=
  let shape := Vector.replicate F row
  let out := mapBlock shape (fun d r =>
    if accepted && decide (d.val=0) then
      let copied := copy (row.get r)
      ⟨copied.value,copied.bitSteps,4⟩
    else ⟨zero,0,4⟩)
  ⟨out.value,out.bitSteps,out.control+F+2⟩

theorem constant_view {F C : ℕ} (accepted : Bool) (row : Vector Cell C) (d : Fin F) (r : Fin C) :
    cellView (constant F accepted row).value d r=if accepted && decide (d.val=0) then view (row.get r) else 0 := by
  simp only [constant]
  rw [mapBlock_get]
  split <;> simp_all

theorem constant_bound {F C : ℕ} (accepted : Bool) (row : Vector Cell C) (A : ℕ)
    (h : ∀ r, (view (row.get r)).natAbs≤A) : Bound A (constant F accepted row).value := by
  intro d r
  rw [constant_view]
  split
  · exact h r
  · simp

theorem constant_bits {F C : ℕ} (accepted : Bool) (row : Vector Cell C) (A : ℕ)
    (h : ∀ r, (view (row.get r)).natAbs≤A) :
    (constant F accepted row).bitSteps≤F*(C*BackendScalarBits.backendScalarUnit A.size) := by
  apply mapBlock_bits
  intro d r
  split
  · exact copy_price A.size _ (Nat.size_le_size (h r))
  · simp

theorem constant_control {F C : ℕ} (accepted : Bool) (row : Vector Cell C) :
    (constant F accepted row).control≤F*(C*36+41)+10 := by
  have h := mapBlock_control (Vector.replicate F row) (fun d r =>
    if accepted && decide (d.val=0) then
      let copied := copy (row.get r)
      (⟨copied.value,copied.bitSteps,4⟩ : Run Cell)
    else ⟨zero,0,4⟩) (W:=4) (by intro d r; split <;> exact le_refl 4)
  simp only [constant]
  nlinarith

def normalAsOpposite {L : ℕ} (n : Vector NormalLetter L) : Fin L → OppositeLetter :=
  fun i => if n.get i=.p2 then .w else .s

theorem normalAsOpposite_bits {L : ℕ} (n : Vector NormalLetter L) :
    oppositeWBits (normalAsOpposite n)=normalP2Bits n.get := by
  funext i
  cases h : n.get i <;> simp [normalAsOpposite,normalP2Bits,oppositeWBits,h]

def execute {L C : ℕ} (F : ℕ) (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) : Run (Block F C) :=
  let row := readRow raw n o
  let normal := BinaryCroppedHighInput.test capCell (normalAsOpposite n)
  let opposite := BinaryCroppedHighInput.test capCell o.get
  let out := constant F (normal.value && opposite.value) row.value
  ⟨out.value,normal.bitSteps+opposite.bitSteps+out.bitSteps,row.control+out.control+8*L+12⟩

theorem execute_view {L C F : ℕ} (cap : ℕ) (capCell : Cell) (hc : view capCell=(cap:ℤ))
    (raw : BinarySourceFormation.RawStore L C) (n : Vector NormalLetter L) (o : Vector OppositeLetter L)
    (d : Fin F) (r : Fin C) :
    cellView (execute F capCell raw n o).value d r = if d.val=0 then
      cropBoth cap (fun nn oo => view (BinarySourceFormation.readRaw raw nn oo r)) n.get o.get else 0 := by
  simp only [execute,constant_view,BinaryCroppedHighInput.test_value cap capCell hc,normalAsOpposite_bits,readRow_get]
  by_cases hd : d.val=0 <;> by_cases hn : ones (normalP2Bits n.get)≤cap <;>
    by_cases ho : ones (oppositeWBits o.get)≤cap <;> simp [hd,hn,ho,cropBoth,CroppedSourceContraction.crop]

def RawBound {L C : ℕ} (raw : BinarySourceFormation.RawStore L C) (A : ℕ) : Prop :=
  ∀ n o r, (view (BinarySourceFormation.readRaw raw n o r)).natAbs≤A

theorem execute_bound {L C F : ℕ} (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) (A : ℕ) (ha : RawBound raw A) :
    Bound A (execute F capCell raw n o).value := by
  apply constant_bound
  intro r
  rw [readRow_get]
  exact ha _ _ _

def bitBudget (L C F cap A : ℕ) : ℕ := 2*BinaryCroppedHighInput.testBudget L cap+F*(C*BackendScalarBits.backendScalarUnit A.size)
def controlBudget (L C F : ℕ) : ℕ := 12*L+24+16*(L+1)^2+F*(C*36+41)

theorem execute_bits {L C F : ℕ} (cap : ℕ) (capCell : Cell) (hc : view capCell=(cap:ℤ))
    (raw : BinarySourceFormation.RawStore L C) (n : Vector NormalLetter L) (o : Vector OppositeLetter L)
    (A : ℕ) (ha : RawBound raw A) : (execute F capCell raw n o).bitSteps≤bitBudget L C F cap A := by
  have hn := BinaryCroppedHighInput.test_price cap capCell hc (normalAsOpposite n)
  have ho := BinaryCroppedHighInput.test_price cap capCell hc o.get
  have he := constant_bits (F:=F) ((BinaryCroppedHighInput.test capCell (normalAsOpposite n)).value &&
    (BinaryCroppedHighInput.test capCell o.get).value) (readRow raw n o).value A (by intro r; rw [readRow_get]; exact ha _ _ _)
  simp only [execute,bitBudget]
  omega

theorem execute_control {L C F : ℕ} (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) :
    (execute F capCell raw n o).control≤controlBudget L C F := by
  have h := constant_control (F:=F) ((BinaryCroppedHighInput.test capCell (normalAsOpposite n)).value &&
    (BinaryCroppedHighInput.test capCell o.get).value) (readRow raw n o).value
  simp only [execute,readRow_control,controlBudget]
  omega

/-- Original integer cap enters once at this boundary. A recursive root may
instead share one encoded cap across every call to execute. -/
def run {L C : ℕ} (F cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) : Run (Block F C) :=
  let capCell := BinaryMultiplierAdapter.encodeInteger (cap:ℤ)
  let out := execute F capCell.value raw n o
  ⟨out.value,capCell.bitSteps+out.bitSteps,out.control+4⟩

theorem run_bits {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (n : Vector NormalLetter L) (o : Vector OppositeLetter L) (A : ℕ) (ha : RawBound raw A) :
    (run F cap raw n o).bitSteps≤10*(cap.size+1)^2+bitBudget L C F cap A := by
  have he := BinaryMultiplierAdapter.encodeInteger_cost (cap:ℤ)
  have hr := execute_bits (F:=F) cap _ (BinaryMultiplierAdapter.encodeInteger_view _) raw n o A ha
  simp only [run,Int.natAbs_natCast] at *
  omega

#print axioms readRow_get
#print axioms readRow_control
#print axioms constant_view
#print axioms constant_bound
#print axioms constant_bits
#print axioms constant_control
#print axioms normalAsOpposite_bits
#print axioms execute_view
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
#print axioms run_bits
end ThinMatrix.BinaryResidualLeaf
