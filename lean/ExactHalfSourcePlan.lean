import ExactHalfWeightTable
import HalfSourceRetainedTranslations

set_option autoImplicit false

/-! Retained translation-index selectors. The actual translation list is
constructed, including its zero-dimensional special case, then copied once.
The counters retain translation numerator arithmetic, binary sum updates and
decoding, inverse-weight arithmetic and indexed key/state/selector construction.
Score-kernel/power-table control and binary address lowering remain unpriced. -/
namespace ThinMatrix.ExactHalfSourcePlan
open WalshEmbedding SourceFormation ExactHalfWeightTable
open BinaryGroupedCoordinates

abbrev J (m : ℕ) := (ExactHalfCroppedEmbedding.shifts m).length
abbrev Shifts (m : ℕ) := Vector (Vector Bool m) (J m)
abbrev Picks (L m : ℕ) := Table (Table (Fin (J m)) 2 m) 2 L

def count (m : ℕ) : ℕ := if m=0 then 1 else 64*m^3

theorem count_eq (m : ℕ) : count m=J m := (ExactHalfCroppedEmbedding.shifts_length m).symm

/-- The supplied size is runtime data; the type equality is erased. -/
def indexedBuild {α : Type} {n : ℕ} (size : ℕ) (hs : size=n) (f : Fin n → Program α) : Program (Vector α n) :=
  let out := vectorBuild size (fun i => f (Fin.cast hs i))
  ⟨out.value.cast hs,out.operations⟩

theorem indexedBuild_eq {α : Type} {n : ℕ} (size : ℕ) (hs : size=n) (f : Fin n → Program α) :
    indexedBuild size hs f=vectorBuild n f := by
  subst n; rfl

def sizedScan {n : ℕ} (size : ℕ) (hs : size=n) (cap : ℕ) (evaluate : Fin n → ℕ × ℕ) :
    Option (Fin n) × ℕ :=
  let out := HalfSourceScan.run cap (fun i : Fin size => evaluate (Fin.cast hs i))
  (out.1.map (Fin.cast hs),out.2)

theorem sizedScan_eq {n : ℕ} (size : ℕ) (hs : size=n) (cap : ℕ) (evaluate : Fin n → ℕ × ℕ) :
    sizedScan size hs cap evaluate=HalfSourceScan.run cap evaluate := by
  subst n
  simp [sizedScan]

def storedShifts (m : ℕ) : Shifts m :=
  let ds := ExactHalfCroppedEmbedding.shifts m
  ⟨(ds.map (fun d => Vector.ofFn d)).toArray,by simp [ds,J]⟩

theorem storedShifts_get (m : ℕ) (j : Fin (J m)) :
    ((storedShifts m).get j).get=(ExactHalfCroppedEmbedding.shifts m).get j := by
  funext i
  simp [storedShifts,Vector.get,List.get_eq_getElem]

def evaluate {L m : ℕ} (weights : Store L m) (ds : Shifts m)
    (Q : Cube L) (h : Cube m) (j : Fin (J m)) : ℕ × ℕ :=
  let shifted := Vector.ofFn (xorBits h (ds.get j).get)
  let outer := tableReadProgram 2 L weights (cubeKey Q)
  let inner := tableReadProgram 2 m outer.value (cubeKey shifted.get)
  (inner.value,outer.operations+inner.operations+8*m+8)

theorem evaluate_value {L m : ℕ} (weights : Store L m) (ds : Shifts m)
    (Q : Finset (Fin L)) (h : Cube m) (j : Fin (J m)) :
    (evaluate weights ds (setBits Q) h j).1=
      ExactHalfWeightTable.read weights Q (xorBits h (ds.get j).get) := by
  simp only [evaluate,tableReadProgram_value,ofFn_get,ExactHalfWeightTable.read]

theorem evaluate_work {L m : ℕ} (weights : Store L m) (ds : Shifts m)
    (Q : Cube L) (h : Cube m) (j : Fin (J m)) :
    (evaluate weights ds Q h j).2=2*L+10*m+10 := by
  simp only [evaluate,tableReadProgram_cost]; omega

def select {L m : ℕ} (weights : Store L m) (ds : Shifts m)
    (Q : Cube L) (h : Cube m) : Program (Fin (J m)) :=
  let out := sizedScan (count m) (count_eq m) (m/2) (evaluate weights ds Q h)
  ⟨out.1.getD ⟨0,ExactHalfCroppedEmbedding.shifts_nonempty m⟩,out.2+2⟩

theorem select_value {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (Q : Finset (Fin L)) (h : Cube m) :
    (select (build shape.environment.good (candidates shape.environment.gammaColumns).value).value
      (storedShifts m) (setBits Q) h).value=ExactHalfCroppedEmbedding.scanPick L m Q h := by
  have he (j : Fin (J m)) := evaluate_value
    (build shape.environment.good (candidates shape.environment.gammaColumns).value).value
    (storedShifts m) Q h j
  simp only [storedShifts_get,read_build] at he
  have hs := HalfSourceScan.run_eq_first
    (fun j => ExactHalfCroppedEmbedding.weight L m Q (xorBits h ((ExactHalfCroppedEmbedding.shifts m).get j)))
    _ he (ExactHalfCroppedEmbedding.valid_exists L m Q h)
  simp only [select,sizedScan_eq,hs,Option.getD_some,ExactHalfCroppedEmbedding.scanPick,
    ExactHalfCroppedEmbedding.scan_result]

def selectBudget (L m : ℕ) : ℕ := J m*(2*L+10*m+14)+4

theorem select_work {L m : ℕ} (weights : Store L m) (ds : Shifts m)
    (Q : Cube L) (h : Cube m) : (select weights ds Q h).operations ≤ selectBudget L m := by
  have hs := HalfSourceScan.run_work (m/2) (evaluate weights ds Q h) (2*L+10*m+10)
    (fun j => le_of_eq (evaluate_work _ _ _ _ j))
  simpa only [select,sizedScan_eq,selectBudget,Nat.add_assoc] using Nat.add_le_add_right hs 2

def buildPicks {L m : ℕ} (weights : Store L m) (ds : Shifts m) : Program (Picks L m) :=
  tableBuild 2 L fun Q => tableBuild 2 m fun h => select weights ds (keyCube Q) (keyCube h)

def readPick {L m : ℕ} (picks : Picks L m) (Q : Finset (Fin L)) (h : Cube m) : Fin (J m) :=
  tableRead 2 m (tableRead 2 L picks (cubeKey (setBits Q))) (cubeKey h)

theorem readPick_build {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (Q : Finset (Fin L)) (h : Cube m) :
    readPick (buildPicks
      (build shape.environment.good (candidates shape.environment.gammaColumns).value).value
      (storedShifts m)).value Q h = ExactHalfCroppedEmbedding.scanPick L m Q h := by
  simp only [readPick,buildPicks,tableRead_build,keyCube_cubeKey]
  exact select_value shape Q h

def picksBudget (L m : ℕ) : ℕ := ((selectBudget L m+16*m)*2^m+16*L)*2^L

theorem buildPicks_work {L m : ℕ} (weights : Store L m) (ds : Shifts m) :
    (buildPicks weights ds).operations ≤ picksBudget L m := by
  apply tableBuild_cost; intro Q
  apply tableBuild_cost; intro h
  exact select_work _ _ _ _

structure Plan (L m : ℕ) where
  shifts : Shifts m
  picks : Picks L m
  construction : HalfSourceRetainedTranslations.Payload m

/-- Copy the generated translations once; retain their construction payload. -/
def generatedShifts (m : ℕ) (generated : HalfSourceRetainedTranslations.Payload m)
    (hg : generated.entries=ExactHalfCroppedEmbedding.shifts m) : Shifts m :=
  ⟨(generated.entries.map (fun d => Vector.ofFn d)).toArray,by simp [hg,J]⟩

theorem generatedShifts_value (m : ℕ) :
    generatedShifts m (HalfSourceRetainedTranslations.produce m).value
      (HalfSourceRetainedTranslations.produce_entries m)=storedShifts m := by
  unfold generatedShifts storedShifts
  simp only [HalfSourceRetainedTranslations.produce_entries]

/-- The generator runs once and its payload and charged work are retained.
This remains a partial binary/indexed-control ledger, as stated above. -/
def prepare {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) : Run (Plan L m) :=
  let generated := HalfSourceRetainedTranslations.produce m
  let ds := generatedShifts m generated.value (HalfSourceRetainedTranslations.produce_entries m)
  let cs := candidates shape.environment.gammaColumns
  let weights := build shape.environment.good cs.value
  let picks := buildPicks weights.value ds
  ⟨⟨ds,picks.value,generated.value⟩,generated.bitSteps+cs.bitSteps,
    generated.control+cs.control+weights.operations+picks.operations+(4*m+8)*ds.toArray.size+16⟩

theorem prepare_pick {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (Q : Finset (Fin L)) (h : Cube m) :
    readPick (prepare shape).value.picks Q h=ExactHalfCroppedEmbedding.scanPick L m Q h :=
  by
    simpa only [prepare,generatedShifts_value] using readPick_build shape Q h

theorem prepare_shift {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (j : Fin (J m)) :
    (((prepare shape).value.shifts).get j).get=(ExactHalfCroppedEmbedding.shifts m).get j :=
  by
    simpa only [prepare,generatedShifts_value] using storedShifts_get m j

theorem inverse_bits {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) :
    (candidates shape.environment.gammaColumns).bitSteps ≤ 2^L*candidateBitBudget L := candidates_bits _

theorem prepare_bits {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) :
    (prepare shape).bitSteps ≤ HalfSourceRetainedTranslations.arithmeticBudget m+2^L*candidateBitBudget L :=
  Nat.add_le_add (HalfSourceRetainedTranslations.produce_bits m) (candidates_bits _)

theorem prepare_keeps_generation {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) :
    (prepare shape).value.construction=(HalfSourceRetainedTranslations.produce m).value ∧
    (prepare shape).bitSteps=(HalfSourceRetainedTranslations.produce m).bitSteps+
      (candidates shape.environment.gammaColumns).bitSteps := by constructor <;> rfl

theorem prepare_keeps_arithmetic {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) :
    (HalfSourceBinarySelection.translations m).bitSteps≤(prepare shape).bitSteps := by
  have hg := HalfSourceRetainedTranslations.produce_keeps_arithmetic m
  simp only [prepare]
  omega

def retainedControlBudget (L m : ℕ) : ℕ :=
  HalfSourceRetainedTranslations.indexedControlBudget m+
    (100*(L+m+1)^3+4*L+12)*2^L+1+buildBudget L m+picksBudget L m+(4*m+8)*J m+16

theorem prepare_retained_control {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) :
    (prepare shape).control ≤ retainedControlBudget L m := by
  have hg := HalfSourceRetainedTranslations.produce_control m
  have hw := build_cost shape
  have hp := buildPicks_work
    (build shape.environment.good (candidates shape.environment.gammaColumns).value).value (storedShifts m)
  simp only [prepare,generatedShifts_value,candidates_control,retainedControlBudget,Vector.size_toArray]
  omega

#print axioms count_eq
#print axioms indexedBuild_eq
#print axioms sizedScan_eq
#print axioms storedShifts_get
#print axioms evaluate_value
#print axioms evaluate_work
#print axioms select_value
#print axioms select_work
#print axioms readPick_build
#print axioms buildPicks_work
#print axioms generatedShifts_value
#print axioms prepare_pick
#print axioms prepare_shift
#print axioms inverse_bits
#print axioms prepare_bits
#print axioms prepare_keeps_generation
#print axioms prepare_keeps_arithmetic
#print axioms prepare_retained_control
end ThinMatrix.ExactHalfSourcePlan
