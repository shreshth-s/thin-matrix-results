import BinaryGroupedCompletion

set_option autoImplicit false

/-! Finite cropped grouped execution from original integer coefficient and
Boolean request arrays. The program retains binary addresses, serialized
inputs, signed cells and every full output vector. Its theorem bounds actual
binary circuit operations separately from Boolean/indexed-control charges.
This elementary algorithm is not the missing fast rectangular algorithm,
root encoder, complete bit-machine simulation or improved APSP theorem. -/
namespace ThinMatrix.BinaryPreparedGroupedProgram
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation BinaryGroupedCompletion
open CappedBitPreparation CroppedGroupedSuffix
open GroupedPreparation (Prepared selectors selectors_size selectors_get selectors_work keyVector pairKeys sum_keys)
open scoped BigOperators
abbrev Requests (n : ℕ) := PreparedGroupedProgram.Requests n

def runGroup {n r C : ℕ} (stored : Prepared n r C Cell) (p : Fin (2^n))
    (requests : Array (Key n)) : Run (Array (Vector Cell C)) :=
  let masks := selectors stored.keys requests
  let out := runMatrix masks.value (stored.groups.get p)
  ⟨out.value,out.bitSteps,masks.work+out.control+8⟩

@[simp] theorem runGroup_size {n r C : ℕ} (stored : Prepared n r C Cell) (p : Fin (2^n))
    (requests : Array (Key n)) : (runGroup stored p requests).value.size = requests.size := by
  simp [runGroup]

theorem runGroup_correct {n C : ℕ} (r : ℕ) (X : Source n C) (p : Fin (2^n))
    (requests : Array (Key n)) (i : ℕ) (hi : i < requests.size) (c : Fin C) :
    view (((runGroup (prepare r X).value p requests).value[i]'(by simpa using hi)).get c) =
      transform ((pairKeys n).get p).get (support requests[i]) (crop r (StoredGroupedCompletion.readSource X c)) := by
  have h := runMatrix_get (selectors (prepare r X).value.keys requests).value
    ((prepare r X).value.groups.get p) i (by simpa using hi) c
  have hm (j : Fin (CappedSubsetList.count n r)) := selectors_get (prepare r X).value.keys requests i hi j
  simp only [runGroup]
  rw [h]
  simp only [hm,decide_eq_true_eq]
  simp only [prepare_keys,prepare_view]
  rw [sum_keys n r (fun J => if J ⊆ support requests[i] then
    data ((pairKeys n).get p).get (StoredGroupedCompletion.readSource X c) J else 0),transform_cropped]

def groupBits (n r C A : ℕ) : ℕ := CappedSubsetList.count n r*(C*BackendScalarBits.backendScalarUnit (n+A.size))
def groupControl (n r C : ℕ) : ℕ := CappedSubsetList.count n r*(26*n+40*C+48)+3*C+56

theorem runGroup_bits {n C : ℕ} (A r : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) (p : Fin (2^n)) (requests : Array (Key n)) :
    (runGroup (prepare r X).value p requests).bitSteps ≤ requests.size*groupBits n r C A := by
  have h := runMatrix_bits A (n+A.size) (selectors (prepare r X).value.keys requests).value
    ((prepare r X).value.groups.get p) (capped_width n r A) (prepare_abs A r X hX p)
  simpa only [runGroup,groupBits,selectors_size] using h

theorem runGroup_control {n r C : ℕ} (stored : Prepared n r C Cell) (p : Fin (2^n))
    (requests : Array (Key n)) :
    (runGroup stored p requests).control ≤ requests.size*groupControl n r C+20 := by
  have hs := selectors_work stored.keys requests
  have hc := runMatrix_control (selectors stored.keys requests).value (stored.groups.get p)
  rw [selectors_size] at hc
  simp only [runGroup,groupControl]
  nlinarith

def runAll {n r C : ℕ} (stored : Prepared n r C Cell) (requests : Requests n) :
    Run (Vector (Array (Vector Cell C)) (2^n)) :=
  tabulate stored.groups (fun p => runGroup stored p (requests.get p))

@[simp] theorem runAll_get {n r C : ℕ} (stored : Prepared n r C Cell) (requests : Requests n) (p : Fin (2^n)) :
    (runAll stored requests).value.get p = (runGroup stored p (requests.get p)).value := by
  simp only [runAll,tabulate_get]

theorem runAll_bits {n C : ℕ} (A r : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) (requests : Requests n) :
    (runAll (prepare r X).value requests).bitSteps ≤
      StoredGroupedCompletion.requestCount requests*groupBits n r C A := by
  have h := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin (2^n)))) =>
    runGroup_bits A r X hX p (requests.get p))
  rw [← Finset.sum_mul,StoredGroupedCompletion.vector_sum requests Array.size] at h
  simpa only [runAll,tabulate_bits_eq,StoredGroupedCompletion.requestCount] using h

theorem runAll_control {n r C : ℕ} (stored : Prepared n r C Cell) (requests : Requests n) :
    (runAll stored requests).control ≤
      StoredGroupedCompletion.requestCount requests*groupControl n r C+52*2^n+8 := by
  have h := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin (2^n)))) =>
    runGroup_control stored p (requests.get p))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    ← Finset.sum_mul] at h
  rw [StoredGroupedCompletion.vector_sum requests Array.size] at h
  simp only [runAll,tabulate_control_eq,StoredGroupedCompletion.requestCount]
  omega

/-- Preparation runs once. Stored cells, masks and every full result persist
across their consumers; no semantic intermediate is serialized again. -/
def execute {n C : ℕ} (r : ℕ) (X : Source n C) (requests : Requests n) :
    Run (Vector (Array (Vector Cell C)) (2^n)) :=
  let prepared := prepare r X
  let out := runAll prepared.value requests
  ⟨out.value,prepared.bitSteps+out.bitSteps,prepared.control+out.control+12⟩

@[simp] theorem execute_size {n C : ℕ} (r : ℕ) (X : Source n C) (requests : Requests n) (p : Fin (2^n)) :
    ((execute r X requests).value.get p).size = (requests.get p).size := by simp [execute]

theorem execute_correct {n C : ℕ} (r : ℕ) (X : Source n C) (requests : Requests n)
    (p : Fin (2^n)) (i : Fin (requests.get p).size) (c : Fin C) :
    view ((((execute r X requests).value.get p)[i.val]'(by simp)).get c) =
      transform ((pairKeys n).get p).get (support (requests.get p)[i.val])
        (crop r (StoredGroupedCompletion.readSource X c)) := by
  simpa only [execute,runAll_get] using runGroup_correct r X p (requests.get p) i.val i.isLt c

def totalBits (n r C A M : ℕ) : ℕ := preparationBits n r C A+M*groupBits n r C A
def totalControl (n r C M : ℕ) : ℕ := preparationControl n r C+M*groupControl n r C+52*2^n+20

theorem execute_bits {n C : ℕ} (A r : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) (requests : Requests n) :
    (execute r X requests).bitSteps ≤ totalBits n r C A (StoredGroupedCompletion.requestCount requests) := by
  exact Nat.add_le_add (prepare_bits A r X hX) (runAll_bits A r X hX requests)

theorem execute_control {n C : ℕ} (r : ℕ) (X : Source n C) (requests : Requests n) :
    (execute r X requests).control ≤ totalControl n r C (StoredGroupedCompletion.requestCount requests) := by
  have hp := prepare_control r X
  have hr := runAll_control (prepare r X).value requests
  simp only [execute,totalControl]
  omega

theorem data_cells {n B q F : ℕ} (r : ℕ) (X : Source n (B*q*F)) :
    ((prepare r X).value.groups.toList.map (fun group =>
      (group.toList.map (fun row => row.toList.length)).sum)).sum =
      2^n*CappedSubsetList.count n r*(B*q*F) := by
  simp [Vector.length_toList,Nat.mul_assoc]

theorem output_cells {n B q F : ℕ} (r : ℕ) (X : Source n (B*q*F)) (requests : Requests n) :
    ((execute r X requests).value.toList.map (fun rows =>
      (rows.toList.map (fun row => row.toList.length)).sum)).sum =
      StoredGroupedCompletion.requestCount requests*(B*q*F) := by
  rw [← StoredGroupedCompletion.vector_sum (execute r X requests).value
    (fun rows => (rows.toList.map (fun row => row.toList.length)).sum)]
  have hrow (p : Fin (2^n)) :
      (((execute r X requests).value.get p).toList.map (fun row => row.toList.length)).sum =
      (requests.get p).size*(B*q*F) := by simp [Vector.length_toList,execute_size]
  simp only [hrow,← Finset.sum_mul]
  rw [StoredGroupedCompletion.vector_sum requests Array.size]
  rfl

/-- Only the original coefficient magnitude is hypothesized. All stored
operand and partial-sum widths and successful preparation are derived. The
two counters deliberately have different units. -/
theorem correctness_and_costs {n C : ℕ} (A r : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) (requests : Requests n) :
    (∀ p : Fin (2^n), ∀ i : Fin (requests.get p).size, ∀ c : Fin C,
      view ((((execute r X requests).value.get p)[i.val]'(by simp)).get c) =
        transform ((pairKeys n).get p).get (support (requests.get p)[i.val])
          (crop r (StoredGroupedCompletion.readSource X c))) ∧
    (execute r X requests).bitSteps ≤ totalBits n r C A (StoredGroupedCompletion.requestCount requests) ∧
    (execute r X requests).control ≤ totalControl n r C (StoredGroupedCompletion.requestCount requests) :=
  ⟨fun p i c => execute_correct r X requests p i c,execute_bits A r X hX requests,execute_control r X requests⟩

#print axioms runGroup_size
#print axioms runGroup_correct
#print axioms runGroup_bits
#print axioms runGroup_control
#print axioms runAll_get
#print axioms runAll_bits
#print axioms runAll_control
#print axioms execute_size
#print axioms execute_correct
#print axioms execute_bits
#print axioms execute_control
#print axioms data_cells
#print axioms output_cells
#print axioms correctness_and_costs
end ThinMatrix.BinaryPreparedGroupedProgram
