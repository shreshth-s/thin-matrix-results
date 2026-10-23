import GroupedPreparation

set_option autoImplicit false

/-! Complete elementary grouped suffix execution from raw coefficient arrays
and stored request keys. The program generates its own support/pair keys,
constructs all source groups and selector matrices, and returns every full
coefficient vector. No prepared-matrix or preparation-work hypothesis occurs
in the final contract. This is a scalar/Boolean/bounded-register program;
fast rectangular multiplication, binary prices and raw root formation are
separate unresolved dependencies of the faster APSP theorem. -/
namespace ThinMatrix.PreparedGroupedProgram
open CappedBitPreparation CroppedGroupedSuffix GroupedPreparation
open scoped BigOperators
variable {R : Type} [CommRing R]

abbrev Requests (n : ℕ) := Vector (Array (Key n)) (2^n)

/-- Supply the elementary completion's inner dimension from the stored
operand length. No binomial-sum evaluator runs to recover this dimension. -/
def completeStored {S C : ℕ} (masks : Array (Vector Bool S)) (data : Vector (Vector R C) S) :
    GroupedMaskCompletion.Execution C R :=
  let masks' : Array (Vector Bool data.toArray.size) :=
    cast (congrArg (fun k => Array (Vector Bool k)) data.size_toArray.symm) masks
  GroupedMaskCompletion.runMatrix masks' ⟨data.toArray,rfl⟩

theorem completeStored_eq {S C : ℕ} (masks : Array (Vector Bool S)) (data : Vector (Vector R C) S) :
    completeStored masks data = GroupedMaskCompletion.runMatrix masks data := by
  rcases data with ⟨a,h⟩
  cases h
  rfl

def runGroup {n r C : ℕ} (stored : Prepared n r C R) (p : Fin (2^n))
    (requests : Array (Key n)) : Counted (Array (Vector R C)) :=
  let masks := selectors stored.keys requests
  let out := completeStored masks.value (stored.groups.get p)
  ⟨out.outputs,masks.work+out.work+8⟩

@[simp] theorem runGroup_size {n r C : ℕ} (stored : Prepared n r C R) (p : Fin (2^n))
    (requests : Array (Key n)) : (runGroup stored p requests).value.size = requests.size := by
  simp [runGroup,completeStored_eq]

theorem runGroup_correct {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R)
    (p : Fin (2^n)) (requests : Array (Key n)) (i : ℕ) (hi : i<requests.size) (c : Fin C) :
    ((runGroup (prepare r X).value p requests).value[i]'(by simpa using hi)).get c =
      transform ((pairKeys n).get p).get (support requests[i])
        (crop r (StoredGroupedCompletion.readSource X c)) := by
  have h := GroupedMaskCompletion.runMatrix_get (selectors (prepare r X).value.keys requests).value
    ((prepare r X).value.groups.get p) i (by simpa using hi) c
  have hm (j : Fin (CappedSubsetList.count n r)) :=
    selectors_get (prepare r X).value.keys requests i hi j
  simp only [runGroup,completeStored_eq]
  rw [h]
  simp only [hm,decide_eq_true_eq]
  simp only [prepare_keys,prepare_get]
  rw [sum_keys n r (fun J => if J ⊆ support requests[i] then
    data ((pairKeys n).get p).get (StoredGroupedCompletion.readSource X c) J else 0),transform_cropped]

def groupPrice (n r C : ℕ) : ℕ := CappedSubsetList.count n r*(26*n+8*C+40)+3*C+40

theorem runGroup_work {n r C : ℕ} (stored : Prepared n r C R) (p : Fin (2^n))
    (requests : Array (Key n)) :
    (runGroup stored p requests).work ≤ requests.size*groupPrice n r C+16 := by
  have hs := selectors_work stored.keys requests
  have hc := GroupedMaskCompletion.runMatrix_work (selectors stored.keys requests).value (stored.groups.get p)
  rw [selectors_size] at hc
  simp only [runGroup,completeStored_eq,groupPrice]
  nlinarith

def runAll {n r C : ℕ} (stored : Prepared n r C R) (requests : Requests n) :
    Counted (Vector (Array (Vector R C)) (2^n)) :=
  let results := ofStoredFn stored.groups (fun p => runGroup stored p (requests.get p))
  ⟨results.map Counted.value,(results.toList.map Counted.work).sum+16*stored.groups.toArray.size+4⟩

@[simp] theorem runAll_get {n r C : ℕ} (stored : Prepared n r C R) (requests : Requests n) (p : Fin (2^n)) :
    (runAll stored requests).value.get p = (runGroup stored p (requests.get p)).value := by
  simp only [runAll,ofStoredFn_eq,Vector.get_map,Vector.get_ofFn]

theorem runAll_work {n r C : ℕ} (stored : Prepared n r C R) (requests : Requests n) :
    (runAll stored requests).work ≤
      StoredGroupedCompletion.requestCount requests*groupPrice n r C+32*2^n+4 := by
  have h := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin (2^n)))) =>
    runGroup_work stored p (requests.get p))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    ← Finset.sum_mul] at h
  have he : (∑ p, (requests.get p).size) = StoredGroupedCompletion.requestCount requests :=
    StoredGroupedCompletion.vector_sum requests Array.size
  rw [he] at h
  simp only [runAll,ofStoredFn_eq,Vector.size_toArray,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  omega

/-- Retain the one preparation result and pass that value to every group. -/
def execute {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R) (requests : Requests n) :
    Counted (Vector (Array (Vector R C)) (2^n)) :=
  let prepared := prepare r X
  let out := runAll prepared.value requests
  ⟨out.value,prepared.work+out.work+12⟩

@[simp] theorem execute_size {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R)
    (requests : Requests n) (p : Fin (2^n)) :
    ((execute r X requests).value.get p).size = (requests.get p).size := by
  simp [execute]

theorem execute_correct {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R)
    (requests : Requests n) (p : Fin (2^n)) (i : Fin (requests.get p).size) (c : Fin C) :
    (((execute r X requests).value.get p)[i.val]'(by simp)).get c =
      transform ((pairKeys n).get p).get (support (requests.get p)[i.val])
        (crop r (StoredGroupedCompletion.readSource X c)) := by
  simpa only [execute,runAll_get] using runGroup_correct r X p (requests.get p) i.val i.isLt c

def totalBudget (n r C M : ℕ) : ℕ := prepareBudget n r C+M*groupPrice n r C+32*2^n+16

theorem execute_work {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R) (requests : Requests n) :
    (execute r X requests).work ≤ totalBudget n r C (StoredGroupedCompletion.requestCount requests) := by
  have hp := prepare_work r X
  have hr := runAll_work (prepare r X).value requests
  simp only [execute,totalBudget]
  omega

theorem data_cells {n B q F : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n (B*q*F) R) :
    ((prepare r X).value.groups.toList.map (fun group =>
      (group.toList.map (fun row => row.toList.length)).sum)).sum =
      2^n*CappedSubsetList.count n r*(B*q*F) := by
  simp [Vector.length_toList,Nat.mul_assoc]

theorem output_cells {n B q F : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n (B*q*F) R)
    (requests : Requests n) :
    ((execute r X requests).value.toList.map (fun rows =>
      (rows.toList.map (fun row => row.toList.length)).sum)).sum =
      StoredGroupedCompletion.requestCount requests*(B*q*F) := by
  rw [← StoredGroupedCompletion.vector_sum (execute r X requests).value
    (fun rows => (rows.toList.map (fun row => row.toList.length)).sum)]
  have hrow (p : Fin (2^n)) :
      (((execute r X requests).value.get p).toList.map (fun row => row.toList.length)).sum =
      (requests.get p).size*(B*q*F) := by
    simp [Vector.length_toList,execute_size]
  simp only [hrow,← Finset.sum_mul]
  rw [StoredGroupedCompletion.vector_sum requests Array.size]
  rfl

/-- Closed finite-source contract, with only the actual raw source and
request arrays as input; no successful preparation or cost premise. -/
theorem correctness_and_work {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R)
    (requests : Requests n) :
    (∀ p : Fin (2^n), ∀ i : Fin (requests.get p).size, ∀ c : Fin C,
      (((execute r X requests).value.get p)[i.val]'(by simp)).get c =
        transform ((pairKeys n).get p).get (support (requests.get p)[i.val])
          (crop r (StoredGroupedCompletion.readSource X c))) ∧
      (execute r X requests).work ≤ totalBudget n r C (StoredGroupedCompletion.requestCount requests) :=
  ⟨fun p i c => execute_correct r X requests p i c,execute_work r X requests⟩

#print axioms completeStored_eq
#print axioms runGroup_size
#print axioms runGroup_correct
#print axioms runGroup_work
#print axioms runAll_get
#print axioms runAll_work
#print axioms execute_size
#print axioms execute_correct
#print axioms execute_work
#print axioms data_cells
#print axioms output_cells
#print axioms correctness_and_work
end ThinMatrix.PreparedGroupedProgram
