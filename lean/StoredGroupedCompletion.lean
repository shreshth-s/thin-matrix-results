import GroupedMaskCompletion

set_option autoImplicit false

/-!
# Stored cropped suffix groups and independent completion matrices

The source is a matrix of stored coefficient vectors. Preprocessing retains
all pair-bit groups, all capped supports, and all coefficient columns. Each
group receives its own requested selector matrix. The reference completion
returns complete vectors and proves exact reconstruction of the cropped
ordinary suffix transform. It makes no fast rectangular-cost assumption.
The counted entry points consume stored masks and groups. `prepare`,
`selectors`, and `selectorFamilies` are executable preprocessing with exact
storage/refinement results, but their execution costs are not yet proved.
-/
namespace ThinMatrix.StoredGroupedCompletion
open CroppedGroupedSuffix WalshEmbedding GroupedMaskCompletion
open scoped BigOperators
variable {R : Type} [CommRing R]

def rawIndex (n : ℕ) : Word n ≃ Fin (3^n) := finFunctionFinEquiv

def supports (n r : ℕ) : Vector (Finset (Fin n)) (CappedSubsetList.count n r) :=
  ⟨CappedSubsetList.array n r,CappedSubsetList.array_size n r⟩

theorem supports_toList (n r : ℕ) : (supports n r).toList = CappedSubsetList.generate n r := by
  simp [supports,CappedSubsetList.array,Vector.toList]

theorem vector_sum {α M : Type} [AddCommMonoid M] {N : ℕ} (v : Vector α N) (f : α → M) :
    (∑ j, f (v.get j)) = (v.toList.map f).sum := by
  have h : Vector.ofFn (fun j => v.get j) = v := by ext i hi; simp only [Vector.getElem_ofFn]; rfl
  have hl := congrArg Vector.toList h
  rw [Vector.toList_ofFn] at hl
  rw [← hl,List.map_ofFn,List.sum_ofFn]
  rfl

theorem sum_supports (n r : ℕ) (f : Finset (Fin n) → R) :
    (∑ j, f ((supports n r).get j)) =
      ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => J.card ≤ r), f J := by
  rw [vector_sum,supports_toList,← List.sum_toFinset f (CappedSubsetList.generate_nodup n r),
    CappedSubsetList.generate_toFinset]

abbrev Source (n C : ℕ) (R : Type) := Vector (Vector R (3^n)) C

def readSource {n C : ℕ} (X : Source n C R) (c : Fin C) (w : Word n) : R :=
  (X.get c).get (rawIndex n w)

structure Prepared (n r C : ℕ) (R : Type) where
  keys : Vector (Finset (Fin n)) (CappedSubsetList.count n r)
  groups : Vector (Vector (Vector R C) (CappedSubsetList.count n r)) (2^n)

/-- The support list is computed once. Every signed raw entry is copied to
every pair-bit group to which it belongs; no duplication is suppressed. -/
def prepare {n C : ℕ} (r : ℕ) (X : Source n C R) : Prepared n r C R :=
  let keys := supports n r
  let groups := Vector.ofFn (fun p : Fin (2^n) =>
    let bits := (HalfSourceIntegerGreedy.cubeIndex n).symm p
    Vector.ofFn (fun j =>
      let J := keys.get j
      let w := word bits J
      let s : R := signed bits J
      Vector.ofFn (fun c => s * readSource X c w)))
  ⟨keys,groups⟩

@[simp] theorem prepare_keys {n C : ℕ} (r : ℕ) (X : Source n C R) :
    (prepare r X).keys = supports n r := rfl

theorem prepare_get {n C : ℕ} (r : ℕ) (X : Source n C R) (p : Fin (2^n))
    (j : Fin (CappedSubsetList.count n r)) (c : Fin C) :
    (((prepare r X).groups.get p).get j).get c =
      data ((HalfSourceIntegerGreedy.cubeIndex n).symm p) (readSource X c) ((supports n r).get j) := by
  simp only [prepare,Vector.get_ofFn,data]

def selectors {n S : ℕ} (keys : Vector (Finset (Fin n)) S)
    (requests : Array (Finset (Fin n))) : Array (Vector Bool S) :=
  requests.map (fun A => Vector.ofFn (fun j => decide (keys.get j ⊆ A)))

def selectorFamilies {n S : ℕ} (keys : Vector (Finset (Fin n)) S)
    (requests : Vector (Array (Finset (Fin n))) (2^n)) : Vector (Array (Vector Bool S)) (2^n) :=
  requests.map (selectors keys)

/-- Counted completion consumes already stored selectors and source groups. -/
def runGroup {n r C : ℕ} (stored : Prepared n r C R) (p : Fin (2^n))
    (masks : Array (Vector Bool (CappedSubsetList.count n r))) : Execution C R :=
  runMatrix masks (stored.groups.get p)

@[simp] theorem runGroup_size {n r C : ℕ} (stored : Prepared n r C R) (p : Fin (2^n))
    (masks : Array (Vector Bool (CappedSubsetList.count n r))) :
    (runGroup stored p masks).outputs.size = masks.size := by simp [runGroup]

theorem runGroup_correct {n C : ℕ} (r : ℕ) (X : Source n C R) (p : Fin (2^n))
    (requests : Array (Finset (Fin n))) (i : ℕ) (hi : i < requests.size) (c : Fin C) :
    (((runGroup (prepare r X) p (selectors (supports n r) requests)).outputs[i]'
      (by simpa [selectors] using hi)).get c) =
      transform ((HalfSourceIntegerGreedy.cubeIndex n).symm p) requests[i]
        (crop r (readSource X c)) := by
  have h := runMatrix_get (selectors (supports n r) requests)
    ((prepare r X).groups.get p) i (by simpa [selectors] using hi) c
  change (((runGroup (prepare r X) p (selectors (supports n r) requests)).outputs[i]'
    (by simpa [selectors] using hi)).get c) = _ at h
  rw [h]
  simp only [selectors,Array.getElem_map,Vector.get_ofFn,decide_eq_true_eq,prepare_get]
  rw [sum_supports n r (fun J => if J ⊆ requests[i] then
    data ((HalfSourceIntegerGreedy.cubeIndex n).symm p) (readSource X c) J else 0),transform_cropped]

theorem runGroup_work {n r C : ℕ} (stored : Prepared n r C R) (p : Fin (2^n))
    (masks : Array (Vector Bool (CappedSubsetList.count n r))) :
    (runGroup stored p masks).work ≤
      masks.size*(CappedSubsetList.count n r*(8*C+16)+3*C+20)+4 :=
  runMatrix_work masks (stored.groups.get p)

/-- Full duplicated source storage, with no omitted batch, cyclic or formal
coefficient factor. -/
theorem data_cells {n B q F : ℕ} (r : ℕ) (X : Source n (B*q*F) R) :
    ((prepare r X).groups.toList.map (fun group =>
      (group.toList.map (fun row => row.toList.length)).sum)).sum =
      2^n*CappedSubsetList.count n r*(B*q*F) := by
  simp [Vector.length_toList,Nat.mul_assoc]

theorem selector_cells {n S : ℕ} (keys : Vector (Finset (Fin n)) S)
    (requests : Array (Finset (Fin n))) :
    ((selectors keys requests).toList.map (fun row => row.toList.length)).sum = requests.size*S := by
  simp [selectors,Vector.length_toList,Function.comp_def]

theorem group_output_cells {n r B q F : ℕ} (stored : Prepared n r (B*q*F) R)
    (p : Fin (2^n)) (masks : Array (Vector Bool (CappedSubsetList.count n r))) :
    ((runGroup stored p masks).outputs.toList.map (fun row => row.toList.length)).sum =
      masks.size*(B*q*F) := output_cells masks (stored.groups.get p)

/-- Group results are kept independently; unrelated selector rows are never
concatenated into a single matrix product. -/
structure AllExecution (n C : ℕ) (R : Type) where
  groups : Vector (Execution C R) (2^n)
  work : ℕ

def runAll {n r C : ℕ} (stored : Prepared n r C R)
    (masks : Vector (Array (Vector Bool (CappedSubsetList.count n r))) (2^n)) : AllExecution n C R :=
  let results := Vector.ofFn (fun p => runGroup stored p (masks.get p))
  ⟨results,(results.toList.map Execution.work).sum+16*2^n+4⟩

@[simp] theorem runAll_get {n r C : ℕ} (stored : Prepared n r C R)
    (masks : Vector (Array (Vector Bool (CappedSubsetList.count n r))) (2^n)) (p : Fin (2^n)) :
    (runAll stored masks).groups.get p = runGroup stored p (masks.get p) := by
  simp only [runAll,Vector.get_ofFn]

theorem runAll_correct {n C : ℕ} (r : ℕ) (X : Source n C R)
    (requests : Vector (Array (Finset (Fin n))) (2^n)) (p : Fin (2^n))
    (i : Fin (requests.get p).size) (c : Fin C) :
    ((((runAll (prepare r X) (selectorFamilies (supports n r) requests)).groups.get p).outputs[i.val]'
      (by simp [selectorFamilies,selectors])).get c) =
      transform ((HalfSourceIntegerGreedy.cubeIndex n).symm p) (requests.get p)[i.val]
        (crop r (readSource X c)) := by
  simpa only [runAll_get,selectorFamilies,Vector.get_map] using
    runGroup_correct r X p (requests.get p) i.val i.isLt c

def requestCount {A : Type} {N : ℕ} (requests : Vector (Array A) N) : ℕ :=
  (requests.toList.map Array.size).sum

theorem all_output_cells {n r B q F : ℕ} (stored : Prepared n r (B*q*F) R)
    (masks : Vector (Array (Vector Bool (CappedSubsetList.count n r))) (2^n)) :
    ((runAll stored masks).groups.toList.map (fun result =>
      (result.outputs.toList.map (fun row => row.toList.length)).sum)).sum =
      requestCount masks*(B*q*F) := by
  simp only [runAll,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    group_output_cells,requestCount]
  rw [← Finset.sum_mul,vector_sum masks Array.size]

theorem all_work {n r C : ℕ} (stored : Prepared n r C R)
    (masks : Vector (Array (Vector Bool (CappedSubsetList.count n r))) (2^n)) :
    (runAll stored masks).work ≤
      requestCount masks*(CappedSubsetList.count n r*(8*C+16)+3*C+20)+20*2^n+4 := by
  have h := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin (2^n)))) =>
    runGroup_work stored p (masks.get p))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    ← Finset.sum_mul] at h
  have he : (∑ p, (masks.get p).size) = requestCount masks := by
    exact vector_sum masks Array.size
  rw [he] at h
  simp only [runAll,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  omega

#print axioms supports_toList
#print axioms vector_sum
#print axioms sum_supports
#print axioms prepare_keys
#print axioms prepare_get
#print axioms runGroup_size
#print axioms runGroup_correct
#print axioms runGroup_work
#print axioms data_cells
#print axioms selector_cells
#print axioms group_output_cells
#print axioms runAll_get
#print axioms runAll_correct
#print axioms all_output_cells
#print axioms all_work
end ThinMatrix.StoredGroupedCompletion
