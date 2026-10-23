import GroupedCoordinates

set_option autoImplicit false

/-! Counted construction of all signed source groups and selector rows from
raw coefficient arrays and Boolean request keys. Every traversal, retained
intermediate, source read, coefficient write and scalar negation is charged
in the scalar/Boolean/bounded-register model. Binary scalar and address
prices remain a separate refinement, as does formation of the raw source. -/
namespace ThinMatrix.GroupedPreparation
open CappedBitPreparation GroupedCoordinates CroppedGroupedSuffix
open scoped BigOperators

structure Counted (A : Type) where
  value : A
  work : ℕ

/-- Obtain the executable loop length from retained storage, not its type's
cardinality expression. The cast and all index-bound proofs are erased. -/
def ofStoredFn {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → B) : Vector B N :=
  Vector.cast shape.size_toArray (Vector.ofFn (fun i : Fin shape.toArray.size =>
    f ⟨i.val,by simpa only [shape.size_toArray] using i.isLt⟩))

theorem ofStoredFn_eq {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → B) :
    ofStoredFn shape f = Vector.ofFn f := by
  rcases shape with ⟨a,h⟩
  cases h
  rfl

def mapVector {A B : Type} {N : ℕ} (f : A → Counted B) (v : Vector A N) : Counted (Vector B N) :=
  let results := v.map f
  ⟨results.map Counted.value,(results.toList.map Counted.work).sum+16*v.toArray.size+4⟩

@[simp] theorem mapVector_get {A B : Type} {N : ℕ} (f : A → Counted B) (v : Vector A N) (i : Fin N) :
    (mapVector f v).value.get i = (f (v.get i)).value := by simp [mapVector]

theorem mapVector_work {A B : Type} {N W : ℕ} (f : A → Counted B) (v : Vector A N)
    (h : ∀ a, (f a).work ≤ W) : (mapVector f v).work ≤ N*(W+16)+4 := by
  have hs := List.sum_le_card_nsmul ((v.map f).toList.map Counted.work) W (by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    rw [Vector.toList_map] at hb
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
    exact h a)
  simp only [List.length_map,Vector.length_toList,smul_eq_mul] at hs
  simp only [mapVector,Vector.size_toArray]
  nlinarith

def mapArray {A B : Type} (f : A → Counted B) (v : Array A) : Counted (Array B) :=
  let results := v.map f
  ⟨results.map Counted.value,results.foldl (fun w row => w+row.work) 0+16*v.size+4⟩

@[simp] theorem mapArray_size {A B : Type} (f : A → Counted B) (v : Array A) :
    (mapArray f v).value.size = v.size := by simp [mapArray]

@[simp] theorem mapArray_get {A B : Type} (f : A → Counted B) (v : Array A) (i : ℕ) (hi : i<v.size) :
    (mapArray f v).value[i]'(by simpa using hi) = (f v[i]).value := by simp [mapArray]

theorem mapArray_work {A B : Type} {W : ℕ} (f : A → Counted B) (v : Array A)
    (h : ∀ a, (f a).work ≤ W) : (mapArray f v).work ≤ v.size*(W+16)+4 := by
  have hs := BinaryArrayCosts.array_fold_cost_bound (v.map f) Counted.work W (by
    intro b hb
    obtain ⟨a,_,rfl⟩ := Array.mem_map.mp hb
    exact h a)
  simp only [Array.size_map] at hs
  simp only [mapArray,Array.size_map]
  nlinarith

def keyVector (n r : ℕ) : Vector (Key n) (CappedSubsetList.count n r) :=
  ⟨(generate n r).toArray,by simp [generate_length]⟩

@[simp] theorem keyVector_toList (n r : ℕ) : (keyVector n r).toList = generate n r := by
  simp [keyVector,Vector.toList]

theorem sum_keys {R : Type} [AddCommMonoid R] (n r : ℕ) (f : Finset (Fin n) → R) :
    (∑ j, f (support ((keyVector n r).get j))) =
      ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => J.card ≤ r), f J := by
  rw [StoredGroupedCompletion.vector_sum (keyVector n r) (fun k => f (support k)),keyVector_toList]
  change ((generate n r).map (f ∘ support)).sum = _
  rw [← List.map_map,← List.sum_toFinset f ((generate_nodup n r).map support_injective),generated_supports]

def storeKeys (n r : ℕ) : Counted (Vector (Key n) (CappedSubsetList.count n r)) :=
  let out := execute n r
  ⟨⟨out.keys.toArray,by simp [out,execute_keys,generate_length]⟩,out.work+4*out.keys.length+2⟩

@[simp] theorem storeKeys_value (n r : ℕ) : (storeKeys n r).value = keyVector n r := by
  simp only [storeKeys,keyVector,execute_keys]

def keyBudget (n r : ℕ) : ℕ := (n+1)*(8*n+32)*CappedSubsetList.count n r+4*CappedSubsetList.count n r+2

theorem storeKeys_work (n r : ℕ) : (storeKeys n r).work ≤ keyBudget n r := by
  have h := work_bound n r
  simp only [storeKeys,execute_keys,generate_length,keyBudget]
  omega

theorem count_full (n : ℕ) : CappedSubsetList.count n n = 2^n := Nat.sum_range_choose n

def pairKeys (n : ℕ) : Vector (Key n) (2^n) := Vector.cast (count_full n) (keyVector n n)

@[simp] theorem pairKeys_toList (n : ℕ) : (pairKeys n).toList = generate n n := by
  rw [pairKeys,Vector.toList_cast,keyVector_toList]

theorem pairKeys_nodup (n : ℕ) : (pairKeys n).toList.Nodup := by
  rw [pairKeys_toList]
  exact generate_nodup n n

theorem pairKeys_supports (n : ℕ) :
    ((pairKeys n).toList.map support).toFinset = Finset.univ := by
  rw [pairKeys_toList,generated_supports]
  ext J
  have hJ : J.card ≤ n := by simpa using Finset.card_le_univ J
  simp [hJ]

def storePairs (n : ℕ) : Counted (Vector (Key n) (2^n)) :=
  let out := storeKeys n n
  ⟨Vector.cast (count_full n) out.value,out.work+2⟩

@[simp] theorem storePairs_value (n : ℕ) : (storePairs n).value = pairKeys n := by
  simp [storePairs,pairKeys]

theorem storePairs_work (n : ℕ) : (storePairs n).work ≤ keyBudget n n+2 :=
  Nat.add_le_add_right (storeKeys_work n n) 2

variable {R : Type} [CommRing R]

def datum {n C : ℕ} (X : StoredGroupedCompletion.Source n C R) (p k : Key n) : Counted (Vector R C) :=
  let pos := coordinates p k
  let index : Fin (3^n) := ⟨pos.index,coordinates_lt p k⟩
  let row := ofStoredFn X (fun c =>
    let x := (X.get c).get index
    if pos.negative then -x else x)
  ⟨row,pos.work+12*X.toArray.size+8⟩

theorem datum_value {n C : ℕ} (X : StoredGroupedCompletion.Source n C R) (p k : Key n) (c : Fin C) :
    (datum X p k).value.get c = data p.get (StoredGroupedCompletion.readSource X c) (support k) := by
  have hi : (⟨(coordinates p k).index,coordinates_lt p k⟩ : Fin (3^n)) =
      StoredGroupedCompletion.rawIndex n (word p.get (support k)) := Fin.ext (coordinates_index p k)
  simp only [datum,ofStoredFn_eq,Vector.get_ofFn,hi,data,StoredGroupedCompletion.readSource]
  rw [← coordinates_sign]
  cases h : (coordinates p k).negative <;> simp [sign]

theorem datum_work {n C : ℕ} (X : StoredGroupedCompletion.Source n C R) (p k : Key n) :
    (datum X p k).work = 28*n+12*C+16 := by simp only [datum,coordinates_work,Vector.size_toArray]; omega

structure Prepared (n r C : ℕ) (R : Type) where
  keys : Vector (Key n) (CappedSubsetList.count n r)
  pairs : Vector (Key n) (2^n)
  groups : Vector (Vector (Vector R C) (CappedSubsetList.count n r)) (2^n)

def prepare {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R) : Counted (Prepared n r C R) :=
  let keys := storeKeys n r
  let pairs := storePairs n
  let groups := mapVector (fun p => mapVector (datum X p) keys.value) pairs.value
  ⟨⟨keys.value,pairs.value,groups.value⟩,keys.work+pairs.work+groups.work+12⟩

@[simp] theorem prepare_keys {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R) :
    (prepare r X).value.keys = keyVector n r := by simp [prepare]
@[simp] theorem prepare_pairs {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R) :
    (prepare r X).value.pairs = pairKeys n := by simp [prepare]

theorem prepare_get {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R)
    (p : Fin (2^n)) (j : Fin (CappedSubsetList.count n r)) (c : Fin C) :
    (((prepare r X).value.groups.get p).get j).get c =
      data ((pairKeys n).get p).get (StoredGroupedCompletion.readSource X c)
        (support ((keyVector n r).get j)) := by
  simp only [prepare,mapVector_get,storeKeys_value,storePairs_value,datum_value]

def prepareBudget (n r C : ℕ) : ℕ :=
  keyBudget n r+keyBudget n n+2^n*(CappedSubsetList.count n r*(28*n+12*C+32)+20)+18

theorem prepare_work {n C : ℕ} (r : ℕ) (X : StoredGroupedCompletion.Source n C R) :
    (prepare r X).work ≤ prepareBudget n r C := by
  have hrow (p : Key n) := mapVector_work (datum X p) (storeKeys n r).value
    (fun k => le_of_eq (datum_work X p k))
  have hg := mapVector_work (fun p => mapVector (datum X p) (storeKeys n r).value)
    (storePairs n).value hrow
  have hk := storeKeys_work n r
  have hp := storePairs_work n
  simp only [prepare,prepareBudget]
  nlinarith

def selectorRow {n S : ℕ} (keys : Vector (Key n) S) (a : Key n) : Counted (Vector Bool S) :=
  mapVector (fun k => let out := subset k a; ⟨out.1,out.2⟩) keys

theorem selectorRow_get {n S : ℕ} (keys : Vector (Key n) S) (a : Key n) (j : Fin S) :
    (selectorRow keys a).value.get j = decide (support (keys.get j) ⊆ support a) := by
  simp only [selectorRow,mapVector_get,subset_correct]

theorem selectorRow_work {n S : ℕ} (keys : Vector (Key n) S) (a : Key n) :
    (selectorRow keys a).work ≤ S*(26*n+24)+4 := by
  have h := mapVector_work (fun k => let out := subset k a; (⟨out.1,out.2⟩ : Counted Bool)) keys
    (fun k => le_of_eq (subset_work k a))
  simpa only [selectorRow,Nat.add_assoc] using h

def selectors {n S : ℕ} (keys : Vector (Key n) S) (requests : Array (Key n)) : Counted (Array (Vector Bool S)) :=
  mapArray (selectorRow keys) requests

@[simp] theorem selectors_size {n S : ℕ} (keys : Vector (Key n) S) (requests : Array (Key n)) :
    (selectors keys requests).value.size = requests.size := mapArray_size _ _

theorem selectors_get {n S : ℕ} (keys : Vector (Key n) S) (requests : Array (Key n))
    (i : ℕ) (hi : i<requests.size) (j : Fin S) :
    ((selectors keys requests).value[i]'(by simpa using hi)).get j =
      decide (support (keys.get j) ⊆ support requests[i]) := by
  exact (congrArg (fun v : Vector Bool S => v.get j)
    (mapArray_get (selectorRow keys) requests i hi)).trans (selectorRow_get keys requests[i] j)

theorem selectors_work {n S : ℕ} (keys : Vector (Key n) S) (requests : Array (Key n)) :
    (selectors keys requests).work ≤ requests.size*(S*(26*n+24)+20)+4 := by
  have h := mapArray_work (selectorRow keys) requests (selectorRow_work keys)
  simpa only [selectors,Nat.add_assoc] using h

#print axioms ofStoredFn_eq
#print axioms mapVector_get
#print axioms mapVector_work
#print axioms mapArray_size
#print axioms mapArray_get
#print axioms mapArray_work
#print axioms keyVector_toList
#print axioms sum_keys
#print axioms storeKeys_value
#print axioms storeKeys_work
#print axioms count_full
#print axioms pairKeys_toList
#print axioms pairKeys_nodup
#print axioms pairKeys_supports
#print axioms storePairs_value
#print axioms storePairs_work
#print axioms datum_value
#print axioms datum_work
#print axioms prepare_keys
#print axioms prepare_pairs
#print axioms prepare_get
#print axioms prepare_work
#print axioms selectorRow_get
#print axioms selectorRow_work
#print axioms selectors_size
#print axioms selectors_get
#print axioms selectors_work
end ThinMatrix.GroupedPreparation
