import BinaryGroupedCoordinates

set_option autoImplicit false

/-! The grouped preparation's binary implementation starts with raw integer
coefficient arrays. Each selected input is serialized by the charged boundary
adapter, then copied/negated as stored bits. Ternary addresses are formed in
binary and decoded once per group/support pair. All source coefficients and
all intermediate circuit results are retained; semantic integers are used
only at the original-input boundary and in specifications. -/
namespace ThinMatrix.BinaryGroupedPreparation
open BinaryCell BinaryGroupedCoordinates CappedBitPreparation GroupedPreparation CroppedGroupedSuffix
open scoped BigOperators

/-- All three projections and the two counter traversals are included in the
Boolean/indexed-control annotation. Lengths come from retained storage. -/
def tabulate {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → Run B) : Run (Vector B N) :=
  let rows := ofStoredFn shape f
  ⟨rows.map Run.value,(rows.toList.map Run.bitSteps).sum,
    (rows.toList.map Run.control).sum+32*shape.toArray.size+8⟩

@[simp] theorem tabulate_get {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → Run B) (i : Fin N) :
    (tabulate shape f).value.get i = (f i).value := by simp only [tabulate,ofStoredFn_eq,Vector.get_map,Vector.get_ofFn]

theorem tabulate_bits_eq {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → Run B) :
    (tabulate shape f).bitSteps = ∑ i, (f i).bitSteps := by
  simp only [tabulate,ofStoredFn_eq,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem tabulate_control_eq {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → Run B) :
    (tabulate shape f).control = (∑ i, (f i).control)+32*N+8 := by
  simp only [tabulate,ofStoredFn_eq,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply,Vector.size_toArray]

theorem tabulate_bits {A B : Type} {N W : ℕ} (shape : Vector A N) (f : Fin N → Run B)
    (h : ∀ i, (f i).bitSteps ≤ W) : (tabulate shape f).bitSteps ≤ N*W := by
  rw [tabulate_bits_eq]
  calc
    _ ≤ ∑ _i : Fin N, W := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

theorem tabulate_control {A B : Type} {N W : ℕ} (shape : Vector A N) (f : Fin N → Run B)
    (h : ∀ i, (f i).control ≤ W) : (tabulate shape f).control ≤ N*(W+32)+8 := by
  rw [tabulate_control_eq]
  have hh : (∑ i, (f i).control) ≤ N*W := by
    calc
      _ ≤ ∑ _i : Fin N, W := Finset.sum_le_sum (fun i _ => h i)
      _ = _ := by simp
  nlinarith

def mapArray {A B : Type} (f : A → Run B) (v : Array A) : Run (Array B) :=
  let rows := v.map f
  ⟨rows.map Run.value,rows.foldl (fun s r => s+r.bitSteps) 0,
    rows.foldl (fun s r => s+r.control) 0+32*v.size+8⟩

@[simp] theorem mapArray_size {A B : Type} (f : A → Run B) (v : Array A) :
    (mapArray f v).value.size = v.size := by simp [mapArray]

@[simp] theorem mapArray_get {A B : Type} (f : A → Run B) (v : Array A) (i : ℕ) (hi : i<v.size) :
    (mapArray f v).value[i]'(by simpa using hi) = (f v[i]).value := by simp [mapArray]

theorem mapArray_bits {A B : Type} {W : ℕ} (f : A → Run B) (v : Array A)
    (h : ∀ a ∈ v, (f a).bitSteps ≤ W) : (mapArray f v).bitSteps ≤ v.size*W := by
  have hh := BinaryArrayCosts.array_fold_cost_bound (v.map f) Run.bitSteps W (by
    intro r hr
    obtain ⟨a,ha,rfl⟩ := Array.mem_map.mp hr
    exact h a ha)
  simpa only [mapArray,Array.size_map] using hh

theorem mapArray_control {A B : Type} {W : ℕ} (f : A → Run B) (v : Array A)
    (h : ∀ a ∈ v, (f a).control ≤ W) : (mapArray f v).control ≤ v.size*(W+32)+8 := by
  have hh := BinaryArrayCosts.array_fold_cost_bound (v.map f) Run.control W (by
    intro r hr
    obtain ⟨a,ha,rfl⟩ := Array.mem_map.mp hr
    exact h a ha)
  simp only [Array.size_map] at hh
  simp only [mapArray,Array.size_map]
  nlinarith

def signedCopy (negative : Bool) (x : Cell) : BinaryCell.Result Cell := if negative then neg x else copy x

theorem signedCopy_view (b : Bool) (x : Cell) : view (signedCopy b x).value = sign b*view x := by
  cases b <;> simp [signedCopy,sign]

theorem signedCopy_abs (b : Bool) (x : Cell) : (view (signedCopy b x).value).natAbs = (view x).natAbs := by
  cases b <;> simp [signedCopy]

theorem signedCopy_bits (A : ℕ) (b : Bool) (x : Cell) (hx : (view x).natAbs ≤ A) :
    (signedCopy b x).bitSteps ≤ BackendScalarBits.backendScalarUnit A.size := by
  have hw := Nat.size_le_size hx
  cases b
  · exact copy_price _ _ hw
  · exact sub_price _ zero x (by simp) hw

/-- Only the original input is serialized; no intermediate integer view is
re-encoded. Both positive and negative copies use the binary circuit. -/
def inputCell (b : Bool) (z : ℤ) : Run Cell :=
  let encoded := BinaryMultiplierAdapter.encodeInteger z
  let out := signedCopy b encoded.value
  ⟨out.value,encoded.bitSteps+out.bitSteps,8⟩

theorem inputCell_view (b : Bool) (z : ℤ) : view (inputCell b z).value = sign b*z := by
  change view (signedCopy b (BinaryMultiplierAdapter.encodeInteger z).value).value = _
  rw [signedCopy_view]
  exact congrArg (fun x => sign b*x) (BinaryMultiplierAdapter.encodeInteger_view z)

theorem inputCell_abs (b : Bool) (z : ℤ) : (view (inputCell b z).value).natAbs = z.natAbs := by
  change (view (signedCopy b (BinaryMultiplierAdapter.encodeInteger z).value).value).natAbs = _
  rw [signedCopy_abs]
  exact congrArg Int.natAbs (BinaryMultiplierAdapter.encodeInteger_view z)

def inputUnit (A : ℕ) : ℕ := 10*(A.size+1)^2+BackendScalarBits.backendScalarUnit A.size

theorem inputCell_bits (A : ℕ) (b : Bool) (z : ℤ) (hz : z.natAbs ≤ A) :
    (inputCell b z).bitSteps ≤ inputUnit A := by
  have he := BinaryMultiplierAdapter.encodeInteger_cost z
  have hs := signedCopy_bits A b (BinaryMultiplierAdapter.encodeInteger z).value
    (by simpa only [BinaryMultiplierAdapter.encodeInteger_view,view] using hz)
  have hw := Nat.size_le_size hz
  have hm : 10*(z.natAbs.size+1)^2 ≤ 10*(A.size+1)^2 := by gcongr
  simp only [inputCell,inputUnit]
  omega

abbrev Source (n C : ℕ) := StoredGroupedCompletion.Source n C ℤ

def datum {n C : ℕ} (X : Source n C) (p k : Key n) : Run (Vector Cell C) :=
  let pos := locate p k
  let index : Fin (3^n) := ⟨pos.value.index,locate_lt p k⟩
  let rows := tabulate X (fun c => inputCell pos.value.negative ((X.get c).get index))
  ⟨rows.value,pos.bitSteps+rows.bitSteps,pos.control+rows.control+8⟩

theorem datum_view {n C : ℕ} (X : Source n C) (p k : Key n) (c : Fin C) :
    view ((datum X p k).value.get c) = data p.get (StoredGroupedCompletion.readSource X c) (support k) := by
  have hi : (⟨(locate p k).value.index,locate_lt p k⟩ : Fin (3^n)) =
      StoredGroupedCompletion.rawIndex n (word p.get (support k)) :=
    Fin.ext ((locate_index p k).trans (GroupedCoordinates.coordinates_index p k))
  simp only [datum,tabulate_get,inputCell_view,hi,locate_negative,GroupedCoordinates.coordinates_sign,
    data,StoredGroupedCompletion.readSource]

theorem datum_abs {n C : ℕ} (A : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) (p k : Key n) (c : Fin C) :
    (view ((datum X p k).value.get c)).natAbs ≤ A := by
  simpa only [datum,tabulate_get,inputCell_abs] using hX c ⟨(locate p k).value.index,locate_lt p k⟩

theorem datum_bits {n C : ℕ} (A : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) (p k : Key n) :
    (datum X p k).bitSteps ≤ addressBudget n+C*inputUnit A := by
  have hp := locate_bits p k
  have hr := tabulate_bits X (fun c => inputCell (locate p k).value.negative
    ((X.get c).get ⟨(locate p k).value.index,locate_lt p k⟩))
    (fun c => inputCell_bits A _ _ (hX c _))
  simp only [datum]
  omega

theorem datum_control {n C : ℕ} (X : Source n C) (p k : Key n) :
    (datum X p k).control ≤ 28*n+40*C+26 := by
  have hr := tabulate_control X (fun c => inputCell (locate p k).value.negative
    ((X.get c).get ⟨(locate p k).value.index,locate_lt p k⟩)) (fun _ => le_refl 8)
  simp only [datum,locate_control]
  nlinarith

def prepare {n C : ℕ} (r : ℕ) (X : Source n C) : Run (Prepared n r C Cell) :=
  let keys := storeKeys n r
  let pairs := storePairs n
  let groups := tabulate pairs.value (fun p => tabulate keys.value (fun j => datum X (pairs.value.get p) (keys.value.get j)))
  ⟨⟨keys.value,pairs.value,groups.value⟩,groups.bitSteps,keys.work+pairs.work+groups.control+12⟩

@[simp] theorem prepare_keys {n C : ℕ} (r : ℕ) (X : Source n C) :
    (prepare r X).value.keys = keyVector n r := by simp [prepare]
@[simp] theorem prepare_pairs {n C : ℕ} (r : ℕ) (X : Source n C) :
    (prepare r X).value.pairs = pairKeys n := by simp [prepare]

theorem prepare_view {n C : ℕ} (r : ℕ) (X : Source n C) (p : Fin (2^n))
    (j : Fin (CappedSubsetList.count n r)) (c : Fin C) :
    view ((((prepare r X).value.groups.get p).get j).get c) =
      data ((pairKeys n).get p).get (StoredGroupedCompletion.readSource X c) (support ((keyVector n r).get j)) := by
  simp only [prepare,tabulate_get,storeKeys_value,storePairs_value,datum_view]

theorem prepare_abs {n C : ℕ} (A r : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) (p : Fin (2^n))
    (j : Fin (CappedSubsetList.count n r)) (c : Fin C) :
    (view ((((prepare r X).value.groups.get p).get j).get c)).natAbs ≤ A := by
  simp only [prepare,tabulate_get]
  exact datum_abs A X hX _ _ c

def preparationBits (n r C A : ℕ) : ℕ := 2^n*(CappedSubsetList.count n r*(addressBudget n+C*inputUnit A))
def preparationControl (n r C : ℕ) : ℕ :=
  keyBudget n r+keyBudget n n+2^n*(CappedSubsetList.count n r*(28*n+40*C+58)+40)+22

theorem prepare_bits {n C : ℕ} (A r : ℕ) (X : Source n C)
    (hX : ∀ c w, ((X.get c).get w).natAbs ≤ A) :
    (prepare r X).bitSteps ≤ preparationBits n r C A := by
  apply tabulate_bits
  intro p
  apply tabulate_bits
  intro j
  exact datum_bits A X hX _ _

theorem prepare_control {n C : ℕ} (r : ℕ) (X : Source n C) :
    (prepare r X).control ≤ preparationControl n r C := by
  have hr (p : Fin (2^n)) := tabulate_control (storeKeys n r).value
    (fun j => datum X ((storePairs n).value.get p) ((storeKeys n r).value.get j))
    (fun j => datum_control X _ _)
  have hg := tabulate_control (storePairs n).value
    (fun p => tabulate (storeKeys n r).value (fun j => datum X ((storePairs n).value.get p) ((storeKeys n r).value.get j))) hr
  have hk := storeKeys_work n r
  have hp := storePairs_work n
  simp only [prepare,preparationControl]
  nlinarith

#print axioms tabulate_get
#print axioms tabulate_bits_eq
#print axioms tabulate_control_eq
#print axioms tabulate_bits
#print axioms tabulate_control
#print axioms mapArray_size
#print axioms mapArray_get
#print axioms mapArray_bits
#print axioms mapArray_control
#print axioms signedCopy_view
#print axioms signedCopy_abs
#print axioms signedCopy_bits
#print axioms inputCell_view
#print axioms inputCell_abs
#print axioms inputCell_bits
#print axioms datum_view
#print axioms datum_abs
#print axioms datum_bits
#print axioms datum_control
#print axioms prepare_keys
#print axioms prepare_pairs
#print axioms prepare_view
#print axioms prepare_abs
#print axioms prepare_bits
#print axioms prepare_control
end ThinMatrix.BinaryGroupedPreparation
