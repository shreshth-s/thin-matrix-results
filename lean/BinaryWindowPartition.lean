import WindowSelection
import BinaryGroupedPreparation

set_option autoImplicit false

/-! Window ownership and all component arrays are constructed from an actual
row-major ternary source. The owner is computed once per raw word, shared by
all coefficient slots, and retained. Every component writes every slot,
including zeros. Binary copies and indexed-register control are priced
separately; the latter has not been compiled to binary machine operations. -/
namespace ThinMatrix.BinaryWindowPartition
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open GroupedPreparation (ofStoredFn ofStoredFn_eq)
open CyclicLightWindow
open scoped BigOperators

abbrev Source (k C : ℕ) := Vector (Vector Cell C) (3^(2*k))

def halfIndex {k : ℕ} (normal : Bool) (i : Fin k) : Fin (2*k) :=
  ⟨if normal then i.val else k+i.val,by split <;> omega⟩

def bits {k : ℕ} (normal : Bool) (w : CroppedGroupedSuffix.Word (2*k)) : Fin k → Bool :=
  fun i => decide (w (halfIndex normal i)=2)

def sourceValue {k C : ℕ} (X : Source k C) (w : CroppedGroupedSuffix.Word (2*k)) (c : Fin C) : ℤ :=
  view ((X.get (StoredGroupedCompletion.rawIndex (2*k) w)).get c)

def InputBound {k C : ℕ} (X : Source k C) (A : ℕ) : Prop :=
  ∀ i c, (view ((X.get i).get c)).natAbs≤A

def assign {k : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (index : ℕ) : Run (Option (Fin k)) :=
  let word := WindowSelection.decode (2*k) index
  let rareBits := Vector.ofFn (bits normal word.value.get)
  let chosen := WindowSelection.choose ell r rareBits
  ⟨chosen.value,0,word.work+chosen.work+8*k+6⟩

def assignBudget (k ell : ℕ) : ℕ := (2*k)*(6*(2*k)+16)+2+WindowSelection.budget k ell+8*k+6

theorem assign_value {k : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (i : Fin (3^(2*k))) :
    (assign (k:=k) ell r normal i.val).value =
      if h : count (bits normal ((StoredGroupedCompletion.rawIndex (2*k)).symm i))≤r then
        some (first ell r (bits normal ((StoredGroupedCompletion.rawIndex (2*k)).symm i)) h) else none := by
  have hf (f : Fin k → Bool) : (Vector.ofFn f).get=f := by funext j; simp
  simp only [assign,WindowSelection.choose_value,hf,WindowSelection.decode_index]

theorem assign_control {k : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (i : ℕ) :
    (assign (k:=k) ell r normal i).control≤assignBudget k ell := by
  have hd := WindowSelection.decode_work (2*k) i
  have hs := WindowSelection.choose_work ell r (Vector.ofFn (bits normal (WindowSelection.decode (2*k) i).value.get))
  simp only [assign,assignBudget]
  omega

def copyRow {k C : ℕ} (s : Fin k) (owner : Option (Fin k)) (row : Vector Cell C) : Run (Vector Cell C) :=
  let copied := tabulate row (fun c =>
    if owner=some s then let out := copy (row.get c); (⟨out.value,out.bitSteps,4⟩ : Run Cell)
    else ⟨zero,0,2⟩)
  ⟨copied.value,copied.bitSteps,copied.control+4⟩

theorem copyRow_get {k C : ℕ} (s : Fin k) (owner : Option (Fin k)) (row : Vector Cell C) (c : Fin C) :
    view ((copyRow s owner row).value.get c) = if owner=some s then view (row.get c) else 0 := by
  simp only [copyRow,tabulate_get]
  split <;> simp_all

theorem copyRow_bits {k C : ℕ} (s : Fin k) (owner : Option (Fin k)) (row : Vector Cell C)
    (A : ℕ) (ha : ∀ c, (view (row.get c)).natAbs≤A) :
    (copyRow s owner row).bitSteps ≤ C*BackendScalarBits.backendScalarUnit A.size := by
  apply tabulate_bits
  intro c
  split
  · exact copy_price A.size (row.get c) (Nat.size_le_size (ha c))
  · exact Nat.zero_le _

theorem copyRow_control {k C : ℕ} (s : Fin k) (owner : Option (Fin k)) (row : Vector Cell C) :
    (copyRow s owner row).control ≤ 36*C+12 := by
  have h := tabulate_control row (fun c =>
    if owner=some s then let out := copy (row.get c); (⟨out.value,out.bitSteps,4⟩ : Run Cell)
    else ⟨zero,0,2⟩) (W:=4) (by intro c; split <;> simp)
  simp only [copyRow]
  nlinarith

structure Prepared (k C : ℕ) where
  owners : Vector (Option (Fin k)) (3^(2*k))
  components : Vector (Source k C) k

def buildComponent {k C : ℕ} (s : Fin k) (owners : Vector (Option (Fin k)) (3^(2*k)))
    (X : Source k C) : Run (Source k C) :=
  tabulate X (fun i => copyRow s (owners.get i) (X.get i))

def execute {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C) : Run (Prepared k C) :=
  let owners := tabulate X (fun i => assign (k:=k) ell r normal i.val)
  let keys := Vector.ofFn (fun s : Fin k => s)
  let parts := tabulate keys (fun s => buildComponent s owners.value X)
  ⟨⟨owners.value,parts.value⟩,owners.bitSteps+parts.bitSteps,
    owners.control+parts.control+4*k+8⟩

theorem execute_get {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C)
    (s : Fin k) (w : CroppedGroupedSuffix.Word (2*k)) (c : Fin C) :
    sourceValue ((execute ell r normal X).value.components.get s) w c =
      component ell r (bits normal w) s (sourceValue X w c) := by
  simp only [execute,sourceValue,tabulate_get,buildComponent,copyRow_get,assign_value,Equiv.symm_apply_apply]
  by_cases h : count (bits normal w)≤r
  · simp only [h,↓reduceDIte,Option.some.injEq,component]
    simp only [eq_comm]
  · simp [h,component]

theorem reconstruct {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C)
    (w : CroppedGroupedSuffix.Word (2*k)) (c : Fin C) :
    (∑ s, sourceValue ((execute ell r normal X).value.components.get s) w c) =
      if count (bits normal w)≤r then sourceValue X w c else 0 := by
  simp_rw [execute_get]
  exact component_sum _ _ _ _

theorem window_supported {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C)
    (s : Fin k) (w : CroppedGroupedSuffix.Word (2*k)) (c : Fin C)
    (h : r*ell/k<weight ell (bits normal w) s) :
    sourceValue ((execute ell r normal X).value.components.get s) w c=0 := by
  rw [execute_get]
  exact component_zero _ _ _ _ _ h

/-- This is the contraction interface used by subsequent prefix/suffix
encoders. It retains all window components and every coefficient column. -/
theorem transform_reconstruction {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C)
    (K : CroppedGroupedSuffix.Word (2*k) → ℤ) (c : Fin C) :
    (∑ s, ∑ w, K w*sourceValue ((execute ell r normal X).value.components.get s) w c) =
      ∑ w, K w*(if count (bits normal w)≤r then sourceValue X w c else 0) := by
  simp_rw [execute_get]
  exact contraction_sum _ _ _ _ _

def bitBudget (k C A : ℕ) : ℕ := k*(3^(2*k))*(C*BackendScalarBits.backendScalarUnit A.size)
def controlBudget (k C ell : ℕ) : ℕ :=
  (3^(2*k))*(assignBudget k ell+32)+8+k*((3^(2*k))*(36*C+44)+40)+4*k+16

theorem execute_bits {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C)
    (A : ℕ) (ha : InputBound X A) : (execute ell r normal X).bitSteps ≤ bitBudget k C A := by
  have ho := tabulate_bits X (fun i => assign (k:=k) ell r normal i.val) (W:=0) (by intro i; rfl)
  have hb (s : Fin k) := tabulate_bits X (fun i => copyRow s
    ((tabulate X (fun i => assign (k:=k) ell r normal i.val)).value.get i) (X.get i))
    (fun i => copyRow_bits _ _ _ A (ha i))
  have hp := tabulate_bits (Vector.ofFn (fun s : Fin k => s))
    (fun s => buildComponent s (tabulate X (fun i => assign (k:=k) ell r normal i.val)).value X) hb
  simp only [execute,bitBudget]
  nlinarith

theorem execute_control {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C) :
    (execute ell r normal X).control ≤ controlBudget k C ell := by
  have ho := tabulate_control X (fun i => assign (k:=k) ell r normal i.val) (fun i => assign_control ell r normal i.val)
  have hb (s : Fin k) := tabulate_control X (fun i => copyRow s
    ((tabulate X (fun i => assign (k:=k) ell r normal i.val)).value.get i) (X.get i))
    (fun i => copyRow_control _ _ _)
  have hp := tabulate_control (Vector.ofFn (fun s : Fin k => s))
    (fun s => buildComponent s (tabulate X (fun i => assign (k:=k) ell r normal i.val)).value X) hb
  simp only [execute,controlBudget]
  nlinarith

theorem coefficient_cells {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C) :
    (((execute ell r normal X).value.components.toList.map fun part =>
      (part.toList.map fun row => row.toList.length).sum).sum) = k*(3^(2*k))*C := by
  simp only [Vector.length_toList,List.map_const',List.sum_replicate,smul_eq_mul]
  ring


theorem execute_magnitude {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C)
    (A : ℕ) (ha : InputBound X A) (s : Fin k) :
    InputBound ((execute ell r normal X).value.components.get s) A := by
  intro i c
  have h := execute_get ell r normal X s ((StoredGroupedCompletion.rawIndex (2*k)).symm i) c
  simp only [sourceValue,Equiv.apply_symm_apply] at h
  rw [h]
  unfold component
  split
  · split
    · exact ha i c
    · simp
  · simp

/-- The shifted ordinary forms consume each disjoint component. This bridge
is valid before choosing which coordinates to transform as a prefix. -/
theorem ordinary_reconstruction {k C : ℕ} [NeZero k] (ell r : ℕ) (normal : Bool) (X : Source k C)
    (p : WalshEmbedding.Cube (2*k)) (active : Finset (Fin (2*k))) (c : Fin C) :
    (∑ s, CroppedGroupedSuffix.transform p active
      (fun w => sourceValue ((execute ell r normal X).value.components.get s) w c)) =
      CroppedGroupedSuffix.transform p active
        (fun w => if count (bits normal w)≤r then sourceValue X w c else 0) :=
  transform_reconstruction ell r normal X (CroppedGroupedSuffix.kernel p active) c

/-- Use the larger channel count, choosing the normal half on a tie. The
remaining rare budget and the side are computed once for the whole source. -/
def prepare {k C : ℕ} [NeZero k] (ell cap normalChannels oppositeChannels : ℕ) (X : Source k C) :
    Run (Prepared k C) :=
  let side := decide (oppositeChannels≤normalChannels)
  let rareBudget := cap-max normalChannels oppositeChannels
  let out := execute ell rareBudget side X
  ⟨out.value,out.bitSteps,out.control+8⟩

theorem prepare_side (normalChannels oppositeChannels : ℕ) :
    (if decide (oppositeChannels≤normalChannels) then normalChannels else oppositeChannels) =
      max normalChannels oppositeChannels := by
  by_cases h : oppositeChannels≤normalChannels
  · simp [h]
  · simp [h,Nat.max_eq_right (by omega : normalChannels≤oppositeChannels)]

theorem correctness_and_costs {k C : ℕ} [NeZero k]
    (ell cap normalChannels oppositeChannels A : ℕ) (X : Source k C) (ha : InputBound X A) :
    let r := cap-max normalChannels oppositeChannels
    let normal := decide (oppositeChannels≤normalChannels)
    let out := prepare ell cap normalChannels oppositeChannels X
    (∀ w c, (∑ s, sourceValue (out.value.components.get s) w c) =
      if count (bits normal w)≤r then sourceValue X w c else 0) ∧
    (∀ s w c, r*ell/k<weight ell (bits normal w) s → sourceValue (out.value.components.get s) w c=0) ∧
    (∀ s, InputBound (out.value.components.get s) A) ∧
    out.bitSteps≤bitBudget k C A ∧ out.control≤controlBudget k C ell+8 := by
  dsimp only [prepare]
  exact ⟨reconstruct ell _ _ X,window_supported ell _ _ X,execute_magnitude ell _ _ X A ha,
    execute_bits ell _ _ X A ha,Nat.add_le_add_right (execute_control ell _ _ X) 8⟩

/-- With no remaining positions there is one component, the copied source.
No division or first-window search is performed in this boundary case. -/
def executeZero {C : ℕ} (X : Source 0 C) : Run (Vector (Source 0 C) 1) :=
  let out := tabulate X (fun i => copyRow (0 : Fin 1) (some 0) (X.get i))
  ⟨Vector.singleton out.value,out.bitSteps,out.control+4⟩

theorem executeZero_get {C : ℕ} (X : Source 0 C) (w : CroppedGroupedSuffix.Word 0) (c : Fin C) :
    sourceValue ((executeZero X).value.get 0) w c = sourceValue X w c := by
  change view (((tabulate X (fun i => copyRow (0 : Fin 1) (some 0) (X.get i))).value.get
    (StoredGroupedCompletion.rawIndex 0 w)).get c) = _
  rw [tabulate_get,copyRow_get]
  rfl

theorem executeZero_bits {C : ℕ} (X : Source 0 C) (A : ℕ) (ha : InputBound X A) :
    (executeZero X).bitSteps≤C*BackendScalarBits.backendScalarUnit A.size := by
  have h := tabulate_bits X (fun i => copyRow (0 : Fin 1) (some 0) (X.get i))
    (fun i => copyRow_bits _ _ _ A (ha i))
  simpa only [executeZero,Nat.mul_zero,pow_zero,Nat.one_mul] using h

theorem executeZero_control {C : ℕ} (X : Source 0 C) : (executeZero X).control≤36*C+56 := by
  have h := tabulate_control X (fun i => copyRow (0 : Fin 1) (some 0) (X.get i))
    (fun i => copyRow_control _ _ _)
  simpa only [executeZero,Nat.mul_zero,pow_zero,Nat.one_mul,Nat.add_assoc] using Nat.add_le_add_right h 4

#print axioms assign_value
#print axioms assign_control
#print axioms copyRow_get
#print axioms copyRow_bits
#print axioms copyRow_control
#print axioms execute_get
#print axioms reconstruct
#print axioms window_supported
#print axioms transform_reconstruction
#print axioms execute_bits
#print axioms execute_control
#print axioms coefficient_cells
#print axioms execute_magnitude
#print axioms ordinary_reconstruction
#print axioms prepare_side
#print axioms correctness_and_costs
#print axioms executeZero_get
#print axioms executeZero_bits
#print axioms executeZero_control
end ThinMatrix.BinaryWindowPartition
