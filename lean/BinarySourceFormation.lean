import BackendScalarBits
import SourceFormation
import BinaryCell
import AdaptiveBitBounds

/-!
# Binary materialization of the direct Walsh source

Runtime coefficient cells contain canonical signed Boolean lists. Walsh
signs, accumulation, and normal weights act on those lists directly.
Semantic integers occur only in projections and proofs. Public finite
indices and the stored Boolean environment use the same control model as
SourceFormation; array-to-machine addressing is a separate refinement.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

namespace ThinMatrix.BinarySourceCells
open IntegerArithmetic BackendScalarBits

/-- Runtime payload is a signed binary list; the remaining field is erased. -/
abbrev Cell := BinaryCell.Cell

def Cell.view (a : Cell) : ℤ := signedValue a.bits

abbrev Result (α : Type) := BinaryCell.Result α

def zero : Cell := ⟨⟨false,[]⟩,rfl⟩
def one : Cell := ⟨⟨false,[true]⟩,rfl⟩

@[simp] theorem zero_view : zero.view = 0 := rfl
@[simp] theorem one_view : one.view = 1 := rfl
@[simp] theorem zero_width : zero.bits.magnitude.length = 0 := rfl
@[simp] theorem one_width : one.bits.magnitude.length = 1 := rfl

def run (op : ScalarInstruction) : Result Cell :=
  let child := execute op
  ⟨⟨child.1,by rw [execute_canonical_width,execute_correct]⟩,child.2⟩

@[simp] theorem run_view (op : ScalarInstruction) :
    (run op).value.view = instructionValue op := execute_correct op

theorem run_bitSteps (B : ℕ) (op : ScalarInstruction) (h : op.Fits B) :
    (run op).bitSteps ≤ 200*(B+1)^2 := by
  exact (execute_price B op h).trans_eq (by unfold scalarUnit; ring)

def add (a b : Cell) : Result Cell := run (.add a.bits b.bits)
def neg (a : Cell) : Result Cell := run (.subtract zero.bits a.bits)
def double (a : Cell) : Result Cell := add a a

@[simp] theorem add_view (a b : Cell) : (add a b).value.view = a.view+b.view := by
  exact run_view _

@[simp] theorem neg_view (a : Cell) : (neg a).value.view = -a.view := by
  simpa [neg,instructionValue,Cell.view,zero,signedValue,value] using run_view (.subtract zero.bits a.bits)

@[simp] theorem double_view (a : Cell) : (double a).value.view = 2*a.view := by
  rw [double,add_view]
  ring

theorem add_bitSteps (B : ℕ) (a b : Cell)
    (ha : a.bits.magnitude.length ≤ B) (hb : b.bits.magnitude.length ≤ B) :
    (add a b).bitSteps ≤ 200*(B+1)^2 := run_bitSteps B _ ⟨ha,hb⟩

theorem neg_bitSteps (B : ℕ) (a : Cell) (ha : a.bits.magnitude.length ≤ B) :
    (neg a).bitSteps ≤ 200*(B+1)^2 := run_bitSteps B _ ⟨Nat.zero_le _,ha⟩

theorem double_bitSteps (B : ℕ) (a : Cell) (ha : a.bits.magnitude.length ≤ B) :
    (double a).bitSteps ≤ 200*(B+1)^2 := add_bitSteps B a a ha ha

/-- Public natural control repeats actual binary addition. The computed
cell is passed directly to the next stage and is never re-encoded. -/
def shiftPower : ℕ → Cell → Result Cell
  | 0, a => ⟨a,0⟩
  | r+1, a =>
      let child := shiftPower r a
      let next := double child.value
      ⟨next.value,child.bitSteps+next.bitSteps⟩

@[simp] theorem shiftPower_view (r : ℕ) (a : Cell) :
    (shiftPower r a).value.view = (2:ℤ)^r*a.view := by
  induction r with
  | zero => simp [shiftPower]
  | succ r ih =>
      simp only [shiftPower,double_view,ih,pow_succ]
      ring

/-- Common physical width of every partial shift is an explicit premise. -/
theorem shiftPower_bitSteps_uniform (r B : ℕ) (a : Cell)
    (h : ∀ j < r, (shiftPower j a).value.bits.magnitude.length ≤ B) :
    (shiftPower r a).bitSteps ≤ r*(200*(B+1)^2) := by
  induction r with
  | zero => simp [shiftPower]
  | succ r ih =>
      have hc := ih (fun j hj => h j (by omega))
      have hd := double_bitSteps B (shiftPower r a).value (h r (by omega))
      dsimp only [shiftPower]
      rw [Nat.add_mul,Nat.one_mul]
      omega

theorem shift_size {x : ℤ} {A r m : ℕ}
    (hx : |x| ≤ (A:ℤ)) (hr : r ≤ m) :
    ((2:ℤ)^r*x).natAbs.size ≤ A.log2+m+1 := by
  have hx' : x.natAbs ≤ A := by
    rw [← Int.natCast_natAbs] at hx
    exact Int.ofNat_le.mp hx
  apply Nat.size_le.mpr
  simp only [Int.natAbs_mul,Int.natAbs_pow]
  change 2^r*x.natAbs < 2^(A.log2+m+1)
  calc
    2^r*x.natAbs ≤ 2^m*A :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hr) hx'
    _ < 2^m*2^(A.log2+1) :=
      Nat.mul_lt_mul_of_pos_left Nat.lt_log2_self (by positivity)
    _ = 2^(A.log2+m+1) := by
      rw [← Nat.pow_add]
      congr 1
      omega

/-- The original cap bounds every retained partial shift, including zero
and the final output. The width is logarithmic in the input magnitude. -/
theorem shiftPower_width (A r m : ℕ) (a : Cell)
    (ha : |a.view| ≤ (A:ℤ)) (hr : r ≤ m) :
    (shiftPower r a).value.bits.magnitude.length ≤ A.log2+m+1 := by
  rw [(shiftPower r a).value.canonical]
  change (shiftPower r a).value.view.natAbs.size ≤ _
  rw [shiftPower_view]
  exact shift_size ha hr

theorem shiftPower_bitSteps (A r m : ℕ) (a : Cell)
    (ha : |a.view| ≤ (A:ℤ)) (hr : r ≤ m) :
    (shiftPower r a).bitSteps ≤ r*(200*(A.log2+m+2)^2) := by
  have h := shiftPower_bitSteps_uniform r (A.log2+m+1) a (by
    intro j hj
    exact shiftPower_width A j m a ha (by omega))
  simpa only [Nat.add_assoc] using h

/-- A caller may substitute a larger common physical allowance. -/
theorem shiftPower_bitSteps_common (A r m B : ℕ) (a : Cell)
    (ha : |a.view| ≤ (A:ℤ)) (hr : r ≤ m) (hB : A.log2+m+1 ≤ B) :
    (shiftPower r a).bitSteps ≤ r*(200*(B+1)^2) := by
  apply shiftPower_bitSteps_uniform
  intro j hj
  exact (shiftPower_width A j m a ha (by omega)).trans hB

#print axioms run_view
#print axioms add_bitSteps
#print axioms neg_bitSteps
#print axioms double_bitSteps
#print axioms shiftPower_view
#print axioms shiftPower_bitSteps_uniform
#print axioms shiftPower_width
#print axioms shiftPower_bitSteps
#print axioms shiftPower_bitSteps_common
end ThinMatrix.BinarySourceCells

namespace ThinMatrix.BinaryWalshBounds
open IntegerArithmetic SourceFormation WalshEmbedding BackendScalarBits

/-- Every finite partial sum is charged using original occurrence terms. -/
theorem sum_natAbs_bound (xs : List ℤ) (A : ℕ)
    (hx : ∀ z ∈ xs, z.natAbs ≤ A) : (xs.sum).natAbs ≤ xs.length*A := by
  induction xs with
  | nil => simp
  | cons z xs ih =>
      have hz := hx z (by simp)
      have ht := ih (fun w hw => hx w (by simp [hw]))
      simp only [List.sum_cons, List.length_cons]
      exact (Int.natAbs_add_le _ _).trans (by nlinarith)

theorem sum_abs_bound (xs : List ℤ) (A : ℕ)
    (hx : ∀ z ∈ xs, |z| ≤ (A:ℤ)) : |xs.sum| ≤ (xs.length*A:ℕ) := by
  have hn : ∀ z ∈ xs, z.natAbs ≤ A := by
    intro z hz
    exact_mod_cast (show (z.natAbs:ℤ) ≤ (A:ℤ) by simpa only [Int.natCast_natAbs] using hx z hz)
  simpa only [Int.natCast_natAbs] using (show ((xs.sum).natAbs:ℤ) ≤ (xs.length*A:ℕ) by exact_mod_cast sum_natAbs_bound xs A hn)

theorem sublist_sum_natAbs_bound (xs ys : List ℤ) (A : ℕ)
    (hys : ys.Sublist xs) (hx : ∀ z ∈ xs, z.natAbs ≤ A) :
    ys.sum.natAbs ≤ xs.length*A := by
  exact (sum_natAbs_bound ys A (fun z hz => hx z (hys.subset hz))).trans
    (Nat.mul_le_mul_right A hys.length_le)

/-- The bit bound is logarithmic in the number of summands; repeated
occurrences are retained in the length bound. -/
theorem natAbs_size_of_le_power_mul (z : ℤ) (k A : ℕ)
    (hz : z.natAbs ≤ 2^k*A) : z.natAbs.size ≤ k+A.size := by
  apply Nat.size_le.mpr
  have hA : A < 2^A.size := Nat.size_le.mp (le_refl A.size)
  calc
    z.natAbs ≤ 2^k*A := hz
    _ < 2^k*2^A.size := Nat.mul_lt_mul_of_pos_left hA (by positivity)
    _ = 2^(k+A.size) := (pow_add ..).symm

theorem sum_size_bound (xs : List ℤ) (k A : ℕ) (hlen : xs.length ≤ 2^k)
    (hx : ∀ z ∈ xs, z.natAbs ≤ A) : xs.sum.natAbs.size ≤ k+A.size := by
  exact natAbs_size_of_le_power_mul _ k A
    ((sum_natAbs_bound xs A hx).trans (Nat.mul_le_mul_right A hlen))

theorem walshTerm_natAbs_bound {k : ℕ} (read : Cube k → Program ℤ)
    (frequency outer : Cube k) (A : ℕ) (hr : (read outer).value.natAbs≤A) :
    (walshTerm read frequency outer).value.natAbs≤A := by
  unfold walshTerm
  split <;> simpa using hr

theorem walshProgram_natAbs_bound {k : ℕ} (read : Cube k → Program ℤ)
    (frequency : Cube k) (A : ℕ) (hr : ∀ outer, (read outer).value.natAbs≤A) :
    (walshProgram read frequency).value.natAbs≤2^k*A := by
  let terms := (cubeList k).map (fun outer => (walshTerm read frequency outer).value)
  have ht : ∀ z ∈ terms, z.natAbs≤A := by
    intro z hz
    obtain ⟨outer, _, rfl⟩ := List.mem_map.mp hz
    exact walshTerm_natAbs_bound read frequency outer A (hr outer)
  have h := sum_natAbs_bound terms A ht
  simpa [terms,walshProgram,List.map_map,Function.comp_def,cubeList_length] using h

theorem walshProgram_size_bound {k : ℕ} (read : Cube k → Program ℤ)
    (frequency : Cube k) (A : ℕ) (hr : ∀ outer, (read outer).value.natAbs≤A) :
    (walshProgram read frequency).value.natAbs.size≤k+A.size :=
  natAbs_size_of_le_power_mul _ k A (walshProgram_natAbs_bound read frequency A hr)

theorem weighted_natAbs_bound (z : ℤ) (k h A : ℕ) (hz : z.natAbs≤2^k*A) :
    ((2:ℤ)^h*z).natAbs≤2^(k+h)*A := by
  rw [Int.natAbs_mul,Int.natAbs_pow]
  norm_num only [Int.natAbs_ofNat']
  calc
    2^h*z.natAbs ≤ 2^h*(2^k*A) := Nat.mul_le_mul_left _ hz
    _ = 2^(k+h)*A := by rw [← mul_assoc,←pow_add,Nat.add_comm h k]

theorem weighted_size_bound (z : ℤ) (k h m A : ℕ)
    (hh : h ≤ m) (hz : z.natAbs ≤ 2^k*A) :
    ((2:ℤ)^h*z).natAbs.size≤k+m+A.size := by
  exact (natAbs_size_of_le_power_mul _ (k+h) A (weighted_natAbs_bound z k h A hz)).trans (by omega)

/-- Actual binary accumulation: one canonicalized binary add per stored
term, with the child result reused. -/
def sumBinary : List SignedBits → SignedBits × ℕ
  | [] => (⟨false,[]⟩,1)
  | x::xs =>
      let child := sumBinary xs
      let output := execute (.add x child.1)
      (output.1,child.2+output.2+1)

theorem sumBinary_value (xs : List SignedBits) :
    signedValue (sumBinary xs).1 = (xs.map signedValue).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumBinary,execute_correct,instructionValue,ih,List.map_cons,List.sum_cons]

theorem sumBinary_canonical (xs : List SignedBits) :
    (sumBinary xs).1.magnitude.length = (signedValue (sumBinary xs).1).natAbs.size := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      change (execute (.add x (sumBinary xs).1)).1.magnitude.length =
        (signedValue (execute (.add x (sumBinary xs).1)).1).natAbs.size
      rw [execute_canonical_width,execute_correct]

/-- Every recursive partial sum has at most the original total number of
terms; the cost uses their logarithmic canonical width throughout. -/
theorem sumBinary_cost (xs : List SignedBits) (k A : ℕ)
    (hlen : xs.length≤2^k)
    (hcanon : ∀ x∈xs, x.magnitude.length=(signedValue x).natAbs.size)
    (hx : ∀ x∈xs, (signedValue x).natAbs≤A) :
    (sumBinary xs).2≤1+xs.length*(2*scalarUnit (k+A.size)+1) := by
  induction xs with
  | nil => simp [sumBinary]
  | cons x xs ih =>
      have hlen' : xs.length≤2^k := by simp only [List.length_cons] at hlen; omega
      have hcanon' : ∀ y∈xs, y.magnitude.length=(signedValue y).natAbs.size :=
        fun y hy => hcanon y (by simp [hy])
      have hx' : ∀ y∈xs, (signedValue y).natAbs≤A := fun y hy => hx y (by simp [hy])
      have hi := ih hlen' hcanon' hx'
      have hxlen : x.magnitude.length≤k+A.size := by
        rw [hcanon x (by simp)]
        have hn := Nat.size_le_size (hx x (by simp))
        omega
      have hchild : (sumBinary xs).1.magnitude.length≤k+A.size := by
        rw [sumBinary_canonical,sumBinary_value]
        apply sum_size_bound _ k A
        · simpa using hlen'
        · intro z hz
          obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
          exact hx' y hy
      have hc := execute_price (k+A.size) (.add x (sumBinary xs).1) ⟨hxlen,hchild⟩
      simp only [sumBinary,List.length_cons]
      nlinarith

#print axioms sum_abs_bound
#print axioms walshProgram_size_bound
#print axioms weighted_size_bound
#print axioms sumBinary_cost
end ThinMatrix.BinaryWalshBounds

namespace ThinMatrix.BinarySourceStorage
open SourceFormation
open scoped BigOperators

variable {α β γ : Type*}

/-- Semantic projection preserves the already executed operation counter. -/
def programMap (g : α → β) (p : Program α) : Program β :=
  { value := g p.value, operations := p.operations }

@[simp] theorem programMap_value (g : α → β) (p : Program α) :
    (programMap g p).value = g p.value := rfl

@[simp] theorem programMap_operations (g : α → β) (p : Program α) :
    (programMap g p).operations = p.operations := rfl

theorem program_ext (p r : Program α) (hv : p.value = r.value)
    (hc : p.operations = r.operations) : p = r := by
  cases p
  cases r
  simp_all

/-- Projection recursively visits the actual stored backing vectors. -/
def mapTable (g : α → β) (radix : ℕ) : (n : ℕ) → Table α radix n → Table β radix n
  | 0, data => g data
  | n+1, data => data.map (mapTable g radix n)

@[simp] theorem tableRead_map (g : α → β) (radix n : ℕ)
    (data : Table α radix n) (key : Fin n → Fin radix) :
    tableRead radix n (mapTable g radix n data) key = g (tableRead radix n data key) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tableRead, mapTable, Vector.get_map, ih]

/-- Extensionality of radix trees by their actual leaf reads. -/
theorem table_ext (radix n : ℕ) (data other : Table α radix n)
    (h : ∀ key, tableRead radix n data key = tableRead radix n other key) : data = other := by
  induction n with
  | zero => exact h (fun i => Fin.elim0 i)
  | succ n ih =>
      apply Vector.ext
      intro a ha
      apply ih
      intro rest
      simpa only [tableRead, Fin.cons_zero, Fin.cons_succ, Vector.get_eq_getElem] using h (Fin.cons ⟨a, ha⟩ rest)

/-- Value naturality does not require the two leaf implementations to have the
same operation costs. This is the useful statement for binary arithmetic. -/
theorem tableBuild_map_value (g : α → β) (radix n : ℕ)
    (f : (Fin n → Fin radix) → Program α)
    (projected : (Fin n → Fin radix) → Program β)
    (hf : ∀ key, (projected key).value = g (f key).value) :
    (tableBuild radix n projected).value = mapTable g radix n (tableBuild radix n f).value := by
  apply table_ext radix n
  intro key
  rw [tableRead_map, tableRead_build, tableRead_build]
  exact hf key

@[simp] theorem tableBuild_map_operations (g : α → β) (radix n : ℕ)
    (f : (Fin n → Fin radix) → Program α) :
    (tableBuild radix n (fun key => programMap g (f key))).operations =
      (tableBuild radix n f).operations := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tableBuild, Vector.get_ofFn]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact ih (fun rest => f (Fin.cons a rest))

theorem tableBuild_map (g : α → β) (radix n : ℕ)
    (f : (Fin n → Fin radix) → Program α) :
    tableBuild radix n (fun key => programMap g (f key)) =
      programMap (mapTable g radix n) (tableBuild radix n f) := by
  have hv := tableBuild_map_value g radix n f (fun key => programMap g (f key)) (fun _ => rfl)
  have hc := tableBuild_map_operations g radix n f
  exact program_ext _ _ hv hc

theorem vectorBuild_map_value (g : α → β) (n : ℕ) (f : Fin n → Program α)
    (projected : Fin n → Program β)
    (hf : ∀ i, (projected i).value = g (f i).value) :
    (vectorBuild n projected).value = (vectorBuild n f).value.map g := by
  apply Vector.ext
  intro i hi
  simpa [vectorBuild] using hf ⟨i, hi⟩

theorem vectorBuild_map (g : α → β) (n : ℕ) (f : Fin n → Program α) :
    vectorBuild n (fun i => programMap g (f i)) =
      programMap (fun v => v.map g) (vectorBuild n f) := by
  have hv := vectorBuild_map_value g n f (fun i => programMap g (f i)) (fun _ => rfl)
  have hc : (vectorBuild n (fun i => programMap g (f i))).operations =
      (vectorBuild n f).operations := by
    simp only [vectorBuild, Vector.get_ofFn, programMap]
  exact program_ext _ _ hv hc

abbrev RawStoreOf (α : Type*) (L q : ℕ) := Table (Table (Vector α q) 3 L) 4 L

def mapRaw {L q : ℕ} (g : α → β) (store : RawStoreOf α L q) : RawStoreOf β L q :=
  mapTable (mapTable (fun v => v.map g) 3 L) 4 L store

def readRawOf {L q : ℕ} (store : RawStoreOf α L q)
    (normal : Fin L → WalshEmbedding.NormalLetter)
    (opposite : Fin L → WalshEmbedding.OppositeLetter) (residue : Fin q) : α :=
  (tableRead 3 L (tableRead 4 L store (fun i => normalIndex (normal i)))
    (fun i => oppositeIndex (opposite i))).get residue

@[simp] theorem readRawOf_map {L q : ℕ} (g : α → β) (store : RawStoreOf α L q)
    (normal : Fin L → WalshEmbedding.NormalLetter)
    (opposite : Fin L → WalshEmbedding.OppositeLetter) (residue : Fin q) :
    readRawOf (mapRaw g store) normal opposite residue = g (readRawOf store normal opposite residue) := by
  simp only [readRawOf, mapRaw, tableRead_map, Vector.get_map]

def rawBuildOf {L q : ℕ}
    (f : (Fin L → WalshEmbedding.NormalLetter) →
      (Fin L → WalshEmbedding.OppositeLetter) → Program (Vector α q)) :
    Program (RawStoreOf α L q) :=
  tableBuild 4 L fun normal => tableBuild 3 L fun opposite =>
    f (fun i => indexNormal (normal i)) (fun i => indexOpposite (opposite i))

theorem rawBuildOf_map_value {L q : ℕ} (g : α → β)
    (f : (Fin L → WalshEmbedding.NormalLetter) →
      (Fin L → WalshEmbedding.OppositeLetter) → Program (Vector α q))
    (projected : (Fin L → WalshEmbedding.NormalLetter) →
      (Fin L → WalshEmbedding.OppositeLetter) → Program (Vector β q))
    (hf : ∀ normal opposite, (projected normal opposite).value =
      (f normal opposite).value.map g) :
    (rawBuildOf projected).value = mapRaw g (rawBuildOf f).value := by
  unfold rawBuildOf mapRaw
  apply tableBuild_map_value (mapTable (fun v : Vector α q => v.map g) 3 L) 4 L
  intro normal
  exact tableBuild_map_value (fun v : Vector α q => v.map g) 3 L _ _ (fun opposite => hf _ _)

@[simp] theorem readRawOf_build {L q : ℕ}
    (f : (Fin L → WalshEmbedding.NormalLetter) →
      (Fin L → WalshEmbedding.OppositeLetter) → Program (Vector α q))
    (normal : Fin L → WalshEmbedding.NormalLetter)
    (opposite : Fin L → WalshEmbedding.OppositeLetter) (residue : Fin q) :
    readRawOf (rawBuildOf f).value normal opposite residue =
      (f normal opposite).value.get residue := by
  unfold readRawOf rawBuildOf
  rw [tableRead_build, tableRead_build]
  simp only [indexNormal_normalIndex, indexOpposite_oppositeIndex]

@[simp] theorem normalIndex_indexNormal (i : Fin 4) : normalIndex (indexNormal i) = i := by
  fin_cases i <;> rfl

@[simp] theorem oppositeIndex_indexOpposite (i : Fin 3) : oppositeIndex (indexOpposite i) = i := by
  fin_cases i <;> rfl

/-- Leafwise equality proves equality of the actual stored nested vectors. -/
theorem rawStore_ext {L q : ℕ} (store other : RawStoreOf α L q)
    (h : ∀ normal opposite residue,
      readRawOf store normal opposite residue = readRawOf other normal opposite residue) :
    store = other := by
  apply table_ext 4 L
  intro normal
  apply table_ext 3 L
  intro opposite
  apply Vector.ext
  intro residue hr
  simpa only [readRawOf, normalIndex_indexNormal, oppositeIndex_indexOpposite,
    Vector.get_eq_getElem] using
    h (fun i => indexNormal (normal i)) (fun i => indexOpposite (opposite i)) ⟨residue, hr⟩

@[simp] theorem readRawOf_int {L q : ℕ} (store : RawStore L q)
    (normal : Fin L → WalshEmbedding.NormalLetter)
    (opposite : Fin L → WalshEmbedding.OppositeLetter) (residue : Fin q) :
    readRawOf store normal opposite residue = readRaw store normal opposite residue := rfl

#print axioms tableRead_map
#print axioms tableBuild_map
#print axioms vectorBuild_map
#print axioms rawBuildOf_map_value
#print axioms rawStore_ext
end ThinMatrix.BinarySourceStorage

namespace ThinMatrix.BinarySourceFormation
open SourceFormation WalshEmbedding IntegerArithmetic BackendScalarBits
open BinarySourceCells
open scoped BigOperators

abbrev BinaryLeftRead (L m k q : ℕ) :=
  Finset (Fin L) → Cube L → Cube k → Cube m → Cube m → Fin q → Program Cell
abbrev BinaryRightRead (L m k q : ℕ) :=
  Finset (Fin L) → Cube L → Cube m → Cube m → Cube k → Fin q → Program Cell

/-- Original Boolean coefficients enter as literal bits, with no Int encoding. -/
def ofBool (b : Bool) : Cell := if b then one else zero

@[simp] theorem ofBool_view (b : Bool) : (ofBool b).view = if b then 1 else 0 := by
  cases b <;> rfl

noncomputable def semantic {α : Type} (read : α → Program Cell) : α → Program ℤ :=
  fun a => ⟨(read a).value.view,(read a).operations⟩

noncomputable def semanticLeft {L m k q : ℕ} (read : BinaryLeftRead L m k q) :
    LeftRead L m k q := fun Q bits outer r s j =>
  ⟨(read Q bits outer r s j).value.view,(read Q bits outer r s j).operations⟩
noncomputable def semanticRight {L m k q : ℕ} (read : BinaryRightRead L m k q) :
    RightRead L m k q := fun Q bits r s outer j =>
  ⟨(read Q bits r s outer j).value.view,(read Q bits r s outer j).operations⟩

/-- Each input is read once and the signed output remains binary. -/
def walshTerm {k : ℕ} (read : Cube k → Program Cell) (frequency outer : Cube k) : Program Cell :=
  let input := read outer
  let output := if dotBits frequency outer then BinarySourceCells.neg input.value else ⟨input.value,0⟩
  ⟨output.value,input.operations+output.bitSteps+8*(k+1)⟩

@[simp] theorem walshTerm_view {k : ℕ} (read : Cube k → Program Cell)
    (frequency outer : Cube k) :
    (walshTerm read frequency outer).value.view =
      (SourceFormation.walshTerm (semantic read) frequency outer).value := by
  unfold walshTerm SourceFormation.walshTerm semantic
  dsimp only
  split <;> simp

/-- Store every term once, then accumulate canonical signed cells. -/
def walshProgram {k : ℕ} (read : Cube k → Program Cell) (frequency : Cube k) : Program Cell :=
  let terms := (cubeList k).map (walshTerm read frequency)
  let total := BinaryWalshBounds.sumBinary (terms.map (fun term => term.value.bits))
  { value := ⟨total.1,BinaryWalshBounds.sumBinary_canonical _⟩
    operations := (terms.map (fun term => term.operations)).sum+total.2+8*terms.length }

@[simp] theorem walshProgram_view {k : ℕ} (read : Cube k → Program Cell) (frequency : Cube k) :
    (walshProgram read frequency).value.view =
      (SourceFormation.walshProgram (semantic read) frequency).value := by
  simp only [walshProgram,Cell.view,BinaryWalshBounds.sumBinary_value,List.map_map,
    Function.comp_def,SourceFormation.walshProgram]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact walshTerm_view read frequency a

theorem walshProgram_natAbs_bound {k : ℕ} (read : Cube k → Program Cell)
    (frequency : Cube k) (A : ℕ) (hr : ∀ outer, (read outer).value.view.natAbs ≤ A) :
    (walshProgram read frequency).value.view.natAbs ≤ 2^k*A := by
  rw [walshProgram_view]
  exact BinaryWalshBounds.walshProgram_natAbs_bound _ frequency A hr

def formationWidth (L k A : ℕ) : ℕ := L+k+A.size

theorem shift_bitSteps (r L k A : ℕ) (a : Cell) (hr : r ≤ L)
    (ha : a.view.natAbs ≤ 2^k*A) :
    (shiftPower r a).bitSteps ≤ L*(200*(formationWidth L k A+1)^2) := by
  apply (shiftPower_bitSteps_uniform r (formationWidth L k A) a ?_).trans
    (Nat.mul_le_mul_right _ hr)
  intro j hj
  rw [(shiftPower j a).value.canonical]
  change ((shiftPower j a).value.view).natAbs.size ≤ _
  rw [shiftPower_view]
  simpa only [formationWidth, Nat.add_comm L k] using
    BinaryWalshBounds.weighted_size_bound a.view k j L A (by omega) ha

theorem normalWeight_le {L m k : ℕ} (env : Environment L m k)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    (metadata env normal opposite).normalWeight ≤ L := by
  unfold metadata
  dsimp only
  unfold ones
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- Run indices are unsigned public control values. The equality below
avoids native signed arithmetic in the executable branch test. -/
def leftWordProgram {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : Program (Vector Cell q) :=
  let entry := metadata env normal opposite
  let coefficients := if entry.good && decide (entry.oppositeWeight+m=entry.normalWeight+run.val) then
    vectorBuild q fun residue =>
      let total := walshProgram
        (fun outer => read entry.support (asCube entry.outer) outer
          (asCube entry.gammaNormal) (asCube entry.gammaOpposite) residue)
        (asCube entry.frequency)
      let weighted := shiftPower entry.normalWeight total.value
      ⟨weighted.value,total.operations+weighted.bitSteps⟩
  else vectorBuild q fun _ => ⟨zero,1⟩
  ⟨coefficients.value,coefficients.operations+metadataCost L m k⟩

def rightWordProgram {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : Program (Vector Cell q) :=
  let entry := metadata env normal opposite
  let coefficients := if entry.good && decide (entry.normalWeight+m=entry.oppositeWeight+run.val) then
    vectorBuild q fun residue =>
      let total := walshProgram
        (fun outer => read entry.support (asCube entry.outer)
          (asCube entry.gammaOpposite) (asCube entry.gammaNormal) outer residue)
        (asCube entry.frequency)
      let weighted := shiftPower entry.normalWeight total.value
      ⟨weighted.value,total.operations+weighted.bitSteps⟩
  else vectorBuild q fun _ => ⟨zero,1⟩
  ⟨coefficients.value,coefficients.operations+metadataCost L m k⟩

abbrev RawStore (L q : ℕ) := Table (Table (Vector Cell q) 3 L) 4 L

def readRaw {L q : ℕ} (store : RawStore L q)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) : Cell :=
  (tableRead 3 L (tableRead 4 L store (fun i => normalIndex (normal i)))
    (fun i => oppositeIndex (opposite i))).get residue

def rawBuild {L q : ℕ}
    (f : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → Program (Vector Cell q)) :
    Program (RawStore L q) :=
  tableBuild 4 L fun normal => tableBuild 3 L fun opposite =>
    f (fun i => indexNormal (normal i)) (fun i => indexOpposite (opposite i))

theorem readRaw_build {L q : ℕ}
    (f : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → Program (Vector Cell q))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) :
    readRaw (rawBuild f).value normal opposite residue = (f normal opposite).value.get residue := by
  unfold readRaw rawBuild
  rw [tableRead_build, tableRead_build]
  simp only [indexNormal_normalIndex, indexOpposite_oppositeIndex]

def formLeftSource {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q) (run : Fin (2*m+1)) : Program (RawStore L q) :=
  rawBuild (leftWordProgram env read run)

def formRightSource {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q) (run : Fin (2*m+1)) : Program (RawStore L q) :=
  rawBuild (rightWordProgram env read run)

def formLeftRuns {L m k q : ℕ} (env : Environment L m k) (read : BinaryLeftRead L m k q) :
    Program (Vector (RawStore L q) (2*m+1)) :=
  vectorBuild (2*m+1) fun i => formLeftSource env read i

def formRightRuns {L m k q : ℕ} (env : Environment L m k) (read : BinaryRightRead L m k q) :
    Program (Vector (RawStore L q) (2*m+1)) :=
  vectorBuild (2*m+1) fun i => formRightSource env read i


noncomputable def viewRaw {L q : ℕ} (data : RawStore L q) : SourceFormation.RawStore L q :=
  BinarySourceStorage.mapRaw Cell.view data

@[simp] theorem readRaw_view {L q : ℕ} (data : RawStore L q)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (j : Fin q) :
    SourceFormation.readRaw (viewRaw data) normal opposite j = (readRaw data normal opposite j).view :=
  BinarySourceStorage.readRawOf_map Cell.view data normal opposite j

theorem leftWordProgram_view {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (j : Fin q) :
    ((leftWordProgram env read run normal opposite).value.get j).view =
      (SourceFormation.leftWordProgram env (semanticLeft read) (runValue m run) normal opposite).value.get j := by
  have hc : (metadata env normal opposite).oppositeWeight+m =
      (metadata env normal opposite).normalWeight+run.val ↔
      ((metadata env normal opposite).oppositeWeight : ℤ)-
        ((metadata env normal opposite).normalWeight : ℤ) = runValue m run := by
    unfold runValue
    omega
  unfold leftWordProgram SourceFormation.leftWordProgram
  dsimp only
  simp only [Bool.and_eq_true,decide_eq_true_eq,hc]
  split_ifs
  · rw [vectorBuild_get,vectorBuild_get]
    rw [shiftPower_view,walshProgram_view,powerTwo_eq]
    rfl
  · rw [vectorBuild_get,vectorBuild_get]
    rfl

theorem rightWordProgram_view {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (j : Fin q) :
    ((rightWordProgram env read run normal opposite).value.get j).view =
      (SourceFormation.rightWordProgram env (semanticRight read) (runValue m run) normal opposite).value.get j := by
  have hc : (metadata env normal opposite).normalWeight+m =
      (metadata env normal opposite).oppositeWeight+run.val ↔
      ((metadata env normal opposite).normalWeight : ℤ)-
        ((metadata env normal opposite).oppositeWeight : ℤ) = runValue m run := by
    unfold runValue
    omega
  unfold rightWordProgram SourceFormation.rightWordProgram
  dsimp only
  simp only [Bool.and_eq_true,decide_eq_true_eq,hc]
  split_ifs
  · rw [vectorBuild_get,vectorBuild_get]
    rw [shiftPower_view,walshProgram_view,powerTwo_eq]
    rfl
  · rw [vectorBuild_get,vectorBuild_get]
    rfl

theorem formLeftSource_view {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q) (run : Fin (2*m+1)) :
    viewRaw (formLeftSource env read run).value =
      (SourceFormation.formLeftSource env (semanticLeft read) (runValue m run)).value := by
  apply BinarySourceStorage.rawStore_ext
  intro normal opposite j
  change SourceFormation.readRaw _ normal opposite j = SourceFormation.readRaw _ normal opposite j
  rw [readRaw_view,formLeftSource,readRaw_build,SourceFormation.formLeftSource,SourceFormation.readRaw_build]
  exact leftWordProgram_view env read run normal opposite j

theorem formRightSource_view {L m k q : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q) (run : Fin (2*m+1)) :
    viewRaw (formRightSource env read run).value =
      (SourceFormation.formRightSource env (semanticRight read) (runValue m run)).value := by
  apply BinarySourceStorage.rawStore_ext
  intro normal opposite j
  change SourceFormation.readRaw _ normal opposite j = SourceFormation.readRaw _ normal opposite j
  rw [readRaw_view,formRightSource,readRaw_build,SourceFormation.formRightSource,SourceFormation.readRaw_build]
  exact rightWordProgram_view env read run normal opposite j

theorem formLeftRuns_view {L m k q : ℕ} (env : Environment L m k) (read : BinaryLeftRead L m k q) :
    (formLeftRuns env read).value.map viewRaw = (SourceFormation.formLeftRuns env (semanticLeft read)).value := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change viewRaw ((formLeftRuns env read).value.get ⟨i,hi⟩) =
    (SourceFormation.formLeftRuns env (semanticLeft read)).value.get ⟨i,hi⟩
  simpa only [formLeftRuns,SourceFormation.formLeftRuns,vectorBuild_get] using
    formLeftSource_view env read ⟨i,hi⟩

theorem formRightRuns_view {L m k q : ℕ} (env : Environment L m k) (read : BinaryRightRead L m k q) :
    (formRightRuns env read).value.map viewRaw = (SourceFormation.formRightRuns env (semanticRight read)).value := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change viewRaw ((formRightRuns env read).value.get ⟨i,hi⟩) =
    (SourceFormation.formRightRuns env (semanticRight read)).value.get ⟨i,hi⟩
  simpa only [formRightRuns,SourceFormation.formRightRuns,vectorBuild_get] using
    formRightSource_view env read ⟨i,hi⟩

theorem walshTerm_natAbs_bound_actual {k : ℕ} (read : Cube k → Program Cell)
    (frequency outer : Cube k) (A : ℕ) (hr : (read outer).value.view.natAbs≤A) :
    (walshTerm read frequency outer).value.view.natAbs≤A := by
  rw [walshTerm_view]
  exact BinaryWalshBounds.walshTerm_natAbs_bound (semantic read) frequency outer A hr

theorem walshTerm_cost_actual {k : ℕ} (read : Cube k → Program Cell)
    (frequency outer : Cube k) (A B : ℕ)
    (hc : (read outer).operations≤B) (hr : (read outer).value.view.natAbs≤A) :
    (walshTerm read frequency outer).operations≤B+200*(k+A.size+1)^2+8*(k+1) := by
  have hw : (read outer).value.bits.magnitude.length≤k+A.size := by
    rw [(read outer).value.canonical]
    change (read outer).value.view.natAbs.size≤_
    exact (Nat.size_le_size hr).trans (by omega)
  have hn := neg_bitSteps (k+A.size) (read outer).value hw
  dsimp only [walshTerm]
  split
  · exact Nat.add_le_add_right (Nat.add_le_add hc hn) _
  · change (read outer).operations+0+8*(k+1)≤_
    omega

theorem list_operations_bound {α : Type} (xs : List α) (f : α → ℕ) (B : ℕ)
    (hf : ∀ x∈xs, f x≤B) : (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hf x (by simp)
      have ht := ih (fun y hy => hf y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

/-- Actual binary Walsh formation charges each sign conversion, every
canonical accumulation, and all stored-term traversal operations. -/
theorem walshProgram_cost_actual {k A B : ℕ} (read : Cube k → Program Cell)
    (frequency : Cube k)
    (hc : ∀ outer, (read outer).operations≤B)
    (hr : ∀ outer, (read outer).value.view.natAbs≤A) :
    (walshProgram read frequency).operations≤
      (B+400*(k+A.size+1)^2+8*(k+1)+10)*2^k := by
  let terms := (cubeList k).map (walshTerm read frequency)
  let values := terms.map (fun term => term.value.bits)
  have hlen : terms.length=2^k := by simp [terms,cubeList_length]
  have hterm : ∀ term∈terms, term.operations≤B+200*(k+A.size+1)^2+8*(k+1) := by
    intro term ht
    obtain ⟨outer,_,rfl⟩ := List.mem_map.mp ht
    exact walshTerm_cost_actual read frequency outer A B (hc outer) (hr outer)
  have hcost := list_operations_bound terms (fun term => term.operations)
    (B+200*(k+A.size+1)^2+8*(k+1)) hterm
  have hcanon : ∀ bits∈values,
      bits.magnitude.length=(signedValue bits).natAbs.size := by
    intro bits hb
    obtain ⟨term,_,rfl⟩ := List.mem_map.mp hb
    exact term.value.canonical
  have habs : ∀ bits∈values, (signedValue bits).natAbs≤A := by
    intro bits hb
    obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hb
    obtain ⟨outer,_,rfl⟩ := List.mem_map.mp ht
    exact walshTerm_natAbs_bound_actual read frequency outer A (hr outer)
  have htotal := BinaryWalshBounds.sumBinary_cost values k A
    (by simp [values,hlen]) hcanon habs
  have hp : 1≤(2:ℕ)^k := Nat.one_le_pow _ _ (by decide)
  rw [hlen] at hcost
  have hvalues : values.length=2^k := by simp [values,hlen]
  rw [hvalues] at htotal
  unfold scalarUnit at htotal
  change (terms.map (fun term => term.operations)).sum+
    (BinaryWalshBounds.sumBinary values).2+8*terms.length≤_
  rw [hlen]
  nlinarith


def bitUnit (L k A : ℕ) : ℕ := 1000*(formationWidth L k A+1)^3

theorem bitUnit_pos (L k A : ℕ) : 1 ≤ bitUnit L k A := by
  unfold bitUnit
  have h : 1 ≤ (formationWidth L k A+1)^3 := by
    have h : 0 < (formationWidth L k A+1)^3 := by positivity
    omega
  omega

theorem coefficient_allowance (L k A B : ℕ) :
    (B+400*(k+A.size+1)^2+8*(k+1)+10)*2^k +
      L*(200*(formationWidth L k A+1)^2)+8 ≤
    wordCoefficientBudget k B*bitUnit L k A := by
  let W := formationWidth L k A
  let T := (W+1)^2
  have hL : L ≤ W := by dsimp [W,formationWidth]; omega
  have hk : k+A.size+1 ≤ W+1 := by dsimp [W,formationWidth]; omega
  have hT : 1 ≤ T := by
    have h : 0 < T := by dsimp [T]; positivity
    omega
  have hU : (400+200*L)*T+1 ≤ bitUnit L k A := by
    have hc : 400+200*L ≤ 600*(W+1) := by omega
    have hm := Nat.mul_le_mul_right T hc
    have hw : 1 ≤ (W+1)*T := by nlinarith
    have he : bitUnit L k A = 1000*((W+1)*T) := by dsimp [bitUnit,W,T]; ring
    rw [he]
    nlinarith
  have hP : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by norm_num)
  have hSq := Nat.pow_le_pow_left hk 2
  change (k+A.size+1)^2 ≤ T at hSq
  have hC : B+400*(k+A.size+1)^2+8*(k+1)+10 + L*(200*T)+8 ≤
      (B+8*(k+1)+19)*bitUnit L k A := by
    have hscaled := Nat.mul_le_mul_left (B+8*(k+1)+19) hU
    have hm : (400+200*L)*T ≤ (B+8*(k+1)+19)*((400+200*L)*T) :=
      Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  calc
    _ ≤ (B+400*(k+A.size+1)^2+8*(k+1)+10)*2^k +(L*(200*T)+8)*2^k := by
      change _ + (L*(200*T)+8) ≤ _
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by positivity)) _
    _ = (B+400*(k+A.size+1)^2+8*(k+1)+10 + L*(200*T)+8)*2^k := by ring
    _ ≤ ((B+8*(k+1)+19)*bitUnit L k A)*2^k := Nat.mul_le_mul_right _ hC
    _ = _ := by unfold wordCoefficientBudget; ring


theorem leftWordProgram_cost {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q)
    (hc : ∀ Q bits outer r s j, (read Q bits outer r s j).operations ≤ B)
    (hr : ∀ Q bits outer r s j, (read Q bits outer r s j).value.view.natAbs ≤ A)
    (run : Fin (2*m+1)) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    (leftWordProgram env read run normal opposite).operations ≤ wordBudget L m k q B*bitUnit L k A := by
  let entry := metadata env normal opposite
  let rd (j : Fin q) (outer : Cube k) := read entry.support (asCube entry.outer) outer (asCube entry.gammaNormal) (asCube entry.gammaOpposite) j
  let frequency := asCube entry.frequency
  let coefficient (j : Fin q) : Program Cell :=
    let total := walshProgram (rd j) frequency
    let weighted := shiftPower entry.normalWeight total.value
    ⟨weighted.value,total.operations+weighted.bitSteps⟩
  have hrc (j : Fin q) (outer : Cube k) : (rd j outer).operations ≤ B :=
    hc entry.support (asCube entry.outer) outer (asCube entry.gammaNormal) (asCube entry.gammaOpposite) j
  have hrv (j : Fin q) (outer : Cube k) : (rd j outer).value.view.natAbs ≤ A :=
    hr entry.support (asCube entry.outer) outer (asCube entry.gammaNormal) (asCube entry.gammaOpposite) j
  have hU := bitUnit_pos L k A
  have hbase : 19 ≤ wordCoefficientBudget k B := by
    unfold wordCoefficientBudget
    exact (show 19 ≤ B+8*(k+1)+19 by omega).trans
      (Nat.le_mul_of_pos_right _ (by positivity))
  have hall : 19 ≤ wordCoefficientBudget k B*bitUnit L k A :=
    hbase.trans (Nat.le_mul_of_pos_right _ (by omega))
  have htarget : 8 ≤ wordCoefficientBudget k B*bitUnit L k A := by omega
  have hmeta : metadataCost L m k ≤ metadataCost L m k*bitUnit L k A :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold leftWordProgram
  dsimp only
  split_ifs
  · change (vectorBuild q coefficient).operations+metadataCost L m k ≤ _
    have hv := vectorBuild_cost q (wordCoefficientBudget k B*bitUnit L k A-8) coefficient (fun j => by
      apply Nat.le_sub_of_add_le
      have hw := walshProgram_cost_actual (rd j) frequency (hrc j) (hrv j)
      have hs := shift_bitSteps entry.normalWeight L k A (walshProgram (rd j) frequency).value
        (normalWeight_le env normal opposite) (walshProgram_natAbs_bound (rd j) frequency A (hrv j))
      exact (Nat.add_le_add_right (Nat.add_le_add hw hs) 8).trans (coefficient_allowance L k A B))
    rw [Nat.sub_add_cancel htarget] at hv
    calc
      _ ≤ wordCoefficientBudget k B*bitUnit L k A*q+metadataCost L m k*bitUnit L k A :=
        Nat.add_le_add hv hmeta
      _ = _ := by unfold wordBudget; ring
  · have hv := vectorBuild_cost q 1 (fun _ => (⟨zero,1⟩ : Program Cell)) (fun _ => le_rfl)
    have htarget' : 9 ≤ wordCoefficientBudget k B*bitUnit L k A := by omega
    calc
      _ ≤ wordCoefficientBudget k B*bitUnit L k A*q+metadataCost L m k*bitUnit L k A :=
        Nat.add_le_add (hv.trans (Nat.mul_le_mul_right q htarget')) hmeta
      _ = _ := by unfold wordBudget; ring

theorem rightWordProgram_cost {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q)
    (hc : ∀ Q bits r s outer j, (read Q bits r s outer j).operations ≤ B)
    (hr : ∀ Q bits r s outer j, (read Q bits r s outer j).value.view.natAbs ≤ A)
    (run : Fin (2*m+1)) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    (rightWordProgram env read run normal opposite).operations ≤ wordBudget L m k q B*bitUnit L k A := by
  let entry := metadata env normal opposite
  let rd (j : Fin q) (outer : Cube k) := read entry.support (asCube entry.outer) (asCube entry.gammaOpposite) (asCube entry.gammaNormal) outer j
  let frequency := asCube entry.frequency
  let coefficient (j : Fin q) : Program Cell :=
    let total := walshProgram (rd j) frequency
    let weighted := shiftPower entry.normalWeight total.value
    ⟨weighted.value,total.operations+weighted.bitSteps⟩
  have hrc (j : Fin q) (outer : Cube k) : (rd j outer).operations ≤ B :=
    hc entry.support (asCube entry.outer) (asCube entry.gammaOpposite) (asCube entry.gammaNormal) outer j
  have hrv (j : Fin q) (outer : Cube k) : (rd j outer).value.view.natAbs ≤ A :=
    hr entry.support (asCube entry.outer) (asCube entry.gammaOpposite) (asCube entry.gammaNormal) outer j
  have hU := bitUnit_pos L k A
  have hbase : 19 ≤ wordCoefficientBudget k B := by
    unfold wordCoefficientBudget
    exact (show 19 ≤ B+8*(k+1)+19 by omega).trans
      (Nat.le_mul_of_pos_right _ (by positivity))
  have hall : 19 ≤ wordCoefficientBudget k B*bitUnit L k A :=
    hbase.trans (Nat.le_mul_of_pos_right _ (by omega))
  have htarget : 8 ≤ wordCoefficientBudget k B*bitUnit L k A := by omega
  have hmeta : metadataCost L m k ≤ metadataCost L m k*bitUnit L k A :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold rightWordProgram
  dsimp only
  split_ifs
  · change (vectorBuild q coefficient).operations+metadataCost L m k ≤ _
    have hv := vectorBuild_cost q (wordCoefficientBudget k B*bitUnit L k A-8) coefficient (fun j => by
      apply Nat.le_sub_of_add_le
      have hw := walshProgram_cost_actual (rd j) frequency (hrc j) (hrv j)
      have hs := shift_bitSteps entry.normalWeight L k A (walshProgram (rd j) frequency).value
        (normalWeight_le env normal opposite) (walshProgram_natAbs_bound (rd j) frequency A (hrv j))
      exact (Nat.add_le_add_right (Nat.add_le_add hw hs) 8).trans (coefficient_allowance L k A B))
    rw [Nat.sub_add_cancel htarget] at hv
    calc
      _ ≤ wordCoefficientBudget k B*bitUnit L k A*q+metadataCost L m k*bitUnit L k A :=
        Nat.add_le_add hv hmeta
      _ = _ := by unfold wordBudget; ring
  · have hv := vectorBuild_cost q 1 (fun _ => (⟨zero,1⟩ : Program Cell)) (fun _ => le_rfl)
    have htarget' : 9 ≤ wordCoefficientBudget k B*bitUnit L k A := by omega
    calc
      _ ≤ wordCoefficientBudget k B*bitUnit L k A*q+metadataCost L m k*bitUnit L k A :=
        Nat.add_le_add (hv.trans (Nat.mul_le_mul_right q htarget')) hmeta
      _ = _ := by unfold wordBudget; ring

theorem rawBuild_cost {L q B : ℕ}
    (f : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → Program (Vector Cell q))
    (hf : ∀ normal opposite, (f normal opposite).operations ≤ B) :
    (rawBuild f).operations ≤ (B+56*L)*12^L := by
  have ho (normal : Fin L → Fin 4) :
      (tableBuild 3 L (fun opposite =>
        f (fun i => indexNormal (normal i)) (fun i => indexOpposite (opposite i)))).operations ≤
        (B+24*L)*3^L := by
    simpa using tableBuild_cost 3 L B _ (fun opposite => hf _ _)
  have hn := tableBuild_cost 4 L ((B+24*L)*3^L) _ ho
  have hp : 1 ≤ 3^L := Nat.one_le_pow L 3 (by norm_num)
  unfold rawBuild
  calc
    _ ≤ ((B+24*L)*3^L+32*L)*4^L := by simpa using hn
    _ ≤ (B+56*L)*12^L := by
      have hh : 32*L ≤ 32*L*3^L := by nlinarith
      rw [show (12:ℕ) = 3*4 by norm_num, mul_pow]
      calc
        _ ≤ ((B+56*L)*3^L)*4^L := Nat.mul_le_mul_right _ (by nlinarith)
        _ = _ := by ring


theorem formLeftSource_cost {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q)
    (hc : ∀ Q bits outer r s j, (read Q bits outer r s j).operations ≤ B)
    (hr : ∀ Q bits outer r s j, (read Q bits outer r s j).value.view.natAbs ≤ A)
    (run : Fin (2*m+1)) :
    (formLeftSource env read run).operations ≤ sourceBudget L m k q B*bitUnit L k A := by
  have h := rawBuild_cost _ (fun normal opposite => leftWordProgram_cost env read hc hr run normal opposite)
  have hU := bitUnit_pos L k A
  have hcontrol : 56*L ≤ 56*L*bitUnit L k A := Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ (wordBudget L m k q B*bitUnit L k A+56*L)*12^L := h
    _ ≤ (wordBudget L m k q B*bitUnit L k A+56*L*bitUnit L k A)*12^L :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left hcontrol _)
    _ = _ := by unfold sourceBudget; ring

theorem formRightSource_cost {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q)
    (hc : ∀ Q bits r s outer j, (read Q bits r s outer j).operations ≤ B)
    (hr : ∀ Q bits r s outer j, (read Q bits r s outer j).value.view.natAbs ≤ A)
    (run : Fin (2*m+1)) :
    (formRightSource env read run).operations ≤ sourceBudget L m k q B*bitUnit L k A := by
  have h := rawBuild_cost _ (fun normal opposite => rightWordProgram_cost env read hc hr run normal opposite)
  have hU := bitUnit_pos L k A
  have hcontrol : 56*L ≤ 56*L*bitUnit L k A := Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ (wordBudget L m k q B*bitUnit L k A+56*L)*12^L := h
    _ ≤ (wordBudget L m k q B*bitUnit L k A+56*L*bitUnit L k A)*12^L :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left hcontrol _)
    _ = _ := by unfold sourceBudget; ring

theorem formLeftRuns_cost {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q)
    (hc : ∀ Q bits outer r s j, (read Q bits outer r s j).operations ≤ B)
    (hr : ∀ Q bits outer r s j, (read Q bits outer r s j).value.view.natAbs ≤ A) :
    (formLeftRuns env read).operations ≤ (sourceBudget L m k q B+8)*(2*m+1)*bitUnit L k A := by
  have h := vectorBuild_cost (2*m+1) (sourceBudget L m k q B*bitUnit L k A) _
    (fun i => formLeftSource_cost env read hc hr i)
  have hU := bitUnit_pos L k A
  have hcontrol : 8 ≤ 8*bitUnit L k A := by omega
  calc
    _ ≤ (sourceBudget L m k q B*bitUnit L k A+8)*(2*m+1) := h
    _ ≤ (sourceBudget L m k q B*bitUnit L k A+8*bitUnit L k A)*(2*m+1) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left hcontrol _)
    _ = _ := by ring

theorem formRightRuns_cost {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q)
    (hc : ∀ Q bits r s outer j, (read Q bits r s outer j).operations ≤ B)
    (hr : ∀ Q bits r s outer j, (read Q bits r s outer j).value.view.natAbs ≤ A) :
    (formRightRuns env read).operations ≤ (sourceBudget L m k q B+8)*(2*m+1)*bitUnit L k A := by
  have h := vectorBuild_cost (2*m+1) (sourceBudget L m k q B*bitUnit L k A) _
    (fun i => formRightSource_cost env read hc hr i)
  have hU := bitUnit_pos L k A
  have hcontrol : 8 ≤ 8*bitUnit L k A := by omega
  calc
    _ ≤ (sourceBudget L m k q B*bitUnit L k A+8)*(2*m+1) := h
    _ ≤ (sourceBudget L m k q B*bitUnit L k A+8*bitUnit L k A)*(2*m+1) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left hcontrol _)
    _ = _ := by ring


/-- Original folded 0/1 coefficients are read as Boolean cells. -/
abbrev BoolLeftRead (L m k q : ℕ) :=
  Finset (Fin L) → Cube L → Cube k → Cube m → Cube m → Fin q → Program Bool
abbrev BoolRightRead (L m k q : ℕ) :=
  Finset (Fin L) → Cube L → Cube m → Cube m → Cube k → Fin q → Program Bool

def liftLeft {L m k q : ℕ} (read : BoolLeftRead L m k q) : BinaryLeftRead L m k q :=
  fun Q bits outer r s j =>
    let child := read Q bits outer r s j
    ⟨ofBool child.value,child.operations+1⟩

def liftRight {L m k q : ℕ} (read : BoolRightRead L m k q) : BinaryRightRead L m k q :=
  fun Q bits r s outer j =>
    let child := read Q bits r s outer j
    ⟨ofBool child.value,child.operations+1⟩

@[simp] theorem liftLeft_view {L m k q : ℕ} (read : BoolLeftRead L m k q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube k) (r s : Cube m) (j : Fin q) :
    (liftLeft read Q bits outer r s j).value.view = if (read Q bits outer r s j).value then 1 else 0 := by
  simp only [liftLeft,ofBool_view]

@[simp] theorem liftRight_view {L m k q : ℕ} (read : BoolRightRead L m k q)
    (Q : Finset (Fin L)) (bits : Cube L) (r s : Cube m) (outer : Cube k) (j : Fin q) :
    (liftRight read Q bits r s outer j).value.view = if (read Q bits r s outer j).value then 1 else 0 := by
  simp only [liftRight,ofBool_view]

theorem formLeftRuns_bool_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : BoolLeftRead L m k q)
    (hc : ∀ Q bits outer r s j, (read Q bits outer r s j).operations ≤ B) :
    (formLeftRuns env (liftLeft read)).operations ≤
      (sourceBudget L m k q (B+1)+8)*(2*m+1)*bitUnit L k 1 := by
  apply formLeftRuns_cost env (liftLeft read)
  · intro Q bits outer r s j
    exact Nat.add_le_add_right (hc Q bits outer r s j) _
  · intro Q bits outer r s j
    rw [liftLeft_view]
    split <;> norm_num

theorem formRightRuns_bool_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : BoolRightRead L m k q)
    (hc : ∀ Q bits r s outer j, (read Q bits r s outer j).operations ≤ B) :
    (formRightRuns env (liftRight read)).operations ≤
      (sourceBudget L m k q (B+1)+8)*(2*m+1)*bitUnit L k 1 := by
  apply formRightRuns_cost env (liftRight read)
  · intro Q bits r s outer j
    exact Nat.add_le_add_right (hc Q bits r s outer j) _
  · intro Q bits r s outer j
    rw [liftRight_view]
    split <;> norm_num

theorem formationWidth_le_common (n degree L k A cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hk : k ≤ L) (hA : A ≤ n^degree) :
    formationWidth L k A ≤ AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  have hAs := (Nat.size_le_size (AdaptiveBitBounds.original_power_bound n degree A hA)).trans_eq Nat.size_pow
  have hlin : formationWidth L k A ≤ (2*cL+degree+1)*(n.size+1) := by
    unfold formationWidth
    nlinarith only [hL,hk,hAs]
  have hp : n.size+1 ≤ (n.size+1)^2 := by nlinarith
  have hc : 2*cL+degree+1 ≤
      CoefficientBudget.budgetConstant cL cm cq degree+2*(4*cm+2)^2+20 := by
    unfold CoefficientBudget.budgetConstant
    nlinarith
  exact hlin.trans (Nat.mul_le_mul hc hp)


theorem bitUnit_le_common (n degree L k A cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hk : k ≤ L) (hA : A ≤ n^degree) :
    bitUnit L k A ≤ 1000*(AdaptiveBitBounds.commonBitWidth n degree cL cm cq+1)^3 := by
  unfold bitUnit
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (formationWidth_le_common n degree L k A cL cm cq hL hk hA) _) _)

theorem formLeftRuns_cost_common {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryLeftRead L m k q)
    (hc : ∀ Q bits outer r s j, (read Q bits outer r s j).operations ≤ B)
    (hr : ∀ Q bits outer r s j, (read Q bits outer r s j).value.view.natAbs ≤ A)
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hk : k ≤ L) (hA : A ≤ n^degree) :
    (formLeftRuns env read).operations ≤ (sourceBudget L m k q B+8)*(2*m+1)*
      (1000*(AdaptiveBitBounds.commonBitWidth n degree cL cm cq+1)^3) :=
  (formLeftRuns_cost env read hc hr).trans
    (Nat.mul_le_mul_left _ (bitUnit_le_common n degree L k A cL cm cq hL hk hA))

theorem formRightRuns_cost_common {L m k q A B : ℕ} (env : Environment L m k)
    (read : BinaryRightRead L m k q)
    (hc : ∀ Q bits r s outer j, (read Q bits r s outer j).operations ≤ B)
    (hr : ∀ Q bits r s outer j, (read Q bits r s outer j).value.view.natAbs ≤ A)
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hk : k ≤ L) (hA : A ≤ n^degree) :
    (formRightRuns env read).operations ≤ (sourceBudget L m k q B+8)*(2*m+1)*
      (1000*(AdaptiveBitBounds.commonBitWidth n degree cL cm cq+1)^3) :=
  (formRightRuns_cost env read hc hr).trans
    (Nat.mul_le_mul_left _ (bitUnit_le_common n degree L k A cL cm cq hL hk hA))


#print axioms liftLeft_view
#print axioms liftRight_view
#print axioms formLeftRuns_bool_cost
#print axioms formRightRuns_bool_cost
#print axioms formationWidth_le_common
#print axioms formLeftRuns_cost_common
#print axioms formRightRuns_cost_common

#print axioms walshProgram_cost_actual
#print axioms formLeftSource_cost
#print axioms formRightSource_cost
#print axioms formLeftRuns_cost
#print axioms formRightRuns_cost

#print axioms formLeftSource_view
#print axioms formRightSource_view
#print axioms formLeftRuns_view
#print axioms formRightRuns_view

end ThinMatrix.BinarySourceFormation
