import BinarySourceFormation
import BinaryCell
import ThinMatrixBackend
import FoldedBackendExecution
import BinaryLowEncoder
import BinaryHighExecution
import BinaryHighTable
import BinaryLowQuery

/-!
# Stored-bit execution of the thin-product backend

Runtime coefficient payloads are canonical signed Boolean lists. The original
coefficient readers preserve the native stored-address control and copy bits
with charged primitive execution. Source/cache/table/query stages are joined
below using their actual returned arrays and counters; integer views are
reserved for erased refinement statements.

This bit-cell and bounded-array model is separate from Light compilation.
-/

namespace ThinMatrix.BinaryOriginalReader

open SourceFormation RowIndexing WalshEmbedding

abbrev Cell := BinaryCell.Cell

def viewData {len q : ℕ} (data : Vector (Vector Cell q) len) :
    Vector (Vector ℤ q) len := data.map (fun row => row.map BinaryCell.view)

/-- Address and control execution for a stored binary left coefficient. -/
def selectLeft {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) : Program Cell :=
  let outer := rowRankProgram store row
  let middle := middleRankProgram m inner
  let v := band*(store.codes.toArray.size*4^(L-m)) + outer.value.val
  if hv : v < originalOuterSize m data then
    let address : Fin (N*4^m) := ⟨middle.value.val+4^m*v, by
      have hvN : v < N := by simpa only [originalOuterSize_left] using hv
      have hm := middle.value.isLt
      nlinarith [Nat.mul_le_mul_right (4^m) (Nat.succ_le_of_lt hvN)]⟩
    ⟨(data.get address).get target, outer.operations+middle.operations+12⟩
  else ⟨BinaryCell.zero, outer.operations+middle.operations+12⟩

/-- Address and control execution for a stored binary right coefficient. -/
def selectRight {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) : Program Cell :=
  let outer := rowRankProgram store col
  let middle := middleRankProgram m inner
  let cachedOuter := originalOuterSize m data
  let v := band*(store.codes.toArray.size*4^(L-m)) + outer.value.val
  if hv : v < cachedOuter then
    let address : Fin (4^m*N) := ⟨v+cachedOuter*middle.value.val, by
      have hN : cachedOuter = N := originalOuterSize_right data
      have hvN : v < N := by simpa only [hN] using hv
      have hm := middle.value.isLt
      rw [hN]
      nlinarith [Nat.mul_le_mul_left N (Nat.succ_le_of_lt hm)]⟩
    ⟨(data.get address).get target, outer.operations+middle.operations+12⟩
  else ⟨BinaryCell.zero, outer.operations+middle.operations+12⟩

def readOriginalLeftProgram {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) : Program Cell :=
  let input := selectLeft store data band row inner target
  let output := BinaryCell.copy input.value
  ⟨output.value, input.operations+output.bitSteps⟩

def readOriginalRightProgram {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) : Program Cell :=
  let input := selectRight store data band inner col target
  let output := BinaryCell.copy input.value
  ⟨output.value, input.operations+output.bitSteps⟩

theorem selectLeft_view {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) :
    BinaryCell.view (selectLeft store data band row inner target).value =
      (RowIndexing.readOriginalLeftProgram store (viewData data) band row inner target).value := by
  simp only [selectLeft, RowIndexing.readOriginalLeftProgram, originalOuterSize_left]
  split <;> simp only [viewData, Vector.get_map, BinaryCell.zero_view]

theorem selectRight_view {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) :
    BinaryCell.view (selectRight store data band inner col target).value =
      (RowIndexing.readOriginalRightProgram store (viewData data) band inner col target).value := by
  simp only [selectRight, RowIndexing.readOriginalRightProgram, originalOuterSize_right]
  split <;> simp only [viewData, Vector.get_map, BinaryCell.zero_view]

theorem selectLeft_control {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) :
    (selectLeft store data band row inner target).operations =
      (RowIndexing.readOriginalLeftProgram store (viewData data) band row inner target).operations := by
  simp only [selectLeft, RowIndexing.readOriginalLeftProgram, originalOuterSize_left]
  split <;> rfl

theorem selectRight_control {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) :
    (selectRight store data band inner col target).operations =
      (RowIndexing.readOriginalRightProgram store (viewData data) band inner col target).operations := by
  simp only [selectRight, RowIndexing.readOriginalRightProgram, originalOuterSize_right]
  split <;> rfl

@[simp] theorem readOriginalLeftProgram_view {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) :
    BinaryCell.view (readOriginalLeftProgram store data band row inner target).value =
      (RowIndexing.readOriginalLeftProgram store (viewData data) band row inner target).value := by
  simp only [readOriginalLeftProgram, BinaryCell.copy_view, selectLeft_view]

@[simp] theorem readOriginalRightProgram_view {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) :
    BinaryCell.view (readOriginalRightProgram store data band inner col target).value =
      (RowIndexing.readOriginalRightProgram store (viewData data) band inner col target).value := by
  simp only [readOriginalRightProgram, BinaryCell.copy_view, selectRight_view]

theorem readOriginalLeftProgram_operations {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) :
    (readOriginalLeftProgram store data band row inner target).operations =
      (RowIndexing.readOriginalLeftProgram store (viewData data) band row inner target).operations+
        (BinaryCell.copy (selectLeft store data band row inner target).value).bitSteps := by
  simp only [readOriginalLeftProgram, selectLeft_control]

theorem readOriginalRightProgram_operations {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) :
    (readOriginalRightProgram store data band inner col target).operations =
      (RowIndexing.readOriginalRightProgram store (viewData data) band inner col target).operations+
        (BinaryCell.copy (selectRight store data band inner col target).value).bitSteps := by
  simp only [readOriginalRightProgram, selectRight_control]

theorem selectLeft_size {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) (B : ℕ)
    (hdata : ∀ address r, (BinaryCell.view ((data.get address).get r)).natAbs.size ≤ B) :
    (BinaryCell.view (selectLeft store data band row inner target).value).natAbs.size ≤ B := by
  unfold selectLeft
  dsimp only
  split
  · exact hdata _ target
  · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]

theorem selectRight_size {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) (B : ℕ)
    (hdata : ∀ address r, (BinaryCell.view ((data.get address).get r)).natAbs.size ≤ B) :
    (BinaryCell.view (selectRight store data band inner col target).value).natAbs.size ≤ B := by
  unfold selectRight
  dsimp only
  split
  · exact hdata _ target
  · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]

theorem readOriginalLeftProgram_price {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) (B : ℕ)
    (hdata : ∀ address r, (BinaryCell.view ((data.get address).get r)).natAbs.size ≤ B) :
    (readOriginalLeftProgram store data band row inner target).operations ≤
      (RowIndexing.readOriginalLeftProgram store (viewData data) band row inner target).operations+
        BackendScalarBits.backendScalarUnit B := by
  rw [readOriginalLeftProgram_operations]
  exact Nat.add_le_add_left (BinaryCell.copy_price B _
    (selectLeft_size store data band row inner target B hdata)) _

theorem readOriginalRightProgram_price {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) (B : ℕ)
    (hdata : ∀ address r, (BinaryCell.view ((data.get address).get r)).natAbs.size ≤ B) :
    (readOriginalRightProgram store data band inner col target).operations ≤
      (RowIndexing.readOriginalRightProgram store (viewData data) band inner col target).operations+
        BackendScalarBits.backendScalarUnit B := by
  rw [readOriginalRightProgram_operations]
  exact Nat.add_le_add_left (BinaryCell.copy_price B _
    (selectRight_size store data band inner col target B hdata)) _

theorem readOriginalLeftProgram_cost {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) (B : ℕ)
    (hdata : ∀ address r, (BinaryCell.view ((data.get address).get r)).natAbs.size ≤ B)
    (hm : m ≤ L) :
    (readOriginalLeftProgram store data band row inner target).operations ≤
      64*(L+1)^2*(2^L+1)+BackendScalarBits.backendScalarUnit B := by
  exact (readOriginalLeftProgram_price store data band row inner target B hdata).trans
    (Nat.add_le_add_right
      (RowIndexing.readOriginalLeftProgram_cost store (viewData data) band row inner target hm) _)

theorem readOriginalRightProgram_cost {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector Cell q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) (B : ℕ)
    (hdata : ∀ address r, (BinaryCell.view ((data.get address).get r)).natAbs.size ≤ B)
    (hm : m ≤ L) :
    (readOriginalRightProgram store data band inner col target).operations ≤
      64*(L+1)^2*(2^L+1)+BackendScalarBits.backendScalarUnit B := by
  exact (readOriginalRightProgram_price store data band inner col target B hdata).trans
    (Nat.add_le_add_right
      (RowIndexing.readOriginalRightProgram_cost store (viewData data) band inner col target hm) _)

end ThinMatrix.BinaryOriginalReader

#print axioms ThinMatrix.BinaryOriginalReader.readOriginalLeftProgram_view
#print axioms ThinMatrix.BinaryOriginalReader.readOriginalRightProgram_view
#print axioms ThinMatrix.BinaryOriginalReader.readOriginalLeftProgram_operations
#print axioms ThinMatrix.BinaryOriginalReader.readOriginalRightProgram_operations
#print axioms ThinMatrix.BinaryOriginalReader.readOriginalLeftProgram_cost
#print axioms ThinMatrix.BinaryOriginalReader.readOriginalRightProgram_cost

namespace ThinMatrix.BinaryInputAdapter

open SourceFormation BinarySourceStorage WalshEmbedding

abbrev Cell := BinaryCell.Cell
abbrev InputStoreOf (α : Type*) (L m q : ℕ) :=
  Table (Table (Table (Table (Table (Vector α q) 2 m) 2 m) 2 (L-m)) 2 L) 2 L
abbrev InputStore (L m q : ℕ) := InputStoreOf Cell L m q

def mapInput {α β : Type*} {L m q : ℕ} (g : α → β)
    (store : InputStoreOf α L m q) : InputStoreOf β L m q :=
  mapTable (mapTable (mapTable (mapTable (mapTable
    (fun v : Vector α q => v.map g) 2 m) 2 m) 2 (L-m)) 2 L) 2 L store

def viewInput {L m q : ℕ} (store : InputStore L m q) : ThinMatrixBackend.InputStore L m q :=
  mapInput BinaryCell.view store

def buildLeftAdapter {L m q : ℕ}
    (read : BinarySourceFormation.BinaryLeftRead L m (L-m) q) : Program (InputStore L m q) :=
  tableBuild 2 L fun Q => tableBuild 2 L fun bits =>
    tableBuild 2 (L-m) fun outer => tableBuild 2 m fun h1 => tableBuild 2 m fun h2 =>
      vectorBuild q (fun r => read (cubeSupport (keyCube Q)) (keyCube bits)
        (keyCube outer) (keyCube h1) (keyCube h2) r)

def buildRightAdapter {L m q : ℕ}
    (read : BinarySourceFormation.BinaryRightRead L m (L-m) q) : Program (InputStore L m q) :=
  tableBuild 2 L fun Q => tableBuild 2 L fun bits =>
    tableBuild 2 (L-m) fun outer => tableBuild 2 m fun h1 => tableBuild 2 m fun h2 =>
      vectorBuild q (fun r => read (cubeSupport (keyCube Q)) (keyCube bits)
        (keyCube h1) (keyCube h2) (keyCube outer) r)

def readInputOf {α : Type*} {L m q : ℕ} (store : InputStoreOf α L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) : α :=
  (tableRead 2 m (tableRead 2 m (tableRead 2 (L-m)
    (tableRead 2 L (tableRead 2 L store (cubeKey (setBits Q))) (cubeKey bits))
    (cubeKey outer)) (cubeKey h1)) (cubeKey h2)).get r

abbrev readInput {L m q : ℕ} := @readInputOf Cell L m q

@[simp] theorem readInputOf_map {α β : Type*} {L m q : ℕ} (g : α → β)
    (store : InputStoreOf α L m q) (Q : Finset (Fin L)) (bits : Cube L)
    (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    readInputOf (mapInput g store) Q bits outer h1 h2 r =
      g (readInputOf store Q bits outer h1 h2 r) := by
  simp only [readInputOf, mapInput, tableRead_map, Vector.get_map]

@[simp] theorem readInput_view {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    ThinMatrixBackend.readInput (viewInput store) Q bits outer h1 h2 r =
      BinaryCell.view (readInput store Q bits outer h1 h2 r) := by
  exact readInputOf_map BinaryCell.view store Q bits outer h1 h2 r

@[simp] theorem read_buildLeftAdapter {L m q : ℕ}
    (read : BinarySourceFormation.BinaryLeftRead L m (L-m) q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    readInput (buildLeftAdapter read).value Q bits outer h1 h2 r =
      (read Q bits outer h1 h2 r).value := by
  unfold readInput readInputOf buildLeftAdapter
  simp only [tableRead_build, keyCube_cubeKey, ThinMatrixBackend.cubeSupport_setBits, vectorBuild_get]

@[simp] theorem read_buildRightAdapter {L m q : ℕ}
    (read : BinarySourceFormation.BinaryRightRead L m (L-m) q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    readInput (buildRightAdapter read).value Q bits outer h1 h2 r =
      (read Q bits h1 h2 outer r).value := by
  unfold readInput readInputOf buildRightAdapter
  simp only [tableRead_build, keyCube_cubeKey, ThinMatrixBackend.cubeSupport_setBits, vectorBuild_get]

theorem buildLeftAdapter_view {L m q : ℕ}
    (read : BinarySourceFormation.BinaryLeftRead L m (L-m) q) :
    viewInput (buildLeftAdapter read).value =
      (ThinMatrixBackend.buildLeftAdapter (BinarySourceFormation.semanticLeft read)).value := by
  symm
  unfold ThinMatrixBackend.buildLeftAdapter buildLeftAdapter viewInput mapInput
  apply tableBuild_map_value
  intro Q
  apply tableBuild_map_value
  intro bits
  apply tableBuild_map_value
  intro outer
  apply tableBuild_map_value
  intro h1
  apply tableBuild_map_value
  intro h2
  apply vectorBuild_map_value
  intro r
  rfl

theorem buildRightAdapter_view {L m q : ℕ}
    (read : BinarySourceFormation.BinaryRightRead L m (L-m) q) :
    viewInput (buildRightAdapter read).value =
      (ThinMatrixBackend.buildRightAdapter (BinarySourceFormation.semanticRight read)).value := by
  symm
  unfold ThinMatrixBackend.buildRightAdapter buildRightAdapter viewInput mapInput
  apply tableBuild_map_value
  intro Q
  apply tableBuild_map_value
  intro bits
  apply tableBuild_map_value
  intro outer
  apply tableBuild_map_value
  intro h1
  apply tableBuild_map_value
  intro h2
  apply vectorBuild_map_value
  intro r
  rfl

/-- The cached leaf is copied as binary bits after the stored radix-path read. -/
def leftInputReader {L m q : ℕ} (store : InputStore L m q) :
    BinarySourceFormation.BinaryLeftRead L m (L-m) q :=
  fun Q bits outer h1 h2 r =>
    let output := BinaryCell.copy (readInput store Q bits outer h1 h2 r)
    ⟨output.value, 8*(3*L+m+1)+output.bitSteps⟩

def rightInputReader {L m q : ℕ} (store : InputStore L m q) :
    BinarySourceFormation.BinaryRightRead L m (L-m) q :=
  fun Q bits h1 h2 outer r =>
    let output := BinaryCell.copy (readInput store Q bits outer h1 h2 r)
    ⟨output.value, 8*(3*L+m+1)+output.bitSteps⟩

@[simp] theorem leftInputReader_view {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    BinaryCell.view (leftInputReader store Q bits outer h1 h2 r).value =
      (ThinMatrixBackend.leftInputReader (viewInput store) Q bits outer h1 h2 r).value := by
  simp only [leftInputReader, ThinMatrixBackend.leftInputReader, BinaryCell.copy_view, readInput_view]

@[simp] theorem rightInputReader_view {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    BinaryCell.view (rightInputReader store Q bits h1 h2 outer r).value =
      (ThinMatrixBackend.rightInputReader (viewInput store) Q bits h1 h2 outer r).value := by
  simp only [rightInputReader, ThinMatrixBackend.rightInputReader, BinaryCell.copy_view, readInput_view]

theorem leftInputReader_operations {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    (leftInputReader store Q bits outer h1 h2 r).operations =
      (ThinMatrixBackend.leftInputReader (viewInput store) Q bits outer h1 h2 r).operations+
        (BinaryCell.copy (readInput store Q bits outer h1 h2 r)).bitSteps := rfl

theorem rightInputReader_operations {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    (rightInputReader store Q bits h1 h2 outer r).operations =
      (ThinMatrixBackend.rightInputReader (viewInput store) Q bits h1 h2 outer r).operations+
        (BinaryCell.copy (readInput store Q bits outer h1 h2 r)).bitSteps := rfl

theorem leftInputReader_price {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) (B : ℕ)
    (hsize : (BinaryCell.view (readInput store Q bits outer h1 h2 r)).natAbs.size ≤ B) :
    (leftInputReader store Q bits outer h1 h2 r).operations ≤
      8*(3*L+m+1)+BackendScalarBits.backendScalarUnit B :=
  Nat.add_le_add_left (BinaryCell.copy_price B _ hsize) _

theorem rightInputReader_price {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) (B : ℕ)
    (hsize : (BinaryCell.view (readInput store Q bits outer h1 h2 r)).natAbs.size ≤ B) :
    (rightInputReader store Q bits h1 h2 outer r).operations ≤
      8*(3*L+m+1)+BackendScalarBits.backendScalarUnit B :=
  Nat.add_le_add_left (BinaryCell.copy_price B _ hsize) _

def adapterBudget (L m q B : ℕ) : ℕ :=
  ThinMatrixBackend.binaryTableBudget L (ThinMatrixBackend.binaryTableBudget L
    (ThinMatrixBackend.binaryTableBudget (L-m) (ThinMatrixBackend.binaryTableBudget m
      (ThinMatrixBackend.binaryTableBudget m ((B+8)*q)))))

theorem buildLeftAdapter_cost {L m q : ℕ}
    (read : BinarySourceFormation.BinaryLeftRead L m (L-m) q) (B : ℕ)
    (hread : ∀ Q bits outer h1 h2 r, (read Q bits outer h1 h2 r).operations ≤ B) :
    (buildLeftAdapter read).operations ≤ adapterBudget L m q B := by
  unfold buildLeftAdapter adapterBudget ThinMatrixBackend.binaryTableBudget
  apply tableBuild_cost
  intro Q
  apply tableBuild_cost
  intro bits
  apply tableBuild_cost
  intro outer
  apply tableBuild_cost
  intro h1
  apply tableBuild_cost
  intro h2
  apply vectorBuild_cost
  intro r
  exact hread _ _ _ _ _ _

theorem buildRightAdapter_cost {L m q : ℕ}
    (read : BinarySourceFormation.BinaryRightRead L m (L-m) q) (B : ℕ)
    (hread : ∀ Q bits h1 h2 outer r, (read Q bits h1 h2 outer r).operations ≤ B) :
    (buildRightAdapter read).operations ≤ adapterBudget L m q B := by
  unfold buildRightAdapter adapterBudget ThinMatrixBackend.binaryTableBudget
  apply tableBuild_cost
  intro Q
  apply tableBuild_cost
  intro bits
  apply tableBuild_cost
  intro outer
  apply tableBuild_cost
  intro h1
  apply tableBuild_cost
  intro h2
  apply vectorBuild_cost
  intro r
  exact hread _ _ _ _ _ _

end ThinMatrix.BinaryInputAdapter

#print axioms ThinMatrix.BinaryInputAdapter.readInput_view
#print axioms ThinMatrix.BinaryInputAdapter.buildLeftAdapter_view
#print axioms ThinMatrix.BinaryInputAdapter.buildRightAdapter_view
#print axioms ThinMatrix.BinaryInputAdapter.leftInputReader_view
#print axioms ThinMatrix.BinaryInputAdapter.rightInputReader_view
#print axioms ThinMatrix.BinaryInputAdapter.leftInputReader_price
#print axioms ThinMatrix.BinaryInputAdapter.rightInputReader_price
#print axioms ThinMatrix.BinaryInputAdapter.buildLeftAdapter_cost
#print axioms ThinMatrix.BinaryInputAdapter.buildRightAdapter_cost


namespace ThinMatrix.BinaryBandSource

open SourceFormation WalshEmbedding GoodMapEmbedding

abbrev Cell := BinaryCell.Cell
abbrev StoredLeftMatrix (L m q : ℕ) :=
  Vector (Vector Cell q) (ThinMatrixBackend.tileWidth L m * 4^m)
abbrev StoredRightMatrix (L m q : ℕ) :=
  Vector (Vector Cell q) (4^m * ThinMatrixBackend.tileWidth L m)

def storedRawLeftReader {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q) :
    BinarySourceFormation.BinaryLeftRead L m (L-m) q :=
  fun Q bits outer h1 h2 r =>
    if hb : ThinMatrixBackend.readGoodSet good Q = true then
      let hQ : Q ∈ goodSlots L m := by rw [hg Q] at hb; exact of_decide_eq_true hb
      let compressed := ThinMatrixBackend.compressOutsideProgram Q (goodSlots_size L m Q hQ) bits
      let read := BinaryOriginalReader.readOriginalLeftProgram layout data 0
        (⟨Q,hQ⟩,(asCube compressed.value,outer)) (h1,h2) r
      ⟨read.value, read.operations+compressed.operations+100*(L+m+1)^3⟩
    else ⟨BinaryCell.zero,100*(L+m+1)^3⟩

def storedRawRightReader {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q) :
    BinarySourceFormation.BinaryRightRead L m (L-m) q :=
  fun Q bits h1 h2 outer r =>
    if hb : ThinMatrixBackend.readGoodSet good Q = true then
      let hQ : Q ∈ goodSlots L m := by rw [hg Q] at hb; exact of_decide_eq_true hb
      let compressed := ThinMatrixBackend.compressOutsideProgram Q (goodSlots_size L m Q hQ) bits
      let read := BinaryOriginalReader.readOriginalRightProgram layout data 0 (h1,h2)
        (⟨Q,hQ⟩,(asCube compressed.value,outer)) r
      ⟨read.value, read.operations+compressed.operations+100*(L+m+1)^3⟩
    else ⟨BinaryCell.zero,100*(L+m+1)^3⟩

@[simp] theorem storedRawLeftReader_view {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    BinaryCell.view (storedRawLeftReader good hg layout data Q bits outer h1 h2 r).value =
      (ThinMatrixBackend.storedRawLeftReader good hg layout (BinaryOriginalReader.viewData data)
        Q bits outer h1 h2 r).value := by
  unfold storedRawLeftReader ThinMatrixBackend.storedRawLeftReader
  split <;> simp only [ThinMatrixBackend.originalLeftReader,
    BinaryOriginalReader.readOriginalLeftProgram_view, BinaryCell.zero_view]

@[simp] theorem storedRawRightReader_view {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    BinaryCell.view (storedRawRightReader good hg layout data Q bits h1 h2 outer r).value =
      (ThinMatrixBackend.storedRawRightReader good hg layout (BinaryOriginalReader.viewData data)
        Q bits h1 h2 outer r).value := by
  unfold storedRawRightReader ThinMatrixBackend.storedRawRightReader
  split <;> simp only [ThinMatrixBackend.originalRightReader,
    BinaryOriginalReader.readOriginalRightProgram_view, BinaryCell.zero_view]

theorem storedRawLeftReader_width {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q) (B : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs.size ≤ B)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    (BinaryCell.view (storedRawLeftReader good hg layout data Q bits outer h1 h2 r).value).natAbs.size ≤ B := by
  unfold storedRawLeftReader
  split
  · simp only [BinaryOriginalReader.readOriginalLeftProgram, BinaryCell.copy_view]
    exact BinaryOriginalReader.selectLeft_size _ _ _ _ _ _ B hdata
  · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]

theorem storedRawRightReader_width {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q) (B : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs.size ≤ B)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    (BinaryCell.view (storedRawRightReader good hg layout data Q bits h1 h2 outer r).value).natAbs.size ≤ B := by
  unfold storedRawRightReader
  split
  · simp only [BinaryOriginalReader.readOriginalRightProgram, BinaryCell.copy_view]
    exact BinaryOriginalReader.selectRight_size _ _ _ _ _ _ B hdata
  · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]

theorem storedRawLeftReader_natAbs {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q) (A : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs ≤ A)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    (BinaryCell.view (storedRawLeftReader good hg layout data Q bits outer h1 h2 r).value).natAbs ≤ A := by
  unfold storedRawLeftReader
  split
  · simp only [BinaryOriginalReader.readOriginalLeftProgram, BinaryCell.copy_view]
    unfold BinaryOriginalReader.selectLeft
    dsimp only
    split
    · exact hdata _ r
    · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]
  · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]

theorem storedRawRightReader_natAbs {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q) (A : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs ≤ A)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    (BinaryCell.view (storedRawRightReader good hg layout data Q bits h1 h2 outer r).value).natAbs ≤ A := by
  unfold storedRawRightReader
  split
  · simp only [BinaryOriginalReader.readOriginalRightProgram, BinaryCell.copy_view]
    unfold BinaryOriginalReader.selectRight
    dsimp only
    split
    · exact hdata _ r
    · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]
  · simp only [BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]

def rawReadBudget (L m B : ℕ) : ℕ :=
  64*(L+1)^2*(2^L+1)+BackendScalarBits.backendScalarUnit B+16*(L+1)^2+100*(L+m+1)^3

theorem storedRawLeftReader_cost {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q) (B : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs.size ≤ B) (hm : m ≤ L)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    (storedRawLeftReader good hg layout data Q bits outer h1 h2 r).operations ≤ rawReadBudget L m B := by
  unfold storedRawLeftReader
  split_ifs with hb
  · dsimp only
    have hQ : Q ∈ goodSlots L m := by rw [hg Q] at hb; exact of_decide_eq_true hb
    have h := BinaryOriginalReader.readOriginalLeftProgram_cost layout data 0
      (⟨Q,hQ⟩,(asCube (ThinMatrixBackend.compressOutsideProgram Q
        (goodSlots_size L m Q hQ) bits).value,outer)) (h1,h2) r B hdata hm
    change _ + 16*(L+1)^2+100*(L+m+1)^3 ≤ rawReadBudget L m B
    exact Nat.add_le_add_right (Nat.add_le_add_right h _) _
  · change 100*(L+m+1)^3 ≤ rawReadBudget L m B
    unfold rawReadBudget
    omega

theorem storedRawRightReader_cost {L m q : ℕ}
    (good : GoodStore L)
    (hg : ∀ Q, ThinMatrixBackend.readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q) (B : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs.size ≤ B) (hm : m ≤ L)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    (storedRawRightReader good hg layout data Q bits h1 h2 outer r).operations ≤ rawReadBudget L m B := by
  unfold storedRawRightReader
  split_ifs with hb
  · dsimp only
    have hQ : Q ∈ goodSlots L m := by rw [hg Q] at hb; exact of_decide_eq_true hb
    have h := BinaryOriginalReader.readOriginalRightProgram_cost layout data 0 (h1,h2)
      (⟨Q,hQ⟩,(asCube (ThinMatrixBackend.compressOutsideProgram Q
        (goodSlots_size L m Q hQ) bits).value,outer)) r B hdata hm
    change _ + 16*(L+1)^2+100*(L+m+1)^3 ≤ rawReadBudget L m B
    exact Nat.add_le_add_right (Nat.add_le_add_right h _) _
  · change 100*(L+m+1)^3 ≤ rawReadBudget L m B
    unfold rawReadBudget
    omega

structure Prepared (L m q : ℕ) where
  input : BinaryInputAdapter.InputStore L m q
  runs : Vector (BinarySourceFormation.RawStore L q) (2*m+1)
  inputOperations : ℕ
  sourceOperations : ℕ

def Prepared.operations {L m q : ℕ} (p : Prepared L m q) : ℕ := p.inputOperations+p.sourceOperations

def prepareLeft {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : StoredLeftMatrix L m q) : Prepared L m q :=
  let read := storedRawLeftReader shape.environment.good shape.good shape.layout data
  let input := BinaryInputAdapter.buildLeftAdapter read
  let sources := BinarySourceFormation.formLeftRuns shape.environment
    (BinaryInputAdapter.leftInputReader input.value)
  ⟨input.value,sources.value,input.operations,sources.operations⟩

def prepareRight {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : StoredRightMatrix L m q) : Prepared L m q :=
  let read := storedRawRightReader shape.environment.good shape.good shape.layout data
  let input := BinaryInputAdapter.buildRightAdapter read
  let sources := BinarySourceFormation.formRightRuns shape.environment
    (BinaryInputAdapter.rightInputReader input.value)
  ⟨input.value,sources.value,input.operations,sources.operations⟩

theorem cachedLeftReader_value {L m q : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredLeftMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    (BinarySourceFormation.semanticLeft
      (BinaryInputAdapter.leftInputReader (prepareLeft shape data).input) Q bits outer h1 h2 r).value =
      ThinMatrixBackend.rawLeft (ThinMatrixBackend.readLeftMatrix (BinaryOriginalReader.viewData data))
        Q bits outer h1 h2 r := by
  change BinaryCell.view (BinaryInputAdapter.leftInputReader
    (BinaryInputAdapter.buildLeftAdapter
      (storedRawLeftReader shape.environment.good shape.good shape.layout data)).value
    Q bits outer h1 h2 r).value = _
  simp only [BinaryInputAdapter.leftInputReader, BinaryCell.copy_view,
    BinaryInputAdapter.read_buildLeftAdapter, storedRawLeftReader_view]
  exact ThinMatrixBackend.storedRawLeftReader_value _ _ _ _ Q bits outer h1 h2 r

theorem cachedRightReader_value {L m q : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredRightMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    (BinarySourceFormation.semanticRight
      (BinaryInputAdapter.rightInputReader (prepareRight shape data).input) Q bits h1 h2 outer r).value =
      ThinMatrixBackend.rawRight (ThinMatrixBackend.readRightMatrix (BinaryOriginalReader.viewData data))
        Q bits h1 h2 outer r := by
  change BinaryCell.view (BinaryInputAdapter.rightInputReader
    (BinaryInputAdapter.buildRightAdapter
      (storedRawRightReader shape.environment.good shape.good shape.layout data)).value
    Q bits h1 h2 outer r).value = _
  simp only [BinaryInputAdapter.rightInputReader, BinaryCell.copy_view,
    BinaryInputAdapter.read_buildRightAdapter, storedRawRightReader_view]
  exact ThinMatrixBackend.storedRawRightReader_value _ _ _ _ Q bits h1 h2 outer r

theorem shape_good {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (n : Fin L → NormalLetter) :
    SourceFormation.readGood shape.environment.good n = decide (normalSupport n ∈ goodSlots L m) := by
  have hb : setBits (normalSupport n) = (fun i => decide (normalIsP (n i))) := by
    funext i
    simp [setBits, normalSupport]
  simpa only [ThinMatrixBackend.readGoodSet, SourceFormation.readGood, hb] using
    shape.good (normalSupport n)

theorem prepareLeft_run_view {L m t q : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredLeftMatrix L m q)
    (i : Fin (2*m+1)) :
    BinarySourceFormation.viewRaw ((prepareLeft shape data).runs.get i) =
      ((ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData data)).runs.get i).source := by
  have hv := BinarySourceFormation.formLeftSource_view shape.environment
    (BinaryInputAdapter.leftInputReader (prepareLeft shape data).input) i
  have hrun : (prepareLeft shape data).runs.get i =
      (BinarySourceFormation.formLeftSource shape.environment
        (BinaryInputAdapter.leftInputReader (prepareLeft shape data).input) i).value := by
    simp only [prepareLeft, BinarySourceFormation.formLeftRuns, vectorBuild_get]
  rw [hrun, hv]
  apply BinarySourceStorage.rawStore_ext
  intro normal opposite r
  change SourceFormation.readRaw _ normal opposite r = SourceFormation.readRaw _ normal opposite r
  have hs := SourceFormation.formLeftSource_correct shape.environment
    (BinarySourceFormation.semanticLeft
      (BinaryInputAdapter.leftInputReader (prepareLeft shape data).input))
    (ThinMatrixBackend.rawLeft (ThinMatrixBackend.readLeftMatrix (BinaryOriginalReader.viewData data)))
    (goodSlots L m) (shape_good shape) (cachedLeftReader_value shape data)
    (runValue m i) normal opposite r
  have hn := congrFun (congrFun
    (ThinMatrixBackend.prepareLeftBand_source (t := t) shape (BinaryOriginalReader.viewData data) i)
    (normal,opposite)) r
  change SourceFormation.readRaw _ normal opposite r = _ at hn
  rw [shape.gamma, shape.delta] at hs
  exact hs.trans hn.symm

theorem prepareRight_run_view {L m t q : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredRightMatrix L m q)
    (i : Fin (2*m+1)) :
    BinarySourceFormation.viewRaw ((prepareRight shape data).runs.get i) =
      ((ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData data)).runs.get i).source := by
  have hv := BinarySourceFormation.formRightSource_view shape.environment
    (BinaryInputAdapter.rightInputReader (prepareRight shape data).input) i
  have hrun : (prepareRight shape data).runs.get i =
      (BinarySourceFormation.formRightSource shape.environment
        (BinaryInputAdapter.rightInputReader (prepareRight shape data).input) i).value := by
    simp only [prepareRight, BinarySourceFormation.formRightRuns, vectorBuild_get]
  rw [hrun, hv]
  apply BinarySourceStorage.rawStore_ext
  intro normal opposite r
  change SourceFormation.readRaw _ normal opposite r = SourceFormation.readRaw _ normal opposite r
  have hs := SourceFormation.formRightSource_correct shape.environment
    (BinarySourceFormation.semanticRight
      (BinaryInputAdapter.rightInputReader (prepareRight shape data).input))
    (ThinMatrixBackend.rawRight (ThinMatrixBackend.readRightMatrix (BinaryOriginalReader.viewData data)))
    (goodSlots L m) (shape_good shape) (cachedRightReader_value shape data)
    (runValue m i) normal opposite r
  have hn := congrFun (congrFun
    (ThinMatrixBackend.prepareRightBand_source (t := t) shape (BinaryOriginalReader.viewData data) i)
    (normal,opposite)) r
  change SourceFormation.readRaw _ normal opposite r = _ at hn
  rw [shape.gamma, shape.delta] at hs
  exact hs.trans hn.symm

theorem prepareLeft_runs_view {L m t q : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredLeftMatrix L m q) :
    (prepareLeft shape data).runs.map BinarySourceFormation.viewRaw =
      (ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData data)).runs.map
        (fun run => run.source) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change BinarySourceFormation.viewRaw ((prepareLeft shape data).runs.get ⟨i,hi⟩) =
    ((ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData data)).runs.get ⟨i,hi⟩).source
  exact prepareLeft_run_view shape data ⟨i,hi⟩

theorem prepareRight_runs_view {L m t q : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredRightMatrix L m q) :
    (prepareRight shape data).runs.map BinarySourceFormation.viewRaw =
      (ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData data)).runs.map
        (fun run => run.source) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change BinarySourceFormation.viewRaw ((prepareRight shape data).runs.get ⟨i,hi⟩) =
    ((ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData data)).runs.get ⟨i,hi⟩).source
  exact prepareRight_run_view shape data ⟨i,hi⟩

def cachedReadBudget (L m B : ℕ) : ℕ := 8*(3*L+m+1)+BackendScalarBits.backendScalarUnit B

def preparationBudget (L m q B : ℕ) : ℕ :=
  BinaryInputAdapter.adapterBudget L m q (rawReadBudget L m B)+
    (SourceFormation.sourceBudget L m (L-m) q (cachedReadBudget L m B)+8)*(2*m+1)*
      BinarySourceFormation.bitUnit L (L-m) (2^B)

theorem prepareLeft_operations {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : StoredLeftMatrix L m q) :
    (prepareLeft shape data).operations =
      (BinaryInputAdapter.buildLeftAdapter
        (storedRawLeftReader shape.environment.good shape.good shape.layout data)).operations+
      (BinarySourceFormation.formLeftRuns shape.environment
        (BinaryInputAdapter.leftInputReader (prepareLeft shape data).input)).operations := rfl

theorem prepareRight_operations {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : StoredRightMatrix L m q) :
    (prepareRight shape data).operations =
      (BinaryInputAdapter.buildRightAdapter
        (storedRawRightReader shape.environment.good shape.good shape.layout data)).operations+
      (BinarySourceFormation.formRightRuns shape.environment
        (BinaryInputAdapter.rightInputReader (prepareRight shape data).input)).operations := rfl

theorem prepareLeft_cost {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : StoredLeftMatrix L m q) (B : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs.size ≤ B) (hm : m ≤ L) :
    (prepareLeft shape data).operations ≤ preparationBudget L m q B := by
  let read := storedRawLeftReader shape.environment.good shape.good shape.layout data
  let input := BinaryInputAdapter.buildLeftAdapter read
  have hw Q bits outer h1 h2 r :
      (BinaryCell.view (BinaryInputAdapter.readInput input.value Q bits outer h1 h2 r)).natAbs.size ≤ B := by
    simp only [input, BinaryInputAdapter.read_buildLeftAdapter]
    exact storedRawLeftReader_width _ _ _ data B hdata Q bits outer h1 h2 r
  have hc Q bits outer h1 h2 r :
      (BinaryInputAdapter.leftInputReader input.value Q bits outer h1 h2 r).operations ≤ cachedReadBudget L m B :=
    BinaryInputAdapter.leftInputReader_price input.value Q bits outer h1 h2 r B (hw Q bits outer h1 h2 r)
  have ha Q bits outer h1 h2 r :
      (BinaryInputAdapter.leftInputReader input.value Q bits outer h1 h2 r).value.view.natAbs ≤ 2^B := by
    change (BinaryCell.view (BinaryInputAdapter.leftInputReader input.value Q bits outer h1 h2 r).value).natAbs ≤ _
    simp only [BinaryInputAdapter.leftInputReader, BinaryCell.copy_view]
    exact Nat.le_of_lt (Nat.size_le.mp (hw Q bits outer h1 h2 r))
  have hi := BinaryInputAdapter.buildLeftAdapter_cost read (rawReadBudget L m B)
    (storedRawLeftReader_cost _ _ _ data B hdata hm)
  have hs := BinarySourceFormation.formLeftRuns_cost shape.environment
    (BinaryInputAdapter.leftInputReader input.value) hc ha
  exact Nat.add_le_add hi hs

theorem prepareRight_cost {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : StoredRightMatrix L m q) (B : ℕ)
    (hdata : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs.size ≤ B) (hm : m ≤ L) :
    (prepareRight shape data).operations ≤ preparationBudget L m q B := by
  let read := storedRawRightReader shape.environment.good shape.good shape.layout data
  let input := BinaryInputAdapter.buildRightAdapter read
  have hw Q bits h1 h2 outer r :
      (BinaryCell.view (BinaryInputAdapter.readInput input.value Q bits outer h1 h2 r)).natAbs.size ≤ B := by
    simp only [input, BinaryInputAdapter.read_buildRightAdapter]
    exact storedRawRightReader_width _ _ _ data B hdata Q bits h1 h2 outer r
  have hc Q bits h1 h2 outer r :
      (BinaryInputAdapter.rightInputReader input.value Q bits h1 h2 outer r).operations ≤ cachedReadBudget L m B :=
    BinaryInputAdapter.rightInputReader_price input.value Q bits h1 h2 outer r B (hw Q bits h1 h2 outer r)
  have ha Q bits h1 h2 outer r :
      (BinaryInputAdapter.rightInputReader input.value Q bits h1 h2 outer r).value.view.natAbs ≤ 2^B := by
    change (BinaryCell.view (BinaryInputAdapter.rightInputReader input.value Q bits h1 h2 outer r).value).natAbs ≤ _
    simp only [BinaryInputAdapter.rightInputReader, BinaryCell.copy_view]
    exact Nat.le_of_lt (Nat.size_le.mp (hw Q bits h1 h2 outer r))
  have hi := BinaryInputAdapter.buildRightAdapter_cost read (rawReadBudget L m B)
    (storedRawRightReader_cost _ _ _ data B hdata hm)
  have hs := BinarySourceFormation.formRightRuns_cost shape.environment
    (BinaryInputAdapter.rightInputReader input.value) hc ha
  exact Nat.add_le_add hi hs

end ThinMatrix.BinaryBandSource

#print axioms ThinMatrix.BinaryBandSource.storedRawLeftReader_view
#print axioms ThinMatrix.BinaryBandSource.storedRawRightReader_view
#print axioms ThinMatrix.BinaryBandSource.storedRawLeftReader_width
#print axioms ThinMatrix.BinaryBandSource.storedRawRightReader_width
#print axioms ThinMatrix.BinaryBandSource.storedRawLeftReader_natAbs
#print axioms ThinMatrix.BinaryBandSource.storedRawRightReader_natAbs
#print axioms ThinMatrix.BinaryBandSource.prepareLeft_runs_view
#print axioms ThinMatrix.BinaryBandSource.prepareRight_runs_view
#print axioms ThinMatrix.BinaryBandSource.prepareLeft_cost
#print axioms ThinMatrix.BinaryBandSource.prepareRight_cost


namespace ThinMatrix.BinaryBackendExecution

open SourceFormation
open ThinMatrixBackend
open BinaryCell
open scoped BigOperators

abbrev OriginalLeft (N D q : ℕ) := Vector (Vector BinaryCell.Cell q) (N*D)
abbrev OriginalRight (N D q : ℕ) := Vector (Vector BinaryCell.Cell q) (D*N)

def viewLeft {N D q : ℕ} (A : OriginalLeft N D q) : ThinMatrixBackend.OriginalLeft N D q :=
  BinaryOriginalReader.viewData A

def viewRight {N D q : ℕ} (B : OriginalRight N D q) : ThinMatrixBackend.OriginalRight N D q :=
  BinaryOriginalReader.viewData B

@[simp] theorem viewLeft_get {N D q : ℕ} (A : OriginalLeft N D q)
    (address : Fin (N*D)) (r : Fin q) :
    ((viewLeft A).get address).get r = BinaryCell.view ((A.get address).get r) := by
  simp [viewLeft, BinaryOriginalReader.viewData]

@[simp] theorem viewRight_get {N D q : ℕ} (B : OriginalRight N D q)
    (address : Fin (D*N)) (r : Fin q) :
    ((viewRight B).get address).get r = BinaryCell.view ((B.get address).get r) := by
  simp [viewRight, BinaryOriginalReader.viewData]


/-- A coefficient row is copied through actual bit primitives. -/
def copyRow {q : ℕ} (row : Vector BinaryCell.Cell q) : Program (Vector BinaryCell.Cell q) :=
  vectorBuild q fun r =>
    let copied := BinaryCell.copy (row.get r)
    ⟨copied.value,copied.bitSteps+1⟩

@[simp] theorem copyRow_view {q : ℕ} (row : Vector BinaryCell.Cell q) :
    (copyRow row).value.map BinaryCell.view = row.map BinaryCell.view := by
  apply Vector.ext
  intro i hi
  simp only [copyRow,vectorBuild,Vector.getElem_map,Vector.getElem_ofFn,BinaryCell.copy_view]
  rfl

theorem copyRow_work {q : ℕ} (row : Vector BinaryCell.Cell q) :
    (copyRow row).operations = ∑ r, ((BinaryCell.copy (row.get r)).bitSteps+1+8) := by
  simp [copyRow,vectorBuild,Finset.sum_add_distrib,Nat.mul_comm]

theorem copyRow_price {q : ℕ} (row : Vector BinaryCell.Cell q) (W : ℕ)
    (hr : ∀ r, (BinaryCell.view (row.get r)).natAbs.size ≤ W) :
    (copyRow row).operations ≤ (BackendScalarBits.backendScalarUnit W+9)*q := by
  apply vectorBuild_cost
  intro r
  have h := BinaryCell.copy_price W (row.get r) (hr r)
  change (BinaryCell.copy (row.get r)).bitSteps+1 ≤ BackendScalarBits.backendScalarUnit W+1
  omega

/-- Padded band copy, with runtime strides read from the stored width. -/
def makeLeftBandRuntime {N D m q : ℕ} (width : ℕ) (A : OriginalLeft N D q) (band : ℕ) :
    Program (Vector (Vector BinaryCell.Cell q) (width*4^m)) :=
  vectorBuild (width*4^m) fun address =>
    let pair := (finProdFinEquiv : Fin width × Fin (4^m) ≃ _).symm address
    let v := band*width+pair.1.val
    let row := if hv : v < N then
      if hh : pair.2.val < D then A.get (finProdFinEquiv (⟨v,hv⟩,⟨pair.2.val,hh⟩))
      else Vector.replicate q BinaryCell.zero
      else Vector.replicate q BinaryCell.zero
    let copied := copyRow row
    ⟨copied.value,copied.operations+16⟩

def makeRightBandRuntime {N D m q : ℕ} (width : ℕ) (B : OriginalRight N D q) (band : ℕ) :
    Program (Vector (Vector BinaryCell.Cell q) (4^m*width)) :=
  vectorBuild (4^m*width) fun address =>
    let pair := (finProdFinEquiv : Fin (4^m) × Fin width ≃ _).symm address
    let v := band*width+pair.2.val
    let row := if hv : v < N then
      if hh : pair.1.val < D then B.get (finProdFinEquiv (⟨pair.1.val,hh⟩,⟨v,hv⟩))
      else Vector.replicate q BinaryCell.zero
      else Vector.replicate q BinaryCell.zero
    let copied := copyRow row
    ⟨copied.value,copied.operations+16⟩

@[simp] theorem makeLeftBandRuntime_view {N D m q : ℕ} (width : ℕ)
    (A : OriginalLeft N D q) (band : ℕ) :
    BinaryOriginalReader.viewData (makeLeftBandRuntime (m := m) width A band).value =
      ThinMatrixBackend.makeLeftBandRuntime width (viewLeft A) band := by
  apply Vector.ext
  intro i hi
  change ((BinaryOriginalReader.viewData (makeLeftBandRuntime (m := m) width A band).value).get ⟨i,hi⟩) =
    (ThinMatrixBackend.makeLeftBandRuntime width (viewLeft A) band).get ⟨i,hi⟩
  simp only [BinaryOriginalReader.viewData,Vector.get_map,makeLeftBandRuntime,
    vectorBuild_get,ThinMatrixBackend.makeLeftBandRuntime,Vector.get_ofFn,copyRow_view]
  split <;> first | split <;> simp_all [viewLeft,BinaryOriginalReader.viewData,BinaryCell.zero_view] | simp_all [BinaryCell.zero_view]

@[simp] theorem makeRightBandRuntime_view {N D m q : ℕ} (width : ℕ)
    (B : OriginalRight N D q) (band : ℕ) :
    BinaryOriginalReader.viewData (makeRightBandRuntime (m := m) width B band).value =
      ThinMatrixBackend.makeRightBandRuntime width (viewRight B) band := by
  apply Vector.ext
  intro i hi
  change ((BinaryOriginalReader.viewData (makeRightBandRuntime (m := m) width B band).value).get ⟨i,hi⟩) =
    (ThinMatrixBackend.makeRightBandRuntime width (viewRight B) band).get ⟨i,hi⟩
  simp only [BinaryOriginalReader.viewData,Vector.get_map,makeRightBandRuntime,
    vectorBuild_get,ThinMatrixBackend.makeRightBandRuntime,Vector.get_ofFn,copyRow_view]
  split <;> first | split <;> simp_all [viewRight,BinaryOriginalReader.viewData,BinaryCell.zero_view] | simp_all [BinaryCell.zero_view]

abbrev StoredLeftMatrix (L m q : ℕ) := OriginalLeft (tileWidth L m) (4^m) q
abbrev StoredRightMatrix (L m q : ℕ) := OriginalRight (tileWidth L m) (4^m) q

def makeLeftBandStored {N D L m q : ℕ} (shape : ShapePlan L m)
    (A : OriginalLeft N D q) (band : ℕ) : Program (StoredLeftMatrix L m q) :=
  let built := makeLeftBandRuntime (m := m) shape.width A band
  ⟨Vector.cast (congrArg (fun w => w*4^m) shape.width_eq) built.value,built.operations⟩

def makeRightBandStored {N D L m q : ℕ} (shape : ShapePlan L m)
    (B : OriginalRight N D q) (band : ℕ) : Program (StoredRightMatrix L m q) :=
  let built := makeRightBandRuntime (m := m) shape.width B band
  ⟨Vector.cast (congrArg (fun w => 4^m*w) shape.width_eq) built.value,built.operations⟩

@[simp] theorem makeLeftBandStored_view {N D L m q : ℕ} (shape : ShapePlan L m)
    (A : OriginalLeft N D q) (band : ℕ) :
    BinaryOriginalReader.viewData (makeLeftBandStored shape A band).value =
      ThinMatrixBackend.makeLeftBandStored shape (viewLeft A) band := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  exact makeLeftBandRuntime_view _ A band

@[simp] theorem makeRightBandStored_view {N D L m q : ℕ} (shape : ShapePlan L m)
    (B : OriginalRight N D q) (band : ℕ) :
    BinaryOriginalReader.viewData (makeRightBandStored shape B band).value =
      ThinMatrixBackend.makeRightBandStored shape (viewRight B) band := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  exact makeRightBandRuntime_view _ B band


/-- A shared row/column band retains every Walsh source and every LOW
encoder trace; HIGH preparation below reads these already stored sources. -/
structure PreparedBand (L m q : ℕ) where
  sources : BinaryBandSource.Prepared L m q
  low : Vector (BinaryLowEncoder.Prepared L q (2*m+1)) (2*m+1)
  bitSteps : ℕ

def prepareLeftBand {L m t q : ℕ} (W : ℕ) (shape : ShapePlan L m)
    (data : StoredLeftMatrix L m q) : PreparedBand L m q :=
  let sources := BinaryBandSource.prepareLeft shape data
  let low := sources.runs.map (BinaryLowEncoder.prepareRawSource (m := m) (t := t) W true)
  { sources := sources,low := low
    bitSteps := sources.operations+(∑ i, (low.get i).bitSteps)+8*(2*m+1) }

def prepareRightBand {L m t q : ℕ} (W : ℕ) (shape : ShapePlan L m)
    (data : StoredRightMatrix L m q) : PreparedBand L m q :=
  let sources := BinaryBandSource.prepareRight shape data
  let low := sources.runs.map (BinaryLowEncoder.prepareRawSource (m := m) (t := t) W false)
  { sources := sources,low := low
    bitSteps := sources.operations+(∑ i, (low.get i).bitSteps)+8*(2*m+1) }

def BandRefines {L m q : ℕ} (binary : PreparedBand L m q)
    (native : ThinMatrixBackend.PreparedBand L m q) : Prop :=
  ∀ i, BinarySourceFormation.viewRaw (binary.sources.runs.get i) = (native.runs.get i).source ∧
    BinaryLowQuery.CacheRefines (binary.low.get i).table (native.runs.get i).cache

theorem prepareLeftBand_refines {L m t q : ℕ} [NeZero q] (W : ℕ) (shape : ShapePlan L m)
    (data : StoredLeftMatrix L m q) :
    BandRefines (prepareLeftBand (t := t) W shape data)
      (ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData data)) := by
  intro i
  have hsource := BinaryBandSource.prepareLeft_run_view (t := t) shape data i
  refine ⟨hsource,?_⟩
  simp only [prepareLeftBand,Vector.get_map]
  rw [ThinMatrixBackend.prepareLeftBand_cache]
  have hc := BinaryLowEncoder.prepareRawSource_cacheRefines (m := m) (t := t) W true
    ((BinaryBandSource.prepareLeft shape data).runs.get i)
  rw [hsource] at hc
  exact hc

theorem prepareRightBand_refines {L m t q : ℕ} [NeZero q] (W : ℕ) (shape : ShapePlan L m)
    (data : StoredRightMatrix L m q) :
    BandRefines (prepareRightBand (t := t) W shape data)
      (ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData data)) := by
  intro i
  have hsource := BinaryBandSource.prepareRight_run_view (t := t) shape data i
  refine ⟨hsource,?_⟩
  simp only [prepareRightBand,Vector.get_map]
  rw [ThinMatrixBackend.prepareRightBand_cache]
  have hc := BinaryLowEncoder.prepareRawSource_cacheRefines (m := m) (t := t) W false
    ((BinaryBandSource.prepareRight shape data).runs.get i)
  rw [hsource] at hc
  exact hc

/-- Both ordinary HIGH encoders and the actual FFT/DP execution are
retained. No callback is re-evaluated to recover a work counter. -/
structure PreparedHigh (L m t q : ℕ) where
  left : BinaryHighExecution.StoredEncoding q (2*L)
  right : BinaryHighExecution.StoredEncoding q (2*L)
  high : BinaryHighTable.Result (BinaryHighTable.Table q)
  bitSteps : ℕ

def prepareHigh {L m t q : ℕ} (A : ℕ)
    (X Y : BinarySourceFormation.RawStore L q) : PreparedHigh L m t q :=
  let left := BinaryHighExecution.encodeRawSource L m t q true X
  let right := BinaryHighExecution.encodeRawSource L m t q false Y
  let high := BinaryHighTable.prepare (L := L) (m := m) (t := t)
    (AdaptiveBitBounds.highInputBudget L m A) left.table right.table
  ⟨left,right,high,left.bitSteps+right.bitSteps+high.work+8⟩

structure PreparedTile (L m t q : ℕ) where
  runs : Vector (PreparedHigh L m t q) (2*m+1)
  bitSteps : ℕ

def prepareTile {L m t q : ℕ} (A : ℕ) (left right : PreparedBand L m q) :
    PreparedTile L m t q :=
  let runs := Vector.ofFn (fun i : Fin (2*m+1) => prepareHigh (t := t) A
    (left.sources.runs.get i) (right.sources.runs.get i))
  ⟨runs,(∑ i, (runs.get i).bitSteps)+8*(2*m+1)⟩

/-- LOW query inputs are two shared, prepared band caches. -/
def bandRunCaches {L m q : ℕ} (left right : PreparedBand L m q) :
    BinaryLowQuery.RunCaches L m q (2*m+1) :=
  Vector.ofFn (fun i => ((left.low.get i).table,(right.low.get i).table))

theorem bandRunCaches_refines {L m q : ℕ} (left right : PreparedBand L m q)
    (nativeLeft nativeRight : ThinMatrixBackend.PreparedBand L m q)
    (hl : BandRefines left nativeLeft) (hr : BandRefines right nativeRight) (i : Fin (2*m+1)) :
    BinaryLowQuery.CacheRefines ((bandRunCaches left right).get i).1
        ((ThinMatrixBackend.bandRunCaches nativeLeft nativeRight).get i).1 ∧
    BinaryLowQuery.CacheRefines ((bandRunCaches left right).get i).2
        ((ThinMatrixBackend.bandRunCaches nativeLeft nativeRight).get i).2 := by
  simpa only [bandRunCaches,ThinMatrixBackend.bandRunCaches,Vector.get_ofFn] using
    And.intro (hl i).2 (hr i).2

/-- Global sharing: sources and LOW encoders are prepared once per band;
HIGH tables are prepared once per pair of bands and matching run. -/
structure PreparedGlobal (N D L m t q : ℕ) where
  shape : ShapePlan L m
  leftData : Vector (Program (StoredLeftMatrix L m q)) (TilingCosts.bandCount N (tileWidth L m))
  rightData : Vector (Program (StoredRightMatrix L m q)) (TilingCosts.bandCount N (tileWidth L m))
  left : Vector (PreparedBand L m q) (TilingCosts.bandCount N (tileWidth L m))
  right : Vector (PreparedBand L m q) (TilingCosts.bandCount N (tileWidth L m))
  tiles : Vector (Vector (PreparedTile L m t q) (TilingCosts.bandCount N (tileWidth L m)))
    (TilingCosts.bandCount N (tileWidth L m))
  bitSteps : ℕ

/-- Shape data is an already produced public control payload. Its actual
construction counter is included once, alongside all subsequent bit work. -/
def prepareGlobalShape {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q) : PreparedGlobal N D L m t q :=
  let bands := TilingCosts.bandCount N shape.width
  let hbands : bands = TilingCosts.bandCount N (tileWidth L m) := congrArg (TilingCosts.bandCount N) shape.width_eq
  let leftData := Vector.ofFn (n := bands) (fun b => makeLeftBandStored shape inputLeft b.val)
  let rightData := Vector.ofFn (n := bands) (fun b => makeRightBandStored shape inputRight b.val)
  let left := leftData.map (fun data => prepareLeftBand (t := t) W shape data.value)
  let right := rightData.map (fun data => prepareRightBand (t := t) W shape data.value)
  let tiles := Vector.ofFn (n := bands) (fun b => Vector.ofFn (n := bands)
    (fun c => prepareTile (t := t) A (left.get b) (right.get c)))
  { shape := shape
    leftData := Vector.cast hbands leftData
    rightData := Vector.cast hbands rightData
    left := Vector.cast hbands left
    right := Vector.cast hbands right
    tiles := Vector.cast hbands (tiles.map (Vector.cast hbands))
    bitSteps := shape.operations+(∑ b, (leftData.get b).operations)+
      (∑ b, (rightData.get b).operations)+(∑ b, (left.get b).bitSteps)+
      (∑ b, (right.get b).bitSteps)+(∑ b, ∑ c, ((tiles.get b).get c).bitSteps)+32*bands }


@[simp] theorem prepareGlobalShape_shape {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q) :
    (prepareGlobalShape (t := t) shape W A inputLeft inputRight).shape = shape := rfl

@[simp] theorem prepareGlobalShape_left {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    (prepareGlobalShape (t := t) shape W A inputLeft inputRight).left.get b =
      prepareLeftBand (t := t) W shape (makeLeftBandStored shape inputLeft b.val).value := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  simp [prepareGlobalShape,Vector.cast_rfl]

@[simp] theorem prepareGlobalShape_right {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    (prepareGlobalShape (t := t) shape W A inputLeft inputRight).right.get b =
      prepareRightBand (t := t) W shape (makeRightBandStored shape inputRight b.val).value := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  simp [prepareGlobalShape,Vector.cast_rfl]

@[simp] theorem prepareGlobalShape_tile {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q)
    (b c : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    ((prepareGlobalShape (t := t) shape W A inputLeft inputRight).tiles.get b).get c =
      prepareTile (t := t) A
        (prepareLeftBand (t := t) W shape (makeLeftBandStored shape inputLeft b.val).value)
        (prepareRightBand (t := t) W shape (makeRightBandStored shape inputRight c.val).value) := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  simp [prepareGlobalShape,Vector.cast_rfl]

/-- The work field is the sum over the exact retained preparation payload.
The right side is a proof-only traversal and never invokes an encoder. -/
theorem prepareGlobalShape_work {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q) :
    let p := prepareGlobalShape (t := t) shape W A inputLeft inputRight
    p.bitSteps = shape.operations+(∑ b, (p.leftData.get b).operations)+
      (∑ b, (p.rightData.get b).operations)+(∑ b, (p.left.get b).bitSteps)+
      (∑ b, (p.right.get b).bitSteps)+(∑ b, ∑ c, ((p.tiles.get b).get c).bitSteps)+
      32*TilingCosts.bandCount N (tileWidth L m) := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  simp [prepareGlobalShape,Vector.cast_rfl]

end ThinMatrix.BinaryBackendExecution

#print axioms ThinMatrix.BinaryBackendExecution.viewLeft_get
#print axioms ThinMatrix.BinaryBackendExecution.viewRight_get

#print axioms ThinMatrix.BinaryBackendExecution.prepareLeftBand_refines
#print axioms ThinMatrix.BinaryBackendExecution.prepareRightBand_refines
#print axioms ThinMatrix.BinaryBackendExecution.bandRunCaches_refines

namespace ThinMatrix.BinaryBandBounds

open BinaryBandSource SourceFormation WalshEmbedding CoefficientBounds
open scoped BigOperators

theorem viewData_abs_bound {len q A : ℕ} (data : Vector (Vector BinaryCell.Cell q) len)
    (hd : ∀ i r, (BinaryCell.view ((data.get i).get r)).natAbs ≤ A) :
    ∀ i r, |((BinaryOriginalReader.viewData data).get i).get r| ≤ (A : ℤ) := by
  intro i r
  simp only [BinaryOriginalReader.viewData, Vector.get_map]
  rw [← Int.natCast_natAbs]
  exact_mod_cast hd i r

theorem left_source_coeffBound {q L m A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, (BinaryCell.view ((data.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1)) :
    ∀ a, CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw ((prepareLeft shape data).runs.get run)) a)
      (2^(L+m)*A) := by
  rw [prepareLeft_run_view (t := 0)]
  exact AdaptiveBitBounds.prepared_left_source_bound shape (BinaryOriginalReader.viewData data)
    (viewData_abs_bound data hd) run

theorem right_source_coeffBound {q L m A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, (BinaryCell.view ((data.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1)) :
    ∀ a, CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw ((prepareRight shape data).runs.get run)) a)
      (2^(L+m)*A) := by
  rw [prepareRight_run_view (t := 0)]
  exact AdaptiveBitBounds.prepared_right_source_bound shape (BinaryOriginalReader.viewData data)
    (viewData_abs_bound data hd) run

theorem left_source_natAbs {q L m A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, (BinaryCell.view ((data.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (r : Fin q) :
    (BinarySourceFormation.readRaw ((prepareLeft shape data).runs.get run) normal opposite r).view.natAbs ≤
      2^(L+m)*A := by
  have h := left_source_coeffBound shape data hd run (normal,opposite) r
  change |SourceFormation.readRaw _ normal opposite r| ≤ _ at h
  rw [BinarySourceFormation.readRaw_view, ← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem right_source_natAbs {q L m A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, (BinaryCell.view ((data.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (r : Fin q) :
    (BinarySourceFormation.readRaw ((prepareRight shape data).runs.get run) normal opposite r).view.natAbs ≤
      2^(L+m)*A := by
  have h := right_source_coeffBound shape data hd run (normal,opposite) r
  change |SourceFormation.readRaw _ normal opposite r| ≤ _ at h
  rw [BinarySourceFormation.readRaw_view, ← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem left_high_operand_bound {q L m t A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, (BinaryCell.view ((data.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1))
    (w : HighBoxDP.BaseStates L m t) :
    BinaryHighTable.VectorBound (AdaptiveBitBounds.highInputBudget L m A)
      (BinaryHighTable.readBase
        (BinaryHighExecution.encodeRawSource L m t q true ((prepareLeft shape data).runs.get run)).table w).1 := by
  intro r
  have hv := BinaryHighExecution.encodeRawSource_readBase_view L m t q true
    ((prepareLeft shape data).runs.get run) w
  rw [prepareLeft_run_view (t := t)] at hv
  have hr := congrArg (fun v : Vector ℤ q => v.get r) hv
  simp only [BinaryHighExecution.payloadView, Vector.get_map, if_true] at hr
  have hc := AdaptiveBitBounds.prepared_left_operand_bound shape (BinaryOriginalReader.viewData data)
    (viewData_abs_bound data hd) run w r
  change (BinaryCell.view ((BinaryHighExecution.readBase
    (BinaryHighExecution.encodeRawSource L m t q true ((prepareLeft shape data).runs.get run))
    (ArrayKeys.materialize w.val)).value.get r)).natAbs ≤ _
  rw [hr]
  exact hc

theorem right_high_operand_bound {q L m t A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, (BinaryCell.view ((data.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1))
    (w : HighBoxDP.BaseStates L m t) :
    BinaryHighTable.VectorBound (AdaptiveBitBounds.highInputBudget L m A)
      (BinaryHighTable.readBase
        (BinaryHighExecution.encodeRawSource L m t q false ((prepareRight shape data).runs.get run)).table w).1 := by
  intro r
  have hv := BinaryHighExecution.encodeRawSource_readBase_view L m t q false
    ((prepareRight shape data).runs.get run) w
  rw [prepareRight_run_view (t := t)] at hv
  have hr := congrArg (fun v : Vector ℤ q => v.get r) hv
  simp only [BinaryHighExecution.payloadView, Vector.get_map] at hr
  have hc := AdaptiveBitBounds.prepared_right_operand_bound shape (BinaryOriginalReader.viewData data)
    (viewData_abs_bound data hd) run w r
  change (BinaryCell.view ((BinaryHighExecution.readBase
    (BinaryHighExecution.encodeRawSource L m t q false ((prepareRight shape data).runs.get run))
    (ArrayKeys.materialize w.val)).value.get r)).natAbs ≤ _
  rw [hr]
  exact hc

/-- The actual HIGH preparation is instantiated only with produced binary
source tables; its FFT and stored layer counters remain in the result. -/
def prepareHigh {q L m t : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q) (run : Fin (2*m+1)) (A : ℕ) :=
  (BinaryBackendExecution.prepareHigh (L := L) (m := m) (t := t) (q := q) A
    ((prepareLeft shape left).runs.get run) ((prepareRight shape right).runs.get run)).high

theorem prepareHigh_work {q L m t A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1)) :
    (prepareHigh (t := t) shape left right run A).work ≤
      BinaryHighTable.preparationBudget L m t q (AdaptiveBitBounds.highInputBudget L m A) := by
  exact BinaryHighTable.prepare_work _ (AdaptiveBitBounds.highInputBudget_pos L m A hA) _ _
    (left_high_operand_bound shape left hl run) (right_high_operand_bound shape right hr run)

theorem prepareHigh_bound {q L m t A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A) (run : Fin (2*m+1)) :
    BinaryHighTable.Bounds.TableBound
      (5^(2*L+1)*(q*(AdaptiveBitBounds.highInputBudget L m A)^2))
      (prepareHigh (t := t) shape left right run A).value := by
  exact BinaryHighTable.prepare_bound _ (AdaptiveBitBounds.highInputBudget_pos L m A hA) _ _
    (left_high_operand_bound shape left hl run) (right_high_operand_bound shape right hr run)

end ThinMatrix.BinaryBandBounds

#print axioms ThinMatrix.BinaryBandBounds.left_source_natAbs
#print axioms ThinMatrix.BinaryBandBounds.right_source_natAbs
#print axioms ThinMatrix.BinaryBandBounds.left_high_operand_bound
#print axioms ThinMatrix.BinaryBandBounds.right_high_operand_bound
#print axioms ThinMatrix.BinaryBandBounds.prepareHigh_work
#print axioms ThinMatrix.BinaryBandBounds.prepareHigh_bound


namespace ThinMatrix.BinaryHighCorrectness

open CompleteThinProduct HighBoxDP
open scoped BigOperators

noncomputable def leftTransform {L q : ℕ} [NeZero q]
    (X : SourceWord L → CyclicRing.Cyclic q) (v : LeafWord (2*L)) : Vector ℤ q :=
  Vector.ofFn (fun r => (∑ a : SourceWord L, X a * ∏ i, sourceF i (v i) a) r)

noncomputable def rightTransform {L q : ℕ} [NeZero q]
    (Y : SourceWord L → CyclicRing.Cyclic q) (v : LeafWord (2*L)) : Vector ℤ q :=
  Vector.ofFn (fun r => (∑ a : SourceWord L, Y a * ∏ i, sourceG i (v i) a) r)

theorem left_base_projection {L m t q : ℕ} [NeZero q]
    (raw : BinarySourceFormation.RawStore L q) (w : BaseStates L m t) :
    BinaryHighTable.vectorView
      (BinaryHighTable.readBase (BinaryHighExecution.encodeRawSource L m t q true raw).table w).1 =
      leftTransform (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))
        (baseLeaf w.val w.property.2) := by
  have he : BinaryHighTable.vectorView
      (BinaryHighTable.readBase (BinaryHighExecution.encodeRawSource L m t q true raw).table w).1 =
      HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m := m) (t := t)
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))) w :=
    BinaryHighExecution.encodeRawSource_readBase_view L m t q true raw w
  rw [he]
  apply Vector.ext
  intro r hr
  change (HighBaseEncoder.readBase _ w).get ⟨r,hr⟩ =
    (leftTransform _ (baseLeaf w.val w.property.2)).get ⟨r,hr⟩
  simp only [leftTransform, Vector.get_ofFn]
  exact HighBaseEncoder.encodeLeftSource_read _ w ⟨r,hr⟩

theorem right_base_projection {L m t q : ℕ} [NeZero q]
    (raw : BinarySourceFormation.RawStore L q) (w : BaseStates L m t) :
    BinaryHighTable.vectorView
      (BinaryHighTable.readBase (BinaryHighExecution.encodeRawSource L m t q false raw).table w).1 =
      rightTransform (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))
        (baseLeaf w.val w.property.2) := by
  have he : BinaryHighTable.vectorView
      (BinaryHighTable.readBase (BinaryHighExecution.encodeRawSource L m t q false raw).table w).1 =
      HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m := m) (t := t)
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))) w :=
    BinaryHighExecution.encodeRawSource_readBase_view L m t q false raw w
  rw [he]
  apply Vector.ext
  intro r hr
  change (HighBaseEncoder.readBase _ w).get ⟨r,hr⟩ =
    (rightTransform _ (baseLeaf w.val w.property.2)).get ⟨r,hr⟩
  simp only [rightTransform, Vector.get_ofFn]
  exact HighBaseEncoder.encodeRightSource_read _ w ⟨r,hr⟩

theorem convolution_transform {L q : ℕ} [NeZero q]
    (X Y : SourceWord L → CyclicRing.Cyclic q) (v : LeafWord (2*L)) (r : Fin q) :
    CyclicRing.convolution (leftTransform X v).get (rightTransform Y v).get r =
      globalLeaf X Y sourceF sourceG v r := by
  have hl : (leftTransform X v).get = ∑ a : SourceWord L, X a * ∏ i, sourceF i (v i) a := by
    funext s
    exact Vector.get_ofFn _ s
  have hr : (rightTransform Y v).get = ∑ a : SourceWord L, Y a * ∏ i, sourceG i (v i) a := by
    funext s
    exact Vector.get_ofFn _ s
  rw [hl, hr, ← CyclicRing.mul_eq_convolution]
  rfl

/-- Every selected retained HIGH state is exactly the native state for the
same already formed binary sources, with original stored-cell bounds only. -/
theorem prepareHigh_lookup_correct {q L m t A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBandSource.StoredLeftMatrix L m q)
    (right : BinaryBandSource.StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (run : Fin (2*m+1)) (M : ThinMatrixBackend.FullMultiplier q)
    (w : States L m t) (r : Fin q) :
    let X := (BinaryBandSource.prepareLeft shape left).runs.get run
    let Y := (BinaryBandSource.prepareRight shape right).runs.get run
    ((BinaryHighTable.lookup
      (BinaryBackendExecution.prepareHigh (L := L) (m := m) (t := t) A X Y).high.value
      (ArrayKeys.materialize w.val)).get r).view =
      (StoredHighDP.lookup
        (ThinMatrixBackend.prepareHigh (m := m) (t := t) M
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw X))
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw Y))).table w.val).get r := by
  let X := (BinaryBandSource.prepareLeft shape left).runs.get run
  let Y := (BinaryBandSource.prepareRight shape right).runs.get run
  let XS := ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw X)
  let YS := ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw Y)
  have hb := BinaryHighTable.prepare_source_complete
    (L := L) (m := m) (t := t) (AdaptiveBitBounds.highInputBudget L m A)
    (AdaptiveBitBounds.highInputBudget_pos L m A hA)
    (BinaryHighExecution.encodeRawSource L m t q true X).table
    (BinaryHighExecution.encodeRawSource L m t q false Y).table
    (leftTransform XS) (rightTransform YS)
    (BinaryBandBounds.left_high_operand_bound shape left hl run)
    (BinaryBandBounds.right_high_operand_bound shape right hr run)
    (left_base_projection X) (right_base_projection Y) w r
  have hn := ThinMatrixBackend.prepareHigh_coefficient (m := m) (t := t) M XS YS w r
  rw [tableAfter_complete] at hn
  calc
    _ = boxValue w.val (fun v => CyclicRing.convolution (leftTransform XS v).get (rightTransform YS v).get r) := hb
    _ = boxValue w.val (fun v => globalLeaf XS YS sourceF sourceG v r) := by
      congr 1
      funext v
      exact convolution_transform XS YS v r
    _ = _ := hn.symm

theorem prepareHigh_lookup_vector {q L m t A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBandSource.StoredLeftMatrix L m q)
    (right : BinaryBandSource.StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (run : Fin (2*m+1)) (M : ThinMatrixBackend.FullMultiplier q) (w : States L m t) :
    let X := (BinaryBandSource.prepareLeft shape left).runs.get run
    let Y := (BinaryBandSource.prepareRight shape right).runs.get run
    BinaryHighTable.vectorView (BinaryHighTable.lookup
      (BinaryBackendExecution.prepareHigh (L := L) (m := m) (t := t) A X Y).high.value
      (ArrayKeys.materialize w.val)) =
      StoredHighDP.lookup
        (ThinMatrixBackend.prepareHigh (m := m) (t := t) M
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw X))
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw Y))).table w.val := by
  apply Vector.ext
  intro r hq
  simp only [BinaryHighTable.vectorView, Vector.getElem_map]
  exact prepareHigh_lookup_correct shape left right hA hl hr run M w ⟨r,hq⟩

end ThinMatrix.BinaryHighCorrectness

#print axioms ThinMatrix.BinaryHighCorrectness.left_base_projection
#print axioms ThinMatrix.BinaryHighCorrectness.right_base_projection
#print axioms ThinMatrix.BinaryHighCorrectness.prepareHigh_lookup_correct
#print axioms ThinMatrix.BinaryHighCorrectness.prepareHigh_lookup_vector


namespace ThinMatrix.BinaryBackendExecution
open SourceFormation WalshEmbedding GoodMapEmbedding CompleteThinProduct ThinMatrixBackend
open HighBoxDP
open scoped BigOperators

/-- Computable sorted finite physical positions. The semantic definition
has the same body; no integer coefficient is read to construct positions. -/
def physicalEmbeddingRuntime {L m : ℕ} (QL QR : Finset (Fin L))
    (hQL : QL.card=m) (hQR : QR.card=m) : Fin (2*m) ↪o Fin (2*L) :=
  (CompleteThinProduct.physicalSupport QL QR).orderEmbOfFin
    (CompleteThinProduct.physicalSupport_card QL QR hQL hQR)

def queryGeometry {L m : ℕ}
    (environment : SourceFormation.Environment L m (L-m))
    (row col : OuterIndex L m) : ThinMatrixBackend.QueryMetadata L m :=
  let hL := goodSlots_size L m row.1.val row.1.property
  let hR := goodSlots_size L m col.1.val col.1.property
  let iL := ThinMatrixBackend.expandOutsideVector row.1.val hL row.2.1
  let iR := ThinMatrixBackend.expandOutsideVector col.1.val hR col.2.1
  let jL := Vector.ofFn (fun i => dotBits (fun j => (environment.deltaColumns.get i).get j) col.2.2)
  let jR := Vector.ofFn (fun i => dotBits (fun j => (environment.deltaColumns.get i).get j) row.2.2)
  let outside := Vector.ofFn (sourceOutside iL.get iR.get jL.get jR.get)
  { embedding := physicalEmbeddingRuntime row.1.val col.1.val hL hR
    outside := outside.get
    left_cap := by
      change ((embeddedSupport (physicalEmbedding row.1.val col.1.val hL hR)).filter _).card ≤ m
      rw [physicalEmbedding_support,physicalSupport_left_card row.1.val col.1.val hL]
    right_cap := by
      change ((embeddedSupport (physicalEmbedding row.1.val col.1.val hL hR)).filter _).card ≤ m
      rw [physicalEmbedding_support,physicalSupport_right_card row.1.val col.1.val hR] }

@[simp] theorem queryGeometry_refines {L m : ℕ}
    (environment : SourceFormation.Environment L m (L-m)) (row col : OuterIndex L m) :
    queryGeometry environment row col = ThinMatrixBackend.storedQueryGeometry environment row col := rfl

/-- Store each same-run HIGH scalar result once before summing its cells
and reading its counter. The sum performs actual binary additions. -/
def sumQueryRows {runs : ℕ} (rows : Vector (ToomCook.Counted BinaryCell.Cell) runs) :
    ToomCook.Counted BinaryCell.Cell :=
  let summed := BinaryHighTable.sumCells (rows.toList.map (fun row => row.value))
  ⟨summed.value,(rows.toList.map (fun row => row.operations)).sum+summed.operations+8*runs⟩

@[simp] theorem sumQueryRows_view {runs : ℕ} (rows : Vector (ToomCook.Counted BinaryCell.Cell) runs) :
    (sumQueryRows rows).value.view = ∑ i, (rows.get i).value.view := by
  simp only [sumQueryRows,BinaryHighTable.sumCells_view,List.map_map,Function.comp_def]
  have hv : rows = Vector.ofFn (fun i => rows.get i) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rfl
  have hl : rows.toList = List.ofFn (fun i => rows.get i) := by
    rw [← Vector.toList_ofFn]
    exact congrArg Vector.toList hv
  rw [hl,List.map_ofFn,List.sum_ofFn]
  rfl

structure TileQuery (L m t q : ℕ) where
  metadata : ThinMatrixBackend.QueryMetadata L m
  highRows : Vector (ToomCook.Counted BinaryCell.Cell) (2*m+1)
  high : ToomCook.Counted BinaryCell.Cell
  complete : ToomCook.Counted BinaryCell.Cell
  result : ToomCook.Counted BinaryCell.Cell

def queryTileExecution {L m t q : ℕ} [NeZero q] (shape : ThinMatrixBackend.ShapePlan L m)
    (left right : PreparedBand L m q) (tile : PreparedTile L m t q)
    (row col : OuterIndex L m) (r : Fin q) : TileQuery L m t q :=
  let d := queryGeometry shape.environment row col
  let highRows := Vector.ofFn (fun i : Fin (2*m+1) => BinaryHighTable.query t d.embedding
    (Vector.ofFn d.outside) (tile.runs.get i).high.value r)
  let high := sumQueryRows highRows
  let complete := BinaryLowQuery.queryCell t (Vector.ofFn d.embedding) (Vector.ofFn d.outside)
    (bandRunCaches left right) r high
  ⟨d,highRows,high,complete,⟨complete.value,complete.operations+1000*(L+m+1)^5⟩⟩

def queryTile {L m t q : ℕ} [NeZero q] (shape : ThinMatrixBackend.ShapePlan L m)
    (left right : PreparedBand L m q) (tile : PreparedTile L m t q)
    (row col : OuterIndex L m) (r : Fin q) : ToomCook.Counted BinaryCell.Cell :=
  (queryTileExecution shape left right tile row col r).result

/-- A global query retains the actual tile-level execution and its result.
Address/control fields are public finite indices; coefficient arithmetic
is performed by the stored binary query and the complete binary division. -/
structure GlobalQuery (L m t q : ℕ) where
  tile : TileQuery L m t q
  result : ToomCook.Counted BinaryCell.Cell

def queryGlobalExecution {N D L m t q : ℕ} [NeZero q] (hB : 0 < ThinMatrixBackend.tileWidth L m)
    (prepared : PreparedGlobal N D L m t q) (i j : Fin N) (r : Fin q) : GlobalQuery L m t q :=
  let bi := ThinMatrixBackend.storedLocate prepared.shape hB i
  let bj := ThinMatrixBackend.storedLocate prepared.shape hB j
  let row := RowIndexing.rowUnrank prepared.shape.layout bi.2
  let col := RowIndexing.rowUnrank prepared.shape.layout bj.2
  let result := queryTileExecution prepared.shape (prepared.left.get bi.1) (prepared.right.get bj.1)
    ((prepared.tiles.get bi.1).get bj.1) row col r
  ⟨result,⟨result.result.value,result.result.operations+1000*(L+m+N.log2+1)^5⟩⟩

def queryGlobal {N D L m t q : ℕ} [NeZero q] (hB : 0 < ThinMatrixBackend.tileWidth L m)
    (prepared : PreparedGlobal N D L m t q) (i j : Fin N) (r : Fin q) : ToomCook.Counted BinaryCell.Cell :=
  (queryGlobalExecution hB prepared i j r).result

end ThinMatrix.BinaryBackendExecution

namespace ThinMatrix.BinaryBandCopyBounds

open BinaryBackendExecution SourceFormation

theorem makeLeftBandRuntime_natAbs {N D m q A : ℕ} (width : ℕ)
    (input : OriginalLeft N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A)
    (address : Fin (width*4^m)) (r : Fin q) :
    (BinaryCell.view (((makeLeftBandRuntime (m := m) width input band).value.get address).get r)).natAbs ≤ A := by
  simp only [makeLeftBandRuntime, vectorBuild_get, copyRow, BinaryCell.copy_view]
  split_ifs
  · exact hd _ r
  · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]
  · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]

theorem makeRightBandRuntime_natAbs {N D m q A : ℕ} (width : ℕ)
    (input : OriginalRight N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A)
    (address : Fin (4^m*width)) (r : Fin q) :
    (BinaryCell.view (((makeRightBandRuntime (m := m) width input band).value.get address).get r)).natAbs ≤ A := by
  simp only [makeRightBandRuntime, vectorBuild_get, copyRow, BinaryCell.copy_view]
  split_ifs
  · exact hd _ r
  · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]
  · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.zero_le]

theorem makeLeftBandRuntime_price {N D m q A : ℕ} (width : ℕ)
    (input : OriginalLeft N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A) :
    (makeLeftBandRuntime (m := m) width input band).operations ≤
      ((BackendScalarBits.backendScalarUnit A.size+9)*q+24)*(width*4^m) := by
  unfold makeLeftBandRuntime
  calc
    _ ≤ (((BackendScalarBits.backendScalarUnit A.size+9)*q+16)+8)*(width*4^m) := by
      apply vectorBuild_cost
      intro address
      dsimp only
      apply Nat.add_le_add_right
      apply copyRow_price
      intro r
      split_ifs
      · exact Nat.size_le_size (hd _ r)
      · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]
      · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]
    _ = _ := by rfl

theorem makeRightBandRuntime_price {N D m q A : ℕ} (width : ℕ)
    (input : OriginalRight N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A) :
    (makeRightBandRuntime (m := m) width input band).operations ≤
      ((BackendScalarBits.backendScalarUnit A.size+9)*q+24)*(4^m*width) := by
  unfold makeRightBandRuntime
  calc
    _ ≤ (((BackendScalarBits.backendScalarUnit A.size+9)*q+16)+8)*(4^m*width) := by
      apply vectorBuild_cost
      intro address
      dsimp only
      apply Nat.add_le_add_right
      apply copyRow_price
      intro r
      split_ifs
      · exact Nat.size_le_size (hd _ r)
      · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]
      · simp only [Vector.get_replicate, BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]
    _ = _ := by rfl

theorem makeLeftBandStored_natAbs {N D L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (input : OriginalLeft N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A)
    (address : Fin (ThinMatrixBackend.tileWidth L m*4^m)) (r : Fin q) :
    (BinaryCell.view (((makeLeftBandStored shape input band).value.get address).get r)).natAbs ≤ A := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  exact makeLeftBandRuntime_natAbs _ input band hd address r

theorem makeRightBandStored_natAbs {N D L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (input : OriginalRight N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A)
    (address : Fin (4^m*ThinMatrixBackend.tileWidth L m)) (r : Fin q) :
    (BinaryCell.view (((makeRightBandStored shape input band).value.get address).get r)).natAbs ≤ A := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  exact makeRightBandRuntime_natAbs _ input band hd address r

theorem makeLeftBandStored_price {N D L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (input : OriginalLeft N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A) :
    (makeLeftBandStored shape input band).operations ≤
      ((BackendScalarBits.backendScalarUnit A.size+9)*q+24)*(shape.width*4^m) :=
  makeLeftBandRuntime_price shape.width input band hd

theorem makeRightBandStored_price {N D L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (input : OriginalRight N D q) (band : ℕ)
    (hd : ∀ i r, (BinaryCell.view ((input.get i).get r)).natAbs ≤ A) :
    (makeRightBandStored shape input band).operations ≤
      ((BackendScalarBits.backendScalarUnit A.size+9)*q+24)*(4^m*shape.width) :=
  makeRightBandRuntime_price shape.width input band hd

end ThinMatrix.BinaryBandCopyBounds

#print axioms ThinMatrix.BinaryBandCopyBounds.makeLeftBandRuntime_natAbs
#print axioms ThinMatrix.BinaryBandCopyBounds.makeRightBandRuntime_natAbs
#print axioms ThinMatrix.BinaryBandCopyBounds.makeLeftBandRuntime_price
#print axioms ThinMatrix.BinaryBandCopyBounds.makeRightBandRuntime_price
#print axioms ThinMatrix.BinaryBandCopyBounds.makeLeftBandStored_natAbs
#print axioms ThinMatrix.BinaryBandCopyBounds.makeRightBandStored_natAbs
#print axioms ThinMatrix.BinaryBandCopyBounds.makeLeftBandStored_price
#print axioms ThinMatrix.BinaryBandCopyBounds.makeRightBandStored_price


namespace ThinMatrix.BinaryTileQueryCorrectness

open ThinMatrixBackend HighBoxDP
open scoped BigOperators

theorem highRun_refines {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (M : ThinMatrixBackend.FullMultiplier q) (d : ThinMatrixBackend.QueryMetadata L m)
    (i : Fin (2*m+1)) (r : Fin q) :
    (BinaryHighTable.query t d.embedding (Vector.ofFn d.outside)
      ((BinaryBackendExecution.prepareTile (t := t) A
        (BinaryBackendExecution.prepareLeftBand (t := t) W shape left)
        (BinaryBackendExecution.prepareRightBand (t := t) W shape right)).runs.get i).high.value r).value.view =
      (ThinMatrixBackend.queryHigh rfl d.embedding d.outside d.left_cap d.right_cap
        ((ThinMatrixBackend.prepareTile (t := t) M
          (ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData left))
          (ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData right))).high.get i) r).1 := by
  have hmatch (w : States L m t) :
      ((BinaryHighTable.lookup
        ((BinaryBackendExecution.prepareTile (t := t) A
          (BinaryBackendExecution.prepareLeftBand (t := t) W shape left)
          (BinaryBackendExecution.prepareRightBand (t := t) W shape right)).runs.get i).high.value
        (ArrayKeys.materialize w.val)).get r).view =
        (StoredHighDP.lookup
          ((ThinMatrixBackend.prepareTile (t := t) M
            (ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData left))
            (ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData right))).high.get i).table
          w.val).get r := by
    have h := BinaryHighCorrectness.prepareHigh_lookup_correct shape left right hA hl hr i M w r
    dsimp only at h
    rw [BinaryBandSource.prepareLeft_run_view (t := t), BinaryBandSource.prepareRight_run_view (t := t)] at h
    simpa only [BinaryBackendExecution.prepareTile, Vector.get_ofFn,
      BinaryBackendExecution.prepareLeftBand, BinaryBackendExecution.prepareRightBand,
      ThinMatrixBackend.prepareTile_high] using h
  have h := BinaryHighTable.query_native_refines rfl d.embedding (Vector.ofFn d.outside)
    d.left_cap d.right_cap _ _ r hmatch
  have ho : (Vector.ofFn d.outside).get = d.outside := by
    funext j
    exact Vector.get_ofFn _ j
  simpa only [ho] using h

theorem highRows_refines {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (M : ThinMatrixBackend.FullMultiplier q) (row col : OuterIndex L m) (r : Fin q) :
    let d := BinaryBackendExecution.queryGeometry shape.environment row col
    let tile := BinaryBackendExecution.prepareTile (t := t) A
      (BinaryBackendExecution.prepareLeftBand (t := t) W shape left)
      (BinaryBackendExecution.prepareRightBand (t := t) W shape right)
    (BinaryBackendExecution.sumQueryRows (Vector.ofFn (fun i : Fin (2*m+1) =>
      BinaryHighTable.query t d.embedding (Vector.ofFn d.outside) (tile.runs.get i).high.value r))).value.view =
      (ThinMatrixBackend.queryHighFromTile
        (ThinMatrixBackend.prepareTile (t := t) M
          (ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData left))
          (ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData right))) row col r).1 := by
  dsimp only
  rw [BinaryBackendExecution.sumQueryRows_view]
  simp only [Vector.get_ofFn]
  unfold ThinMatrixBackend.queryHighFromTile
  simp only [ThinMatrixBackend.prepareTile_environment, ThinMatrixBackend.prepareLeftBand_environment]
  simp only [List.map_map, Function.comp_def]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact highRun_refines W shape left right hA hl hr M
    (BinaryBackendExecution.queryGeometry shape.environment row col) i r

/-- Tile refinement includes the actual same-run HIGH sum, the produced
LOW caches, and the complete binary numerator division. -/
theorem queryTile_refines {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (M : ThinMatrixBackend.FullMultiplier q) (row col : OuterIndex L m) (r : Fin q) :
    (BinaryBackendExecution.queryTile shape
      (BinaryBackendExecution.prepareLeftBand (t := t) W shape left)
      (BinaryBackendExecution.prepareRightBand (t := t) W shape right)
      (BinaryBackendExecution.prepareTile (t := t) A
        (BinaryBackendExecution.prepareLeftBand (t := t) W shape left)
        (BinaryBackendExecution.prepareRightBand (t := t) W shape right)) row col r).value.view =
      (ThinMatrixBackend.queryTile
        (ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData left))
        (ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData right))
        (ThinMatrixBackend.prepareTile (t := t) M
          (ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData left))
          (ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData right))) row col r).1 := by
  let binaryLeft := BinaryBackendExecution.prepareLeftBand (t := t) W shape left
  let binaryRight := BinaryBackendExecution.prepareRightBand (t := t) W shape right
  let nativeLeft := ThinMatrixBackend.prepareLeftBand (t := t) shape (BinaryOriginalReader.viewData left)
  let nativeRight := ThinMatrixBackend.prepareRightBand (t := t) shape (BinaryOriginalReader.viewData right)
  let tile := BinaryBackendExecution.prepareTile (t := t) A binaryLeft binaryRight
  let d := BinaryBackendExecution.queryGeometry shape.environment row col
  let high := BinaryBackendExecution.sumQueryRows (Vector.ofFn (fun i : Fin (2*m+1) =>
    BinaryHighTable.query t d.embedding (Vector.ofFn d.outside) (tile.runs.get i).high.value r))
  have hcache := BinaryBackendExecution.bandRunCaches_refines binaryLeft binaryRight nativeLeft nativeRight
    (BinaryBackendExecution.prepareLeftBand_refines W shape left)
    (BinaryBackendExecution.prepareRightBand_refines W shape right)
  have hc := BinaryLowQuery.queryCell_value t (Vector.ofFn d.embedding) (Vector.ofFn d.outside)
    (BinaryBackendExecution.bandRunCaches binaryLeft binaryRight)
    (ThinMatrixBackend.bandRunCaches nativeLeft nativeRight) hcache r high
  have hh := highRows_refines (t := t) W shape left right hA hl hr M row col r
  change high.value.view = _ at hh
  rw [hh] at hc
  exact hc

end ThinMatrix.BinaryTileQueryCorrectness

#print axioms ThinMatrix.BinaryTileQueryCorrectness.highRun_refines
#print axioms ThinMatrix.BinaryTileQueryCorrectness.highRows_refines
#print axioms ThinMatrix.BinaryTileQueryCorrectness.queryTile_refines

namespace ThinMatrix.BinaryBackendExecution
open ThinMatrixBackend
open scoped BigOperators

/-- Complete unpadded-product correctness for the actual stored-bit
pipeline. All source/HIGH caps follow from the original input cells. -/
theorem queryGlobal_correct {N D L m t q A : ℕ} [NeZero q]
    (shape : ThinMatrixBackend.ShapePlan L m) (W : ℕ)
    (hA : 1 ≤ A) (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q)
    (hl : ∀ i r, (BinaryCell.view ((inputLeft.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((inputRight.get i).get r)).natAbs ≤ A)
    (i j : Fin N) (r : Fin q) :
    (queryGlobal (ThinMatrixBackend.tileWidth_pos L m hm)
      (prepareGlobalShape (t := t) shape W A inputLeft inputRight) i j r).value.view =
      (ThinMatrixBackend.originalLeftMatrix (viewLeft inputLeft) *
        ThinMatrixBackend.originalRightMatrix (viewRight inputRight)) i j r := by
  let hB := ThinMatrixBackend.tileWidth_pos L m hm
  let bi := TilingCosts.locate hB i
  let bj := TilingCosts.locate hB j
  let M := ThinMatrixBackend.fftFullMultiplier q
  have hleft := BinaryBandCopyBounds.makeLeftBandStored_natAbs shape inputLeft bi.1.val hl
  have hright := BinaryBandCopyBounds.makeRightBandStored_natAbs shape inputRight bj.1.val hr
  have htquery := BinaryTileQueryCorrectness.queryTile_refines (t := t) W shape
    (makeLeftBandStored shape inputLeft bi.1.val).value
    (makeRightBandStored shape inputRight bj.1.val).value hA hleft hright M
    (RowIndexing.rowUnrank shape.layout bi.2) (RowIndexing.rowUnrank shape.layout bj.2) r
  unfold queryGlobal queryGlobalExecution
  simp only [prepareGlobalShape_shape,ThinMatrixBackend.storedLocate_refines,
    prepareGlobalShape_left,prepareGlobalShape_right,prepareGlobalShape_tile]
  change (queryTile shape
    (prepareLeftBand (t := t) W shape (makeLeftBandStored shape inputLeft bi.1.val).value)
    (prepareRightBand (t := t) W shape (makeRightBandStored shape inputRight bj.1.val).value)
    (prepareTile (t := t) A
      (prepareLeftBand (t := t) W shape (makeLeftBandStored shape inputLeft bi.1.val).value)
      (prepareRightBand (t := t) W shape (makeRightBandStored shape inputRight bj.1.val).value))
    (RowIndexing.rowUnrank shape.layout bi.2) (RowIndexing.rowUnrank shape.layout bj.2) r).value.view = _
  rw [htquery,makeLeftBandStored_view,makeRightBandStored_view,
    ThinMatrixBackend.makeLeftBandStored_refines,ThinMatrixBackend.makeRightBandStored_refines,
    ThinMatrixBackend.queryTile_correct M _ hm ht,
    ThinMatrixBackend.makeLeftBand_value,ThinMatrixBackend.makeRightBand_value,
    RowIndexing.rowUnrank_value,RowIndexing.rowUnrank_value]
  change ((ThinMatrixBackend.rowBand
    (ThinMatrixBackend.padMiddleLeft (m := m) (ThinMatrixBackend.originalLeftMatrix (viewLeft inputLeft))) bi.1 *
    ThinMatrixBackend.columnBand
    (ThinMatrixBackend.padMiddleRight (m := m) (ThinMatrixBackend.originalRightMatrix (viewRight inputRight))) bj.1)
    (ThinMatrixBackend.localRow hB i) (ThinMatrixBackend.localRow hB j)) r = _
  rw [ThinMatrixBackend.genuine_tile_product,ThinMatrixBackend.padMiddle_product hD]

/-- The returned global counter is read from the retained tile execution. -/
theorem queryGlobalExecution_work {N D L m t q : ℕ} [NeZero q]
    (hB : 0 < ThinMatrixBackend.tileWidth L m) (prepared : PreparedGlobal N D L m t q)
    (i j : Fin N) (r : Fin q) :
    (queryGlobalExecution hB prepared i j r).result.operations =
      (queryGlobalExecution hB prepared i j r).tile.result.operations+
        1000*(L+m+N.log2+1)^5 := rfl

/-- Complete normalization is executed once after the stored HIGH sum. -/
theorem queryTileExecution_work {L m t q : ℕ} [NeZero q] (shape : ThinMatrixBackend.ShapePlan L m)
    (left right : PreparedBand L m q) (tile : PreparedTile L m t q)
    (row col : ThinMatrixBackend.OuterIndex L m) (r : Fin q) :
    (queryTileExecution shape left right tile row col r).result.operations =
      (queryTileExecution shape left right tile row col r).complete.operations+
        1000*(L+m+1)^5 := rfl

end ThinMatrix.BinaryBackendExecution

#print axioms ThinMatrix.BinaryBackendExecution.queryGlobal_correct
#print axioms ThinMatrix.BinaryBackendExecution.queryGlobalExecution_work
#print axioms ThinMatrix.BinaryBackendExecution.queryTileExecution_work

namespace ThinMatrix.BinaryBackendExecution
open ThinMatrixBackend SourceFormation WalshEmbedding GoodMapEmbedding
def prepareShapeRuntime (L m : ℕ) : ShapePlan L m :=
  let setup := GoodMapRuntime.construct L m
  let masks := setup.good.map (fun Q => setBits Q.val)
  let good := SourceFormation.prepareGood masks
  let hg : ∀ Q, readGoodSet good.value Q = decide (Q ∈ goodSlots L m) := by
    intro Q
    change readGoodSet (SourceFormation.prepareGood masks).value Q = _
    simp only [readGoodSet,SourceFormation.prepareGood,SourceFormation.tableRead_build,
      SourceFormation.keyCube_cubeKey,SourceFormation.goodMaskProgram_correct,
      RowIndexing.cubeSupport_setBits]
    rw [show maskSlots masks = goodSlots L m from runtimeGoodMasks_slots L m]
  let hgamma : SourceFormation.columnFunction (booleanColumns setup.gamma) =
      boolColumns (GoodSetConstruction.constructGoodMaps L m).1 := by
    rw [booleanColumns_function]
    exact congrArg boolColumns (congrArg Prod.fst (GoodMapRuntime.constructedMaps_eq L m))
  let hdelta : SourceFormation.columnFunction (booleanColumns setup.delta) =
      boolColumns (GoodSetConstruction.constructGoodMaps L m).2 := by
    rw [booleanColumns_function]
    exact congrArg boolColumns (congrArg Prod.snd (GoodMapRuntime.constructedMaps_eq L m))
  let layout := prepareStoredGoodIndex good.value hg
  { environment := ⟨good.value,booleanColumns setup.gamma,booleanColumns setup.delta⟩
    layout := layout
    good := hg
    gamma := by change columnMap _ = _; rw [hgamma]; rfl
    delta := by change columnMap _ = _; rw [hdelta]; rfl
    deltaColumns_eq := hdelta
    width := layout.codes.toArray.size*4^(L-m)
    width_eq := by simp only [Vector.size_toArray]; rfl
    operations := setup.sites+good.operations+1000*(L+m+1)^5*4^L }

@[simp] theorem prepareShapeRuntime_refines (L m : ℕ) : prepareShapeRuntime L m = ThinMatrixBackend.prepareShape L m := rfl
end ThinMatrix.BinaryBackendExecution
#print axioms ThinMatrix.BinaryBackendExecution.prepareShapeRuntime_refines


namespace ThinMatrix.BinaryBackendExecution

/-- Closed preparation entry point. The captured good-map construction,
Boolean environment, compact layout and its returned setup work are formed
once before any row/column bands or tile tables are built. -/
def prepareGlobal {N D L m t q : ℕ} (W A : ℕ)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q) : PreparedGlobal N D L m t q :=
  let shape := prepareShapeRuntime L m
  prepareGlobalShape (t := t) shape W A inputLeft inputRight

theorem prepared_queryGlobal_correct {N D L m t q A : ℕ} [NeZero q]
    (W : ℕ) (hA : 1 ≤ A) (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (inputLeft : OriginalLeft N D q) (inputRight : OriginalRight N D q)
    (hl : ∀ i r, (BinaryCell.view ((inputLeft.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((inputRight.get i).get r)).natAbs ≤ A)
    (i j : Fin N) (r : Fin q) :
    (queryGlobal (ThinMatrixBackend.tileWidth_pos L m hm)
      (prepareGlobal (L := L) (m := m) (t := t) W A inputLeft inputRight) i j r).value.view =
      (ThinMatrixBackend.originalLeftMatrix (viewLeft inputLeft) *
        ThinMatrixBackend.originalRightMatrix (viewRight inputRight)) i j r :=
  queryGlobal_correct (prepareShapeRuntime L m) W hA hm ht hD inputLeft inputRight hl hr i j r

end ThinMatrix.BinaryBackendExecution
#print axioms ThinMatrix.BinaryBackendExecution.prepared_queryGlobal_correct
