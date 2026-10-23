import ExactHalfSourcePlan

set_option autoImplicit false

/-! Actual stored matrix bands feed the exact-half masked binary Walsh
sources. Both translations are shared, but each side tests its own selector.
The full pair/run arrays are retained, including repeated shifts and zeros.
Source formation work is priced separately from incomplete setup costs. -/
namespace ThinMatrix.ExactHalfBandSources
open WalshEmbedding SourceFormation GoodMapEmbedding GoodSetConstruction
open ExactHalfSourcePlan ExactHalfWeightTable BinarySourceFormation
open scoped BigOperators

def pickProgram {L m : ℕ} (plan : Plan L m) (Q : Finset (Fin L)) (h : Cube m) :
    Program (Fin (J m)) :=
  let outer := tableReadProgram 2 L plan.picks (cubeKey (setBits Q))
  let inner := tableReadProgram 2 m outer.value (cubeKey h)
  ⟨inner.value,outer.operations+inner.operations+8*(L+1)^2+4*m+8⟩

theorem pickProgram_value {L m : ℕ} (plan : Plan L m) (Q : Finset (Fin L)) (h : Cube m) :
    (pickProgram plan Q h).value=readPick plan.picks Q h := by
  simp only [pickProgram,tableReadProgram_value,readPick]

theorem pickProgram_work {L m : ℕ} (plan : Plan L m) (Q : Finset (Fin L)) (h : Cube m) :
    (pickProgram plan Q h).operations=8*(L+1)^2+2*L+6*m+10 := by
  simp only [pickProgram,tableReadProgram_cost]; omega

def leftReader {L m d q : ℕ} (plan : Plan L m) (read : BinaryLeftRead L m d q)
    (r s : Fin (J m)) : BinaryLeftRead L m d q :=
  fun Q bits outer h k j =>
    let h' := Vector.ofFn (xorBits h (plan.shifts.get r).get)
    let k' := Vector.ofFn (xorBits k (plan.shifts.get s).get)
    let picked := pickProgram plan Q h'.get
    let out := if picked.value=r then read Q bits outer h'.get k'.get j else ⟨BinaryCell.zero,1⟩
    ⟨out.value,picked.operations+out.operations+8*m+8⟩

def rightReader {L m d q : ℕ} (plan : Plan L m) (read : BinaryRightRead L m d q)
    (r s : Fin (J m)) : BinaryRightRead L m d q :=
  fun Q bits h k outer j =>
    let h' := Vector.ofFn (xorBits h (plan.shifts.get r).get)
    let k' := Vector.ofFn (xorBits k (plan.shifts.get s).get)
    let picked := pickProgram plan Q k'.get
    let out := if picked.value=s then read Q bits h'.get k'.get outer j else ⟨BinaryCell.zero,1⟩
    ⟨out.value,picked.operations+out.operations+8*m+8⟩

theorem leftReader_view {L m d q : ℕ} [NeZero q] (shape : ThinMatrixBackend.ShapePlan L m)
    (read : BinaryLeftRead L m d q) (X : RawLeftInput L m d (CyclicRing.Cyclic q))
    (hr : ∀ Q bits outer h k j, BinaryCell.view (read Q bits outer h k j).value=X Q bits outer h k j)
    (r s : Fin (J m)) (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube d) (h k : Cube m) (j : Fin q) :
    BinaryCell.view (leftReader (prepare shape).value read r s Q bits outer h k j).value=
      MaskedLightSources.leftInput X (ExactHalfCroppedEmbedding.scanPick L m)
        (ExactHalfCroppedEmbedding.shifts m).get r s Q bits outer h k j := by
  simp only [leftReader,ofFn_get,pickProgram_value,prepare_pick,prepare_shift,
    MaskedLightSources.leftInput,TranslatedSourcePartition.leftPiece,MaskedLightSources.xorShift,
    Equiv.coe_fn_mk]
  split
  · exact hr _ _ _ _ _ _
  · rfl

theorem rightReader_view {L m d q : ℕ} [NeZero q] (shape : ThinMatrixBackend.ShapePlan L m)
    (read : BinaryRightRead L m d q) (Y : RawRightInput L m d (CyclicRing.Cyclic q))
    (hr : ∀ Q bits h k outer j, BinaryCell.view (read Q bits h k outer j).value=Y Q bits h k outer j)
    (r s : Fin (J m)) (Q : Finset (Fin L)) (bits : Cube L) (h k : Cube m) (outer : Cube d) (j : Fin q) :
    BinaryCell.view (rightReader (prepare shape).value read r s Q bits h k outer j).value=
      MaskedLightSources.rightInput Y (ExactHalfCroppedEmbedding.scanPick L m)
        (ExactHalfCroppedEmbedding.shifts m).get r s Q bits h k outer j := by
  simp only [rightReader,ofFn_get,pickProgram_value,prepare_pick,prepare_shift,
    MaskedLightSources.rightInput,TranslatedSourcePartition.rightPiece,MaskedLightSources.xorShift,
    Equiv.coe_fn_mk]
  split
  · exact hr _ _ _ _ _ _
  · rfl

def readerBudget (L m B : ℕ) : ℕ := B+8*(L+1)^2+2*L+14*m+19

theorem leftReader_work {L m d q B : ℕ} (plan : Plan L m) (read : BinaryLeftRead L m d q)
    (hc : ∀ Q bits outer h k j, (read Q bits outer h k j).operations ≤ B)
    (r s : Fin (J m)) (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube d) (h k : Cube m) (j : Fin q) :
    (leftReader plan read r s Q bits outer h k j).operations ≤ readerBudget L m B := by
  simp only [leftReader,pickProgram_work,readerBudget]
  split
  · have hh := hc Q bits outer (Vector.ofFn (xorBits h (plan.shifts.get r).get)).get (Vector.ofFn (xorBits k (plan.shifts.get s).get)).get j; omega
  · dsimp only; omega

theorem rightReader_work {L m d q B : ℕ} (plan : Plan L m) (read : BinaryRightRead L m d q)
    (hc : ∀ Q bits h k outer j, (read Q bits h k outer j).operations ≤ B)
    (r s : Fin (J m)) (Q : Finset (Fin L)) (bits : Cube L) (h k : Cube m) (outer : Cube d) (j : Fin q) :
    (rightReader plan read r s Q bits h k outer j).operations ≤ readerBudget L m B := by
  simp only [rightReader,pickProgram_work,readerBudget]
  split
  · have hh := hc Q bits (Vector.ofFn (xorBits h (plan.shifts.get r).get)).get (Vector.ofFn (xorBits k (plan.shifts.get s).get)).get outer j; omega
  · dsimp only; omega

theorem leftReader_bound {L m d q A : ℕ} (plan : Plan L m) (read : BinaryLeftRead L m d q)
    (hr : ∀ Q bits outer h k j, (BinaryCell.view (read Q bits outer h k j).value).natAbs ≤ A)
    (r s : Fin (J m)) (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube d) (h k : Cube m) (j : Fin q) :
    (BinaryCell.view (leftReader plan read r s Q bits outer h k j).value).natAbs ≤ A := by
  simp only [leftReader]; split
  · exact hr _ _ _ _ _ _
  · simp

theorem rightReader_bound {L m d q A : ℕ} (plan : Plan L m) (read : BinaryRightRead L m d q)
    (hr : ∀ Q bits h k outer j, (BinaryCell.view (read Q bits h k outer j).value).natAbs ≤ A)
    (r s : Fin (J m)) (Q : Finset (Fin L)) (bits : Cube L) (h k : Cube m) (outer : Cube d) (j : Fin q) :
    (BinaryCell.view (rightReader plan read r s Q bits h k outer j).value).natAbs ≤ A := by
  simp only [rightReader]; split
  · exact hr _ _ _ _ _ _
  · simp

abbrev Runs (L m q : ℕ) := Vector (BinarySourceFormation.RawStore L q) (2*m+1)

def cacheLeft {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : BinaryBandSource.StoredLeftMatrix L m q) : Program (BinaryInputAdapter.InputStore L m q) :=
  BinaryInputAdapter.buildLeftAdapter
    (BinaryBandSource.storedRawLeftReader shape.environment.good shape.good shape.layout data)

def cacheRight {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : BinaryBandSource.StoredRightMatrix L m q) : Program (BinaryInputAdapter.InputStore L m q) :=
  BinaryInputAdapter.buildRightAdapter
    (BinaryBandSource.storedRawRightReader shape.environment.good shape.good shape.layout data)

def left {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (data : BinaryInputAdapter.InputStore L m q) (r s : Fin (J m)) : Program (Runs L m q) :=
  BinarySourceFormation.formLeftRuns shape.environment
    (leftReader plan (BinaryInputAdapter.leftInputReader data) r s)

def right {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (data : BinaryInputAdapter.InputStore L m q) (r s : Fin (J m)) : Program (Runs L m q) :=
  BinarySourceFormation.formRightRuns shape.environment
    (rightReader plan (BinaryInputAdapter.rightInputReader data) r s)

theorem left_source {L m q : ℕ} [NeZero q] (shape : ThinMatrixBackend.ShapePlan L m)
    (data : BinaryBandSource.StoredLeftMatrix L m q) (r s : Fin (J m)) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (j : Fin q) :
    BinaryCell.view (BinarySourceFormation.readRaw
      ((left shape (prepare shape).value (cacheLeft shape data).value r s).value.get run) normal opposite j)=
      rawLeftSource
        (MaskedLightSources.leftInput (ThinMatrixBackend.rawLeft
          (ThinMatrixBackend.readLeftMatrix (BinaryOriginalReader.viewData data)))
          (ExactHalfCroppedEmbedding.scanPick L m) (ExactHalfCroppedEmbedding.shifts m).get r s)
        (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
        (runValue m run) normal opposite j := by
  rw [show BinaryCell.view=BinarySourceCells.Cell.view from rfl]
  rw [left,BinarySourceFormation.formLeftRuns,vectorBuild_get,
    ← BinarySourceFormation.readRaw_view,BinarySourceFormation.formLeftSource_view]
  let rd := BinaryInputAdapter.leftInputReader (cacheLeft shape data).value
  let X := ThinMatrixBackend.rawLeft (ThinMatrixBackend.readLeftMatrix (BinaryOriginalReader.viewData data))
  have hv : ∀ Q bits outer h k j, BinaryCell.view (rd Q bits outer h k j).value=X Q bits outer h k j := by
    intro Q bits outer h k j
    exact BinaryBandSource.cachedLeftReader_value shape data Q bits outer h k j
  have hh := SourceFormation.formLeftSource_correct shape.environment
    (semanticLeft (leftReader (prepare shape).value rd r s))
    (MaskedLightSources.leftInput X (ExactHalfCroppedEmbedding.scanPick L m)
      (ExactHalfCroppedEmbedding.shifts m).get r s) (goodSlots L m)
    (BinaryBandSource.shape_good shape) (leftReader_view shape rd X hv r s)
    (runValue m run) normal opposite j
  rw [shape.gamma,shape.delta] at hh
  exact hh

theorem right_source {L m q : ℕ} [NeZero q] (shape : ThinMatrixBackend.ShapePlan L m)
    (data : BinaryBandSource.StoredRightMatrix L m q) (r s : Fin (J m)) (run : Fin (2*m+1))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (j : Fin q) :
    BinaryCell.view (BinarySourceFormation.readRaw
      ((right shape (prepare shape).value (cacheRight shape data).value r s).value.get run) normal opposite j)=
      rawRightSource
        (MaskedLightSources.rightInput (ThinMatrixBackend.rawRight
          (ThinMatrixBackend.readRightMatrix (BinaryOriginalReader.viewData data)))
          (ExactHalfCroppedEmbedding.scanPick L m) (ExactHalfCroppedEmbedding.shifts m).get r s)
        (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
        (runValue m run) normal opposite j := by
  rw [show BinaryCell.view=BinarySourceCells.Cell.view from rfl]
  rw [right,BinarySourceFormation.formRightRuns,vectorBuild_get,
    ← BinarySourceFormation.readRaw_view,BinarySourceFormation.formRightSource_view]
  let rd := BinaryInputAdapter.rightInputReader (cacheRight shape data).value
  let Y := ThinMatrixBackend.rawRight (ThinMatrixBackend.readRightMatrix (BinaryOriginalReader.viewData data))
  have hv : ∀ Q bits h k outer j, BinaryCell.view (rd Q bits h k outer j).value=Y Q bits h k outer j := by
    intro Q bits h k outer j
    exact BinaryBandSource.cachedRightReader_value shape data Q bits h k outer j
  have hh := SourceFormation.formRightSource_correct shape.environment
    (semanticRight (rightReader (prepare shape).value rd r s))
    (MaskedLightSources.rightInput Y (ExactHalfCroppedEmbedding.scanPick L m)
      (ExactHalfCroppedEmbedding.shifts m).get r s) (goodSlots L m)
    (BinaryBandSource.shape_good shape) (rightReader_view shape rd Y hv r s)
    (runValue m run) normal opposite j
  rw [shape.gamma,shape.delta] at hh
  exact hh

def bandBudget (L m q A : ℕ) : ℕ :=
  (sourceBudget L m (L-m) q (readerBudget L m (BinaryBandSource.cachedReadBudget L m A.size))+8)*
    (2*m+1)*BinarySourceFormation.bitUnit L (L-m) A

theorem cachedLeft_bound {L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : BinaryBandSource.StoredLeftMatrix L m q)
    (ha : ∀ i j, (BinaryCell.view ((data.get i).get j)).natAbs ≤ A)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h k : Cube m) (j : Fin q) :
    (BinaryCell.view (BinaryInputAdapter.readInput (cacheLeft shape data).value Q bits outer h k j)).natAbs≤A := by
  rw [cacheLeft,BinaryInputAdapter.read_buildLeftAdapter]
  exact BinaryBandSource.storedRawLeftReader_natAbs _ _ _ _ A ha _ _ _ _ _ _

theorem cachedRight_bound {L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (data : BinaryBandSource.StoredRightMatrix L m q)
    (ha : ∀ i j, (BinaryCell.view ((data.get i).get j)).natAbs ≤ A)
    (Q : Finset (Fin L)) (bits : Cube L) (h k : Cube m) (outer : Cube (L-m)) (j : Fin q) :
    (BinaryCell.view (BinaryInputAdapter.readInput (cacheRight shape data).value Q bits outer h k j)).natAbs≤A := by
  rw [cacheRight,BinaryInputAdapter.read_buildRightAdapter]
  exact BinaryBandSource.storedRawRightReader_natAbs _ _ _ _ A ha _ _ _ _ _ _

theorem left_work {L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (data : BinaryBandSource.StoredLeftMatrix L m q)
    (ha : ∀ i j, (BinaryCell.view ((data.get i).get j)).natAbs ≤ A) (r s : Fin (J m)) :
    (left shape plan (cacheLeft shape data).value r s).operations ≤ bandBudget L m q A := by
  apply BinarySourceFormation.formLeftRuns_cost
  · intro Q bits outer h k j
    apply leftReader_work
    intro Q bits outer h k j
    exact BinaryInputAdapter.leftInputReader_price _ _ _ _ _ _ _ A.size
      (Nat.size_le_size (cachedLeft_bound shape data ha Q bits outer h k j))
  · intro Q bits outer h k j
    apply leftReader_bound
    intro Q bits outer h k j
    simp only [BinaryInputAdapter.leftInputReader,BinaryCell.copy_view]
    exact cachedLeft_bound shape data ha Q bits outer h k j

theorem right_work {L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (data : BinaryBandSource.StoredRightMatrix L m q)
    (ha : ∀ i j, (BinaryCell.view ((data.get i).get j)).natAbs ≤ A) (r s : Fin (J m)) :
    (right shape plan (cacheRight shape data).value r s).operations ≤ bandBudget L m q A := by
  apply BinarySourceFormation.formRightRuns_cost
  · intro Q bits h k outer j
    apply rightReader_work
    intro Q bits h k outer j
    exact BinaryInputAdapter.rightInputReader_price _ _ _ _ _ _ _ A.size
      (Nat.size_le_size (cachedRight_bound shape data ha Q bits h k outer j))
  · intro Q bits h k outer j
    apply rightReader_bound
    intro Q bits h k outer j
    simp only [BinaryInputAdapter.rightInputReader,BinaryCell.copy_view]
    exact cachedRight_bound shape data ha Q bits h k outer j

abbrev PairArrays (L m q : ℕ) := Runs L m q × Runs L m q
abbrev Families (L m q : ℕ) := Vector (Vector (PairArrays L m q) (J m)) (J m)

def pair {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (a b : BinaryInputAdapter.InputStore L m q)
    (r s : Fin (J m)) : Program (PairArrays L m q) :=
  let x := left shape plan a r s
  let y := right shape plan b r s
  ⟨(x.value,y.value),x.operations+y.operations+4⟩

def allPairs {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (a : BinaryBandSource.StoredLeftMatrix L m q) (b : BinaryBandSource.StoredRightMatrix L m q) :
    Program (Families L m q) :=
  let aCache := cacheLeft shape a
  let bCache := cacheRight shape b
  let out := indexedBuild (count m) (count_eq m) fun r => indexedBuild (count m) (count_eq m) fun s => pair shape plan aCache.value bCache.value r s
  ⟨out.value,aCache.operations+bCache.operations+out.operations+8⟩

theorem allPairs_get {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (a : BinaryBandSource.StoredLeftMatrix L m q) (b : BinaryBandSource.StoredRightMatrix L m q)
    (r s : Fin (J m)) :
    (((allPairs shape plan a b).value.get r).get s)=
      ((left shape plan (cacheLeft shape a).value r s).value,(right shape plan (cacheRight shape b).value r s).value) := by
  simp only [allPairs,indexedBuild_eq,vectorBuild_get,pair]

def cacheBudget (L m q A : ℕ) : ℕ :=
  BinaryInputAdapter.adapterBudget L m q (BinaryBandSource.rawReadBudget L m A.size)

def familiesBudget (L m q A : ℕ) : ℕ :=
  2*cacheBudget L m q A+((2*bandBudget L m q A+12)*J m+8)*J m+8

theorem allPairs_work {L m q A : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (a : BinaryBandSource.StoredLeftMatrix L m q) (b : BinaryBandSource.StoredRightMatrix L m q)
    (ha : ∀ i j, (BinaryCell.view ((a.get i).get j)).natAbs ≤ A)
    (hb : ∀ i j, (BinaryCell.view ((b.get i).get j)).natAbs ≤ A) (hm : m≤L) :
    (allPairs shape plan a b).operations ≤ familiesBudget L m q A := by
  have hl : (cacheLeft shape a).operations≤cacheBudget L m q A := by
    apply BinaryInputAdapter.buildLeftAdapter_cost
    exact BinaryBandSource.storedRawLeftReader_cost _ _ _ _ A.size
      (fun i j => Nat.size_le_size (ha i j)) hm
  have hr : (cacheRight shape b).operations≤cacheBudget L m q A := by
    apply BinaryInputAdapter.buildRightAdapter_cost
    exact BinaryBandSource.storedRawRightReader_cost _ _ _ _ A.size
      (fun i j => Nat.size_le_size (hb i j)) hm
  have hp : (indexedBuild (count m) (count_eq m) fun r => indexedBuild (count m) (count_eq m) fun s =>
      pair shape plan (cacheLeft shape a).value (cacheRight shape b).value r s).operations ≤
      ((2*bandBudget L m q A+12)*J m+8)*J m := by
    simp only [indexedBuild_eq]
    apply vectorBuild_cost; intro r
    apply vectorBuild_cost; intro s
    have h1 := left_work shape plan a ha r s
    have h2 := right_work shape plan b hb r s
    simp only [pair]; omega
  simp only [allPairs,familiesBudget]; omega

theorem allPairs_occurrences {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (plan : Plan L m)
    (a : BinaryBandSource.StoredLeftMatrix L m q) (b : BinaryBandSource.StoredRightMatrix L m q) :
    (((allPairs shape plan a b).value.toList.map (fun row => row.toArray.size)).sum)=
      if m=0 then 1 else 4096*m^6 := by
  rw [BinaryResidualDegreeSpace.toList_get]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,Vector.size_toArray,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hp := ExactHalfCroppedEmbedding.pair_count m
  simpa only [Fintype.card_prod,Fintype.card_fin,J] using hp

#print axioms cachedLeft_bound
#print axioms cachedRight_bound
#print axioms allPairs_get
#print axioms allPairs_work
#print axioms allPairs_occurrences

#print axioms pickProgram_value
#print axioms pickProgram_work
#print axioms leftReader_view
#print axioms rightReader_view
#print axioms leftReader_work
#print axioms rightReader_work
#print axioms leftReader_bound
#print axioms rightReader_bound
#print axioms left_source
#print axioms right_source
#print axioms left_work
#print axioms right_work
end ThinMatrix.ExactHalfBandSources
