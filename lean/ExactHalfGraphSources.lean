import ExactHalfBandSources
import BinaryFoldedFactory

set_option autoImplicit false

/-! Original binary callback inputs, actual folded formation, actual band
copies, constructed good maps and exact-half selectors feed every pair/run
source array. Physical dimensions come from the existing retained parameter
interface. This supplies sources, not a count oracle or an APSP work theorem. -/
namespace ThinMatrix.ExactHalfGraphSources
open WalshEmbedding SourceFormation BinaryFoldedFormation
open ExactHalfSourcePlan ExactHalfBandSources

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : ℕ) where
  shape : ThinMatrixBackend.ShapePlan p.L p.m
  selectors : BinaryGroupedCoordinates.Run (ExactHalfSourcePlan.Plan p.L p.m)
  folded : BinaryCell.Result (Sources n h (FoldedBackendExecution.physicalFold f) f.cyclic block)
  leftBand : Program (BinaryBandSource.StoredLeftMatrix p.L p.m f.cyclic)
  rightBand : Program (BinaryBandSource.StoredRightMatrix p.L p.m f.cyclic)
  sources : Program (Families p.L p.m f.cyclic)

def execute {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) : Prepared f p block.val :=
  let shape := BinaryBackendExecution.prepareShapeRuntime p.L p.m
  let selectors := ExactHalfSourcePlan.prepare shape
  let folded := formSourcesCached f block input p.foldWidth p.N p.D p.raw
    p.foldWidth_eq p.N_eq p.D_eq p.raw_eq
  let a := BinaryBackendExecution.makeLeftBandStored shape (p.castLeft folded.value.left) bandL
  let b := BinaryBackendExecution.makeRightBandStored shape (p.castRight folded.value.right) bandR
  let sources := allPairs shape selectors.value a.value b.value
  ⟨shape,selectors,folded,a,b,sources⟩

theorem folded_left {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) :
    BinaryFoldedFormation.viewLeft (execute f p block input bandL bandR).folded.value.left=
      FoldedBackendExecution.formLeft f block (viewTable input.left) := by
  simp only [execute,formSourcesCached_refines]
  exact BinaryFoldedFormationCorrect.formSources_left_view f block input

theorem folded_right {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) :
    BinaryFoldedFormation.viewRight (execute f p block input bandL bandR).folded.value.right=
      FoldedBackendExecution.formRight f block (viewTable input.right) := by
  simp only [execute,formSourcesCached_refines]
  exact BinaryFoldedFormationCorrect.formSources_right_view f block input

theorem folded_left_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) (address : Fin (p.N*p.D)) (coeff : Fin f.cyclic) :
    (BinaryCell.view (((p.castLeft (execute f p block input bandL bandR).folded.value.left).get address).get coeff)).natAbs≤1 := by
  simpa only [BinaryBackendExecution.viewLeft,BinaryOriginalReader.viewData,Vector.get_map,BinaryFoldedFactory.prepareBlock,execute] using
    BinaryFoldedFactory.sources_left_abs f p block input address coeff

theorem folded_right_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) (address : Fin (p.D*p.N)) (coeff : Fin f.cyclic) :
    (BinaryCell.view (((p.castRight (execute f p block input bandL bandR).folded.value.right).get address).get coeff)).natAbs≤1 := by
  simpa only [BinaryBackendExecution.viewRight,BinaryOriginalReader.viewData,Vector.get_map,BinaryFoldedFactory.prepareBlock,execute] using
    BinaryFoldedFactory.sources_right_abs f p block input address coeff

theorem left_band_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ)
    (i : Fin (ThinMatrixBackend.tileWidth p.L p.m*4^p.m)) (j : Fin f.cyclic) :
    (BinaryCell.view ((((execute f p block input bandL bandR).leftBand.value).get i).get j)).natAbs≤1 := by
  apply BinaryBandCopyBounds.makeLeftBandStored_natAbs
  intro address coeff
  exact folded_left_bound f p block input bandL bandR address coeff

theorem right_band_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ)
    (i : Fin (4^p.m*ThinMatrixBackend.tileWidth p.L p.m)) (j : Fin f.cyclic) :
    (BinaryCell.view ((((execute f p block input bandL bandR).rightBand.value).get i).get j)).natAbs≤1 := by
  apply BinaryBandCopyBounds.makeRightBandStored_natAbs
  intro address coeff
  exact folded_right_bound f p block input bandL bandR address coeff

theorem sources_work {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) :
    (execute f p block input bandL bandR).sources.operations≤familiesBudget p.L p.m f.cyclic 1 := by
  apply allPairs_work
  · exact left_band_bound f p block input bandL bandR
  · exact right_band_bound f p block input bandL bandR
  · exact p.m_le_L

theorem band_copy_work {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) :
    (execute f p block input bandL bandR).leftBand.operations+
      (execute f p block input bandL bandR).rightBand.operations ≤
      2*((BackendScalarBits.backendScalarUnit 1+9)*f.cyclic+24)*
        (ThinMatrixBackend.tileWidth p.L p.m*4^p.m) := by
  have hl := BinaryBandCopyBounds.makeLeftBandStored_price
    (BinaryBackendExecution.prepareShapeRuntime p.L p.m)
    (p.castLeft (execute f p block input bandL bandR).folded.value.left) bandL
    (folded_left_bound f p block input bandL bandR)
  have hr := BinaryBandCopyBounds.makeRightBandStored_price
    (BinaryBackendExecution.prepareShapeRuntime p.L p.m)
    (p.castRight (execute f p block input bandL bandR).folded.value.right) bandR
    (folded_right_bound f p block input bandL bandR)
  rw [(BinaryBackendExecution.prepareShapeRuntime p.L p.m).width_eq] at hl hr
  simp only [Nat.size_one] at hl hr
  have hh := Nat.add_le_add hl hr
  exact hh.trans_eq (by ring)

/-- Every stored left source is exactly the source used in the already
proved exact-half embedding, with the actual input-derived band. -/
theorem left_source {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) [NeZero f.cyclic]
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (normal : Fin p.L → NormalLetter) (opposite : Fin p.L → OppositeLetter) (j : Fin f.cyclic) :
    BinaryCell.view (BinarySourceFormation.readRaw
      (((((execute f p block input bandL bandR).sources.value.get u).get v).1).get run) normal opposite j)=
      rawLeftSource
        (MaskedLightSources.leftInput (ThinMatrixBackend.rawLeft (ThinMatrixBackend.readLeftMatrix
          (BinaryOriginalReader.viewData (execute f p block input bandL bandR).leftBand.value)))
          (ExactHalfCroppedEmbedding.scanPick p.L p.m) (ExactHalfCroppedEmbedding.shifts p.m).get u v)
        (GoodMapEmbedding.goodSlots p.L p.m)
        (GoodMapEmbedding.cubeMap (GoodSetConstruction.constructGoodMaps p.L p.m).1)
        (GoodMapEmbedding.cubeMap (GoodSetConstruction.constructGoodMaps p.L p.m).2)
        (runValue p.m run) normal opposite j := by
  simp only [execute,allPairs_get]
  exact ExactHalfBandSources.left_source _ _ _ _ _ _ _ _

theorem right_source {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) [NeZero f.cyclic]
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (normal : Fin p.L → NormalLetter) (opposite : Fin p.L → OppositeLetter) (j : Fin f.cyclic) :
    BinaryCell.view (BinarySourceFormation.readRaw
      (((((execute f p block input bandL bandR).sources.value.get u).get v).2).get run) normal opposite j)=
      rawRightSource
        (MaskedLightSources.rightInput (ThinMatrixBackend.rawRight (ThinMatrixBackend.readRightMatrix
          (BinaryOriginalReader.viewData (execute f p block input bandL bandR).rightBand.value)))
          (ExactHalfCroppedEmbedding.scanPick p.L p.m) (ExactHalfCroppedEmbedding.shifts p.m).get u v)
        (GoodMapEmbedding.goodSlots p.L p.m)
        (GoodMapEmbedding.cubeMap (GoodSetConstruction.constructGoodMaps p.L p.m).1)
        (GoodMapEmbedding.cubeMap (GoodSetConstruction.constructGoodMaps p.L p.m).2)
        (runValue p.m run) normal opposite j := by
  simp only [execute,allPairs_get]
  exact ExactHalfBandSources.right_source _ _ _ _ _ _ _ _

theorem pair_occurrences {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : Inputs n) (bandL bandR : ℕ) :
    (((execute f p block input bandL bandR).sources.value.toList.map (fun row => row.toArray.size)).sum)=
      if p.m=0 then 1 else 4096*p.m^6 := allPairs_occurrences _ _ _ _

#print axioms folded_left_bound
#print axioms folded_right_bound
#print axioms folded_left
#print axioms folded_right
#print axioms left_band_bound
#print axioms right_band_bound
#print axioms sources_work
#print axioms band_copy_work
#print axioms left_source
#print axioms right_source
#print axioms pair_occurrences
end ThinMatrix.ExactHalfGraphSources
