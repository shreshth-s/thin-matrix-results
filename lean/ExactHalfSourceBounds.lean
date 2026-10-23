import RetainedResidualFamily

set_option autoImplicit false

/-! Magnitude bounds for the actual translated source stores. The bound is
derived from graph-input folded formation, not supplied as a root-family
precondition. -/
namespace ThinMatrix.ExactHalfSourceBounds
open WalshEmbedding GoodMapEmbedding SourceFormation ExactHalfSourcePlan ExactHalfBandSources
open CoefficientBounds ThinMatrixBackend

 theorem left {L m C A : ℕ} [NeZero C] (shape : ShapePlan L m)
    (a : BinaryBandSource.StoredLeftMatrix L m C)
    (ha : ∀ i j, (BinaryCell.view ((a.get i).get j)).natAbs≤A)
    (r s : Fin (J m)) (run : Fin (2*m+1)) :
    BinaryResidualLeaf.RawBound
      ((ExactHalfBandSources.left shape (prepare shape).value (cacheLeft shape a).value r s).value.get run)
      (2^(L+m)*A) := by
  intro n o j
  rw [ExactHalfBandSources.left_source]
  have hx := AdaptiveBitBounds.rawLeft_bound (BinaryOriginalReader.viewData a)
    (BinaryBandBounds.viewData_abs_bound a ha)
  have hm : ∀ Q bits outer h k, CoeffBound
      (MaskedLightSources.leftInput (rawLeft (readLeftMatrix (BinaryOriginalReader.viewData a)))
        (ExactHalfCroppedEmbedding.scanPick L m) (ExactHalfCroppedEmbedding.shifts m).get r s Q bits outer h k) A := by
    intro Q bits outer h k
    unfold MaskedLightSources.leftInput TranslatedSourcePartition.leftPiece
    split
    · exact hx _ _ _ _ _
    · intro c; simp
  have h := PipelineBitBounds.rawLeftSource_bound _ (goodSlots L m)
    (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
    (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) (runValue m run)
    (fun Q hQ => goodSlots_size L m Q hQ) hm n o j
  rw [← Int.natCast_natAbs] at h
  have hn : (rawLeftSource
    (MaskedLightSources.leftInput (rawLeft (readLeftMatrix (BinaryOriginalReader.viewData a)))
      (ExactHalfCroppedEmbedding.scanPick L m) (ExactHalfCroppedEmbedding.shifts m).get r s)
    (goodSlots L m) (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
    (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) (runValue m run) n o j).natAbs≤2^(L-m+m)*A := by
    exact_mod_cast h
  exact hn.trans (Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by decide) (by omega)))

 theorem right {L m C A : ℕ} [NeZero C] (shape : ShapePlan L m)
    (a : BinaryBandSource.StoredRightMatrix L m C)
    (ha : ∀ i j, (BinaryCell.view ((a.get i).get j)).natAbs≤A)
    (r s : Fin (J m)) (run : Fin (2*m+1)) :
    BinaryResidualLeaf.RawBound
      ((ExactHalfBandSources.right shape (prepare shape).value (cacheRight shape a).value r s).value.get run)
      (2^(L+m)*A) := by
  intro n o j
  rw [ExactHalfBandSources.right_source]
  have hx := AdaptiveBitBounds.rawRight_bound (BinaryOriginalReader.viewData a)
    (BinaryBandBounds.viewData_abs_bound a ha)
  have hm : ∀ Q bits h k outer, CoeffBound
      (MaskedLightSources.rightInput (rawRight (readRightMatrix (BinaryOriginalReader.viewData a)))
        (ExactHalfCroppedEmbedding.scanPick L m) (ExactHalfCroppedEmbedding.shifts m).get r s Q bits h k outer) A := by
    intro Q bits h k outer
    unfold MaskedLightSources.rightInput TranslatedSourcePartition.rightPiece
    split
    · exact hx _ _ _ _ _
    · intro c; simp
  have h := PipelineBitBounds.rawRightSource_bound _ (goodSlots L m)
    (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
    (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) (runValue m run)
    (fun Q hQ => goodSlots_size L m Q hQ) hm n o j
  rw [← Int.natCast_natAbs] at h
  have hn : (rawRightSource
    (MaskedLightSources.rightInput (rawRight (readRightMatrix (BinaryOriginalReader.viewData a)))
      (ExactHalfCroppedEmbedding.scanPick L m) (ExactHalfCroppedEmbedding.shifts m).get r s)
    (goodSlots L m) (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
    (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) (runValue m run) n o j).natAbs≤2^(L-m+m)*A := by
    exact_mod_cast h
  exact hn.trans (Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by decide) (by omega)))

 theorem graph_left {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    BinaryResidualLeaf.RawBound
      (((((ExactHalfGraphSources.execute f p block input bandL bandR).sources.value.get u).get v).1).get run)
      (2^(p.L+p.m)) := by
  haveI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  have hb := ExactHalfGraphSources.left_band_bound f p block input bandL bandR
  have hs := left (BinaryBackendExecution.prepareShapeRuntime p.L p.m)
    (ExactHalfGraphSources.execute f p block input bandL bandR).leftBand.value hb u v run
  simpa only [ExactHalfGraphSources.execute,allPairs_get,Nat.mul_one] using hs

 theorem graph_right {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    BinaryResidualLeaf.RawBound
      (((((ExactHalfGraphSources.execute f p block input bandL bandR).sources.value.get u).get v).2).get run)
      (2^(p.L+p.m)) := by
  haveI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  have hb := ExactHalfGraphSources.right_band_bound f p block input bandL bandR
  have hs := right (BinaryBackendExecution.prepareShapeRuntime p.L p.m)
    (ExactHalfGraphSources.execute f p block input bandL bandR).rightBand.value hb u v run
  simpa only [ExactHalfGraphSources.execute,allPairs_get,Nat.mul_one] using hs

 theorem graph_left_normal_cap {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (normal : Fin p.L → NormalLetter) (opposite : Fin p.L → OppositeLetter) (coeff : Fin f.cyclic)
    (hc : p.m/2<ones (normalP2Bits normal)) :
    BinaryCell.view (BinarySourceFormation.readRaw
      (((((ExactHalfGraphSources.execute f p block input bandL bandR).sources.value.get u).get v).1).get run)
      normal opposite coeff)=0 := by
  haveI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [ExactHalfGraphSources.left_source]
  exact congrFun (ExactHalfResidualWindow.left_normal_cap
    (rawLeft (readLeftMatrix (BinaryOriginalReader.viewData
      (ExactHalfGraphSources.execute f p block input bandL bandR).leftBand.value))) u v (runValue p.m run) normal opposite hc) coeff

 theorem graph_right_normal_cap {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (normal : Fin p.L → NormalLetter) (opposite : Fin p.L → OppositeLetter) (coeff : Fin f.cyclic)
    (hc : p.m/2<ones (normalP2Bits normal)) :
    BinaryCell.view (BinarySourceFormation.readRaw
      (((((ExactHalfGraphSources.execute f p block input bandL bandR).sources.value.get u).get v).2).get run)
      normal opposite coeff)=0 := by
  haveI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [ExactHalfGraphSources.right_source]
  exact congrFun (ExactHalfResidualWindow.right_normal_cap
    (rawRight (readRightMatrix (BinaryOriginalReader.viewData
      (ExactHalfGraphSources.execute f p block input bandL bandR).rightBand.value))) u v (runValue p.m run) normal opposite hc) coeff

#print axioms graph_left_normal_cap
#print axioms graph_right_normal_cap
#print axioms left
#print axioms right
#print axioms graph_left
#print axioms graph_right
end ThinMatrix.ExactHalfSourceBounds
