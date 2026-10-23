import RetainedDegreeRuns

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! Replace actual stored run coefficients by the original masked Walsh
source formulas of the retained folded bands. No supplied semantic answer or
root is assumed in the graph-input specialization. -/
namespace ThinMatrix.GraphLowRunSources
open WalshEmbedding GoodMapEmbedding GoodSetConstruction ExactHalfSourcePlan ResidualFamilyKeys
open DistinguishedResidualSupport
open scoped BigOperators

noncomputable def source {L m q : ℕ} [NeZero q]
    (X : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → CyclicRing.Cyclic q)
    (a b : Mask L m) (forms : Fin (2*(L-m)) → Fin 3 → ℤ) (x : RetainedShiftedFactor.Data m (L-m)) : Polynomial (CyclicRing.Cyclic q) :=
  ((∏ i, forms i (x.1 i) : ℤ) : Polynomial (CyclicRing.Cyclic q))*
    Polynomial.C (cropBoth (m/2) X (RetainedShiftedFactor.normalInput a b x.1 x.2.1)
      (RetainedShiftedFactor.oppositeInput a b x.1 x.2.2))

theorem source_eq {L m q : ℕ} [NeZero q] (raw : BinarySourceFormation.RawStore L q)
    (X : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → CyclicRing.Cyclic q)
    (hr : ∀ n o r, BinaryCell.view (BinarySourceFormation.readRaw raw n o r)=X n o r)
    (a b : Mask L m) (forms : Fin (2*(L-m)) → Fin 3 → ℤ) :
    RetainedShiftedFactor.source raw a b forms=source X a b forms := by
  funext x
  unfold RetainedShiftedFactor.source source RetainedShiftedFactor.rawValue BinaryResidualRootProgram.sourcePolynomial
  congr 2
  funext r
  simp only [cropBoth,CroppedSourceContraction.crop]
  split_ifs <;> simp_all

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

noncomputable def raw (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (run : ℤ) (normal : Fin p.L → NormalLetter) (opposite : Fin p.L → OppositeLetter) : CyclicRing.Cyclic f.cyclic :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let stored := graph.permuted.transformed.source.roots.source
  if right then
    rawRightSource
      (MaskedLightSources.rightInput (ThinMatrixBackend.rawRight (ThinMatrixBackend.readRightMatrix
        (BinaryOriginalReader.viewData stored.rightBand.value)))
        (ExactHalfCroppedEmbedding.scanPick p.L p.m) (ExactHalfCroppedEmbedding.shifts p.m).get u v)
      (goodSlots p.L p.m) (cubeMap (constructGoodMaps p.L p.m).1) (cubeMap (constructGoodMaps p.L p.m).2) run normal opposite
  else
    rawLeftSource
      (MaskedLightSources.leftInput (ThinMatrixBackend.rawLeft (ThinMatrixBackend.readLeftMatrix
        (BinaryOriginalReader.viewData stored.leftBand.value)))
        (ExactHalfCroppedEmbedding.scanPick p.L p.m) (ExactHalfCroppedEmbedding.shifts p.m).get u v)
      (goodSlots p.L p.m) (cubeMap (constructGoodMaps p.L p.m).1) (cubeMap (constructGoodMaps p.L p.m).2) run normal opposite

theorem fromInputs_raw (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (right : Bool) (normal : Fin p.L → NormalLetter) (opposite : Fin p.L → OppositeLetter) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    BinaryCell.view (BinarySourceFormation.readRaw (GraphShiftedRootFactors.raw graph u v run right) normal opposite residue)=
      raw graph u v right (SourceFormation.runValue p.m run) normal opposite residue := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  cases right
  · exact ExactHalfGraphSources.left_source f p block input bandL bandR u v run normal opposite residue
  · exact ExactHalfGraphSources.right_source f p block input bandL bandR u v run normal opposite residue

noncomputable def factor (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    RetainedShiftedFactor.Data p.m (p.L-p.m) → Polynomial (CyclicRing.Cyclic f.cyclic) :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  source (raw graph u v right run) (graph.permuted.transformed.source.roots.keys.value.masks.get a)
    (graph.permuted.transformed.source.roots.keys.value.masks.get b) (GraphShiftedRootFactors.forms graph right a b target request)

theorem fromInputs_factor (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (right : Bool) (a b : Fin (goodSlots p.L p.m).card) (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    GraphShiftedRootFactors.source graph u v run right a b input.target request=
      factor graph u v right (SourceFormation.runValue p.m run) a b input.target request := by
  dsimp only
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  apply source_eq
  exact fromInputs_raw f p block input bandL bandR ell u v run right

/-- The exact-half source formula already satisfies the normal cap for every
integer run. Thus the retained double crop is the intended opposite crop. -/
theorem raw_crop (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (run : ℤ) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    cropBoth (p.m/2) (raw graph u v right run)=CroppedSourceContraction.crop (p.m/2) (raw graph u v right run) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  cases right
  · exact ExactHalfResidualWindow.left_crop_eq _ u v run
  · exact ExactHalfResidualWindow.right_crop_eq _ u v run

theorem factor_value (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (x : RetainedShiftedFactor.Data p.m (p.L-p.m)) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    factor graph u v right run a b target request x=
      ((∏ i, GraphShiftedRootFactors.forms graph right a b target request i (x.1 i) : ℤ) : Polynomial (CyclicRing.Cyclic f.cyclic))*
        Polynomial.C (CroppedSourceContraction.crop (p.m/2) (raw graph u v right run)
          (RetainedShiftedFactor.normalInput (graph.permuted.transformed.source.roots.keys.value.masks.get a)
            (graph.permuted.transformed.source.roots.keys.value.masks.get b) x.1 x.2.1)
          (RetainedShiftedFactor.oppositeInput (graph.permuted.transformed.source.roots.keys.value.masks.get a)
            (graph.permuted.transformed.source.roots.keys.value.masks.get b) x.1 x.2.2)) := by
  unfold factor source
  rw [raw_crop]

#print axioms raw_crop
#print axioms factor_value

#print axioms source_eq
#print axioms fromInputs_raw
#print axioms fromInputs_factor
end ThinMatrix.GraphLowRunSources
