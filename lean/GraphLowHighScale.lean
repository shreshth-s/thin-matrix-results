import CroppedPhysicalContraction

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3200000

/-! Scale identity for the joined, executed exact-half families on retained
folded bands. This is one block and band pair, before outer scheduling. -/
namespace ThinMatrix.GraphLowHighScale
open WalshEmbedding GoodMapEmbedding GoodSetConstruction CompleteThinProduct
open GraphLowHighJoin PhysicalShiftedForms GraphPhysicalQueries ExactHalfSourcePlan
open scoped BigOperators
variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

noncomputable def entry (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n)) : CyclicRing.Cyclic f.cyclic :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let stored := graph.permuted.transformed.source.roots.source
  let q := LowRequestLocator.physical graph target request
  (ThinMatrixBackend.readLeftMatrix (BinaryOriginalReader.viewData stored.leftBand.value)*
    ThinMatrixBackend.readRightMatrix (BinaryOriginalReader.viewData stored.rightBand.value))
      (RowIndexing.rowUnrank stored.shape.layout q.row) (RowIndexing.rowUnrank stored.shape.layout q.column)

theorem summed_inner (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    (∑ u, ∑ v, ∑ run∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ), inner graph target request u v run)=
      (4:CyclicRing.Cyclic f.cyclic)^p.L*entry graph target request := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let stored := graph.permuted.transformed.source.roots.source
  let q := LowRequestLocator.physical graph target request
  let row := RowIndexing.rowUnrank stored.shape.layout q.row
  let col := RowIndexing.rowUnrank stored.shape.layout q.column
  let A : Matrix (ThinMatrixBackend.OuterIndex p.L p.m) (ThinMatrixBackend.InnerIndex p.m) (CyclicRing.Cyclic f.cyclic) := ThinMatrixBackend.readLeftMatrix (BinaryOriginalReader.viewData stored.leftBand.value)
  let B : Matrix (ThinMatrixBackend.InnerIndex p.m) (ThinMatrixBackend.OuterIndex p.L p.m) (CyclicRing.Cyclic f.cyclic) := ThinMatrixBackend.readRightMatrix (BinaryOriginalReader.viewData stored.rightBand.value)
  have hout := LowRequestLocator.physical_outside graph target request
  dsimp only at hout
  rw [ThinMatrixBackend.storedQueryGeometry_outside (q:=f.cyclic)] at hout
  unfold GraphLowHighJoin.inner
  dsimp only
  rw [hout]
  change (∑ u, ∑ v, ∑ run∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ),
    TensorContraction.bilinear
      (absorbedInput (ThinMatrixBackend.queryGeometry p.L p.m f.cyclic row col).embedding
        (ThinMatrixBackend.queryGeometry p.L p.m f.cyclic row col).outside
        (source graph u v false run) (lift true))
      (absorbedInput (ThinMatrixBackend.queryGeometry p.L p.m f.cyclic row col).embedding
        (ThinMatrixBackend.queryGeometry p.L p.m f.cyclic row col).outside
        (source graph u v true run) (lift false))
      (fun a b => ∏ i, fullKernel
        (fun j => lift true ((ThinMatrixBackend.queryGeometry p.L p.m f.cyclic row col).embedding j))
        (fun j => lift false ((ThinMatrixBackend.queryGeometry p.L p.m f.cyclic row col).embedding j)) i a b)) =
      (4:CyclicRing.Cyclic f.cyclic)^p.L*(A*B) row col
  unfold GraphPhysicalQueries.source GraphLowRunSources.raw
  simp only [Bool.false_eq_true,↓reduceIte]
  simp only [ThinMatrixBackend.queryGeometry,ThinMatrixBackend.compactQuery,constructedSourceQuery,
    SourceQueryData.embedding,SourceQueryData.outside]
  simp_rw [CroppedPhysicalContraction.contraction]
  have he := ExactHalfCroppedEmbedding.complete_embedding p.L p.m p.m_le_L
    (ThinMatrixBackend.rawLeft A) (ThinMatrixBackend.rawRight B) row.1.val col.1.val row.1.property col.1.property
    (ThinMatrixBackend.expandOutside row.1.val (goodSlots_size p.L p.m row.1.val row.1.property) row.2.1)
    (ThinMatrixBackend.expandOutside col.1.val (goodSlots_size p.L p.m col.1.val col.1.property) col.2.1)
    row.2.2 col.2.2
  simpa only [A,B,stored,ThinMatrixBackend.rawLeft_at,ThinMatrixBackend.rawRight_at,Matrix.mul_apply,
    ThinMatrixBackend.InnerIndex,Fintype.sum_prod_type] using he

theorem fromInputs_scale (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let q := LowRequestLocator.physical graph input.target request
    BinaryCell.view ((RootProductCollection.output (GraphLowMaskAssembly.execute graph input.target bandL bandR).value request).get residue)+
      BinaryCell.view ((CountedCyclicCollection.output (GraphHighFamily.execute graph input.target bandL bandR).2.value request).get residue)=
      (4:ℤ)^p.L*(if q.bandL=bandL ∧ q.bandR=bandR then entry graph input.target request residue else 0) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  dsimp only
  rw [joined_fromInputs]
  split_ifs
  · have he := congrArg (fun z : CyclicRing.Cyclic f.cyclic => z residue)
      (summed_inner (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target request)
    rw [←Int.cast_ofNat (R:=CyclicRing.Cyclic f.cyclic) (n:=4),←Int.cast_pow,SourceCoordinates.intCast_mul_coeff] at he
    simpa only [CyclicRing.sum_coeff] using he
  · rw [mul_zero]

#print axioms summed_inner
#print axioms fromInputs_scale
end ThinMatrix.GraphLowHighScale
