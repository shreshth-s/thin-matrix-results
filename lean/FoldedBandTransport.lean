import GraphNormalizedBand

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2400000

/-! Transport the actual binary band copies and decoded local rows to the
original folded matrix-product request. No backend answer is assumed. -/
namespace ThinMatrix.FoldedBandTransport
open BinaryCell ThinMatrixBackend

/-- The binary band-copy implementation at the matching pair, with zero
padding removed using the actual middle-dimension fit. -/
theorem copied_product {N D L m q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (hm : m≤L) (hD : D≤4^m)
    (A : BinaryBackendExecution.OriginalLeft N D q) (B : BinaryBackendExecution.OriginalRight N D q)
    (i j : Fin N) :
    (readLeftMatrix (BinaryOriginalReader.viewData
      (BinaryBackendExecution.makeLeftBandStored shape A (storedLocate shape (tileWidth_pos L m hm) i).1.val).value)*
     readRightMatrix (BinaryOriginalReader.viewData
      (BinaryBackendExecution.makeRightBandStored shape B (storedLocate shape (tileWidth_pos L m hm) j).1.val).value))
      (RowIndexing.rowUnrank shape.layout (storedLocate shape (tileWidth_pos L m hm) i).2)
      (RowIndexing.rowUnrank shape.layout (storedLocate shape (tileWidth_pos L m hm) j).2)=
      (originalLeftMatrix (BinaryBackendExecution.viewLeft A)*originalRightMatrix (BinaryBackendExecution.viewRight B)) i j := by
  rw [BinaryBackendExecution.makeLeftBandStored_view,BinaryBackendExecution.makeRightBandStored_view,
    makeLeftBandStored_refines,makeRightBandStored_refines,makeLeftBand_value,makeRightBand_value]
  simp only [storedLocate_refines,RowIndexing.rowUnrank_value]
  change (rowBand (padMiddleLeft (m:=m) (originalLeftMatrix (BinaryBackendExecution.viewLeft A)))
    (TilingCosts.locate (tileWidth_pos L m hm) i).1 *
    columnBand (padMiddleRight (m:=m) (originalRightMatrix (BinaryBackendExecution.viewRight B)))
    (TilingCosts.locate (tileWidth_pos L m hm) j).1)
    (localRow (tileWidth_pos L m hm) i) (localRow (tileWidth_pos L m hm) j)=_
  rw [genuine_tile_product,padMiddle_product hD]

variable {n h r : ℕ}

def request (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (target : BinaryFoldedFormation.BinaryTable n) (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    TilingCosts.Request p.N f.cyclic :=
  GraphCompletionRequests.castRequest p.N_eq.symm ((FoldedBackendExecution.requests f (BinaryFoldedFormation.viewTable target)).get index)

def physical (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (target : BinaryFoldedFormation.BinaryTable n) (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    GraphCompletionRequests.Physical p.L p.m f.cyclic :=
  (GraphCompletionRequests.locate (BinaryBackendExecution.prepareShapeRuntime p.L p.m) p.m_le_L (request f p target index)).value

theorem physical_fromInputs (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    LowRequestLocator.physical (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target index=
      physical f p input.target index := by
  rw [LowRequestLocator.physical_value]
  rfl

noncomputable def foldedEntry (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (index : Fin (FoldedBackendExecution.windowQuerySize n)) : CyclicRing.Cyclic f.cyclic :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let folded := (ExactHalfGraphSources.execute f p block input 0 0).folded.value
  (originalLeftMatrix (BinaryBackendExecution.viewLeft (p.castLeft folded.left))*
    originalRightMatrix (BinaryBackendExecution.viewRight (p.castRight folded.right)))
    (request f p input.target index).row (request f p input.target index).column

theorem matched_entry (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Fin (FoldedBackendExecution.windowQuerySize n))
    (hl : (physical f p input.target index).bandL=bandL) (hr : (physical f p input.target index).bandR=bandR) :
    GraphLowHighScale.entry (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target index=
      foldedEntry f p block input index := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold GraphLowHighScale.entry
  dsimp only
  rw [physical_fromInputs]
  rw [←hl,←hr]
  exact copied_product _ p.m_le_L p.middle_fit _ _ _ _

theorem normalized_request (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    view (GraphNormalizedBand.output (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR
      index (physical f p input.target index).coefficient)=
      if (physical f p input.target index).bandL=bandL ∧ (physical f p input.target index).bandR=bandR then
        foldedEntry f p block input index (physical f p input.target index).coefficient else 0 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [GraphNormalizedBand.fromInputs_value]
  rw [physical_fromInputs]
  split_ifs with hh
  · rw [matched_entry f p block input bandL bandR ell index hh.1 hh.2]
  · rfl

theorem folded_semantic (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    foldedEntry f p block input index (physical f p input.target index).coefficient=
      let x := (FoldedBackendExecution.windowQueryEquiv n).symm index
      FoldedBackendExecution.semanticCoefficient f block (BinaryFoldedFormation.viewTable input.left)
        (BinaryFoldedFormation.viewTable input.right) (BinaryFoldedFormation.viewTable input.target) x.1.1 x.1.2 x.2 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  cases p with
  | mk L m t width N D raw lowWidth hw hN hD hraw hm ht hfit =>
    subst N D
    unfold foldedEntry physical request GraphCompletionRequests.locate GraphCompletionRequests.castRequest
    simp only [BinaryFoldedFactory.Plan.castLeft,BinaryFoldedFactory.Plan.castRight,Vector.cast_rfl,Fin.cast_eq_self]
    change (originalLeftMatrix (BinaryFoldedFormation.viewLeft (ExactHalfGraphSources.execute f _ block input 0 0).folded.value.left)*
      originalRightMatrix (BinaryFoldedFormation.viewRight (ExactHalfGraphSources.execute f _ block input 0 0).folded.value.right)) _ _ _ = _
    rw [ExactHalfGraphSources.folded_left,ExactHalfGraphSources.folded_right,FoldedBackendExecution.form_product]
    simp only [FoldedBackendExecution.requests,Vector.get_ofFn,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
    rfl

#print axioms copied_product
#print axioms physical_fromInputs
#print axioms matched_entry
#print axioms normalized_request
#print axioms folded_semantic
end ThinMatrix.FoldedBandTransport
