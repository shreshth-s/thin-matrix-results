import GraphShiftedLow

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

/-! Unique mask selection from the actual physical folded request. This is a
value identity for exhaustive mask execution, not an efficient routing claim. -/
namespace ThinMatrix.LowRequestLocator
open GoodMapEmbedding ResidualFamilyKeys ExactHalfSourcePlan TensorContraction
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

def physical (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) : GraphCompletionRequests.Physical p.L p.m f.cyclic :=
  (GraphCompletionRequests.prepare f p graph.permuted.transformed.source.roots.source.shape target).physical.value.get request

noncomputable def runValue (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (residue : Fin f.cyclic) : ℤ :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  weightedLow (2*p.m) p.t (ShiftedLowChannelFormula.pencil
    (GraphShiftedRootFactors.source graph u v run false left right target request)
    (GraphShiftedRootFactors.source graph u v run true right left target request)
    (fun x => x.2.1) (fun x => x.2.2) (fun x => x.2.1) (fun x => x.2.2)) residue

theorem sum_masks {L m C : ℕ} {R : Type*} [AddCommMonoid R]
    (q : GraphCompletionRequests.Physical L m C) (bandL bandR : ℕ)
    (F : Fin (goodSlots L m).card → Fin (goodSlots L m).card → R) :
    (∑ a, ∑ b, if RootRequestSelection.accepts bandL bandR false a b q then F a b else 0)=
      if q.bandL=bandL ∧ q.bandR=bandR then F (RootRequestSelection.rowRank q.row) (RootRequestSelection.rowRank q.column) else 0 := by
  classical
  by_cases h : q.bandL=bandL ∧ q.bandR=bandR
  · simp [RootRequestSelection.accepts,RootRequestSelection.ranks,h.1,h.2,ite_and]
  · have hz : ∀ a b, RootRequestSelection.accepts bandL bandR false a b q=false := by
      intro a b
      simp only [RootRequestSelection.accepts,decide_eq_false_iff_not]
      tauto
    simp [hz,h]

theorem physical_value (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    physical graph target request=(GraphCompletionRequests.locate graph.permuted.transformed.source.roots.source.shape p.m_le_L
      (GraphCompletionRequests.castRequest p.N_eq.symm ((FoldedBackendExecution.requests f (BinaryFoldedFormation.viewTable target)).get request))).value :=
  GraphCompletionRequests.prepare_get _ _ _ _ _

theorem canonical_masks {L m C : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ)
    (q : GraphCompletionRequests.Physical L m C) :
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get (RootRequestSelection.rowRank q.row)).bits.get=
      (RowIndexing.rowUnrank store q.row).1.val ∧
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get (RootRequestSelection.rowRank q.column)).bits.get=
      (RowIndexing.rowUnrank store q.column).1.val := by
  simp only [ResidualFamilyKeys.prepare_masks]
  exact ⟨RootRequestSelection.matched_mask store q.row,RootRequestSelection.matched_mask store q.column⟩

theorem physical_outside (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let q := physical graph target request
    q.outside.get=(ThinMatrixBackend.storedQueryGeometry graph.permuted.transformed.source.roots.source.shape.environment
      (RowIndexing.rowUnrank graph.permuted.transformed.source.roots.source.shape.layout q.row)
      (RowIndexing.rowUnrank graph.permuted.transformed.source.roots.source.shape.layout q.column)).outside := by
  dsimp only
  rw [physical_value]
  exact GraphCompletionRequests.locate_outside _ _ _

theorem fromInputs_masks (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let q := physical graph input.target request
    let roots := graph.permuted.transformed.source.roots
    SourceFormation.cubeSupport (roots.keys.value.masks.get (RootRequestSelection.rowRank q.row)).bits.get=
      (RowIndexing.rowUnrank roots.source.shape.layout q.row).1.val ∧
    SourceFormation.cubeSupport (roots.keys.value.masks.get (RootRequestSelection.rowRank q.column)).bits.get=
      (RowIndexing.rowUnrank roots.source.shape.layout q.column).1.val := by
  dsimp only
  exact canonical_masks _ p.t _

noncomputable def value (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  let q := physical graph target request
  if q.bandL=bandL ∧ q.bandR=bandR then
    ∑ u, ∑ v, ∑ run, runValue graph u v run (RootRequestSelection.rowRank q.row) (RootRequestSelection.rowRank q.column) target request residue
  else 0

theorem family_sum (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (∑ left, ∑ right, ∑ u, ∑ v, ∑ run, GraphShiftedLow.value graph u v run left right target bandL bandR request residue)=
      value graph target bandL bandR request residue := by
  calc
    _ = ∑ left, ∑ right, if RootRequestSelection.accepts bandL bandR false left right (physical graph target request)
        then ∑ u, ∑ v, ∑ run, runValue graph u v run left right target request residue else 0 := by
      apply Finset.sum_congr rfl; intro left _
      apply Finset.sum_congr rfl; intro right _
      change (∑ u, ∑ v, ∑ run, if RootRequestSelection.accepts bandL bandR false left right (physical graph target request)
        then runValue graph u v run left right target request residue else 0)=_
      by_cases ha : RootRequestSelection.accepts bandL bandR false left right (physical graph target request)=true
      · simp only [ha,↓reduceIte]
      · simp [ha]
    _ = _ := sum_masks _ _ _ _

#print axioms physical_outside
#print axioms fromInputs_masks
#print axioms sum_masks
#print axioms physical_value
#print axioms canonical_masks
#print axioms family_sum
end ThinMatrix.LowRequestLocator
