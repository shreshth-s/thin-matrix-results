import GraphLowMaskAssembly
import GraphLowRunSources

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1800000

/-! Complete mask aggregation and shared degree-run recombination for the
executed LOW functional of one retained block/band pair. The expression uses
original masked Walsh sources of the actual folded bands and physical request
locators. HIGH, complete-count normalization and fast scheduling remain open. -/
namespace ThinMatrix.GraphLowRecombination
open GoodMapEmbedding ExactHalfSourcePlan TensorContraction BinaryCell
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

noncomputable def runValue (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m)) (run : ℤ)
    (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  weightedLow (2*p.m) p.t (ShiftedLowChannelFormula.pencil
    (GraphLowRunSources.factor graph u v false run left right target request)
    (GraphLowRunSources.factor graph u v true run right left target request)
    (fun x => x.2.1) (fun x => x.2.2) (fun x => x.2.1) (fun x => x.2.2)) residue

theorem fromInputs_run (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (left right : Fin (goodSlots p.L p.m).card) (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    LowRequestLocator.runValue graph u v run left right input.target request residue=
      runValue graph u v (SourceFormation.runValue p.m run) left right input.target request residue := by
  dsimp only
  unfold LowRequestLocator.runValue runValue
  rw [GraphLowRunSources.fromInputs_factor,GraphLowRunSources.fromInputs_factor]

noncomputable def value (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  let q := LowRequestLocator.physical graph target request
  if q.bandL=bandL ∧ q.bandR=bandR then
    ∑ u, ∑ v, ∑ d∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ),
      runValue graph u v d (RootRequestSelection.rowRank q.row) (RootRequestSelection.rowRank q.column) target request residue
  else 0

theorem fromInputs_semantics (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    LowRequestLocator.value graph input.target bandL bandR request residue=
      value graph input.target bandL bandR request residue := by
  dsimp only
  unfold LowRequestLocator.value value
  dsimp only
  split
  · apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro v _
    simp_rw [fromInputs_run]
    exact RetainedDegreeRuns.sum_runs p.m (fun d => runValue
      (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v d
      (RootRequestSelection.rowRank (LowRequestLocator.physical (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target request).row)
      (RootRequestSelection.rowRank (LowRequestLocator.physical (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target request).column)
      input.target request residue)
  · rfl

theorem fromInputs_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    view ((RootProductCollection.output (GraphLowMaskAssembly.execute graph input.target bandL bandR).value request).get residue)=
      value graph input.target bandL bandR request residue := by
  dsimp only
  rw [GraphLowMaskAssembly.fromInputs_value,fromInputs_semantics]

#print axioms fromInputs_run
#print axioms fromInputs_semantics
#print axioms fromInputs_value
end ThinMatrix.GraphLowRecombination
