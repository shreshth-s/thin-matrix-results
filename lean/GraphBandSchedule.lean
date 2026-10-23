import RetainedBandIndices

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-! Exhaustive retained band scheduling for one graph block. Each child runs
formation, both families, normalization and coefficient extraction. All band
pairs, including unmatched pairs, are retained. Recorded preparation charges
are propagated, including translation numerator arithmetic and binary-state
updates. Selection/power-table control and binary address prices are still
missing from the earlier preparation model. `operations` below is an
explicit mixed partial ledger, never a complete binary running-time theorem. -/
namespace ThinMatrix.GraphBandSchedule
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open FoldedBandTransport FoldedRequestBounds
open scoped BigOperators
variable {n h r : ℕ}

def preparationRecorded {b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) : ℕ :=
  let windows := graph.permuted.transformed.source
  let roots := windows.roots
  let src := roots.source
  src.shape.operations+src.selectors.bitSteps+src.selectors.control+src.folded.bitSteps+
    src.leftBand.operations+src.rightBand.operations+src.sources.operations+
    roots.keys.bitSteps+roots.keys.control+roots.roots.bitSteps+roots.roots.control+
    windows.windows.bitSteps+windows.windows.control+
    graph.permuted.transformed.transformed.bitSteps+graph.permuted.transformed.transformed.control+
    graph.permuted.permuted.bitSteps+graph.permuted.permuted.control+graph.encoded.bitSteps+graph.encoded.control

def band (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (a b ell : ℕ) :=
  let out := NormalizedCoefficientCollection.execute f p block input a b ell
  let rows := tabulate out.2.2.value (fun i => (⟨Vector.replicate 1 (out.2.2.value.get i),0,8⟩ : Run (Vector Cell 1)))
  let low := out.2.1.1
  let high := out.2.1.2.1
  let normalized := out.2.1.2.2.2.2
  let charge := preparationRecorded out.1+low.bitSteps+low.control+
    high.1.folded.geometry.bitSteps+high.1.folded.requests.bitSteps+high.1.physical.bitSteps+
    high.1.physical.control+high.2.operations+16+
    normalized.1.bitSteps+normalized.1.control+normalized.2.bitSteps+normalized.2.control+
    64*FoldedBackendExecution.windowQuerySize n+16+out.2.2.bitSteps+out.2.2.control+rows.bitSteps+rows.control+8
  (⟨(out,rows),charge⟩ : ToomCook.Counted _)

theorem band_value (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (a b ell : ℕ)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) (j : Fin 1) :
    view (((band f p block input a b ell).value.2.value.get i).get j)=
      if (physical f p input.target i).bandL=a ∧ (physical f p input.target i).bandR=b then count f block input i else 0 := by
  simp only [band,tabulate_get,Vector.get_replicate,NormalizedCoefficientCollection.execute_value]

theorem band_bound (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (a b ell : ℕ)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) (j : Fin 1) :
    (view (((band f p block input a b ell).value.2.value.get i).get j)).natAbs≤h := by
  rw [band_value]; split_ifs
  · exact count_bound f block input i
  · simp

def execute (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) :=
  let shape := BinaryBackendExecution.prepareShapeRuntime p.L p.m
  let ids := RetainedBandIndices.produce shape p.N
  let all := CountedCyclicCollection.execute ids.value (fun a =>
    CountedCyclicCollection.execute ids.value (fun b => band f p block input (ids.value.get a).val (ids.value.get b).val ell)
      (fun child i => child.2.value.get i)) CountedCyclicCollection.output
  (shape,ids,all)

def output (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (ell : ℕ)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) : Cell :=
  (CountedCyclicCollection.output (execute f p block input ell).2.2.value i).get 0

theorem execute_value (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (ell : ℕ)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) : view (output f p block input ell i)=count f block input i := by
  simp only [output,execute,CountedCyclicCollection.execute_value,RetainedBandIndices.produce_get,band_value]
  exact sum_bands f p input.target i _

theorem execute_bound (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (ell : ℕ)
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) : (view (output f p block input ell i)).natAbs≤h := by
  rw [execute_value]; exact count_bound f block input i

noncomputable def accumulationBudget (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) : ℕ :=
  let S := TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)
  CountedCyclicCollection.budget (fun a : Fin S => CountedCyclicCollection.budget
    (fun b : Fin S => (band f p block input a.val b.val ell).operations)
    (FoldedBackendExecution.windowQuerySize n) 1 h) (FoldedBackendExecution.windowQuerySize n) 1 (S*h)

theorem execute_accumulation_work (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (ell : ℕ) :
    (execute f p block input ell).2.2.operations≤accumulationBudget f p block input ell := by
  unfold execute accumulationBudget
  dsimp only
  apply CountedCyclicCollection.execute_work
  · intro a i j
    apply CountedCyclicCollection.execute_bound
    intro b i j
    exact band_bound f p block input _ _ ell i j
  · intro a
    apply CountedCyclicCollection.execute_work
    · intro b i j
      exact band_bound f p block input _ _ ell i j
    · intro b
      simp only [RetainedBandIndices.produce_get]
      exact le_refl _

#print axioms band_value
#print axioms band_bound
#print axioms execute_value
#print axioms execute_bound
#print axioms execute_accumulation_work
end ThinMatrix.GraphBandSchedule
