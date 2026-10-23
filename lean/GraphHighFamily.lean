import GraphHighRun

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Share request preparation, execute HIGH on every retained translation
pair and common run, and accumulate all request/cyclic coefficients. All
children and rejected queries remain retained and charged. This is finite
HIGH correctness, not a normalized LOW/HIGH count or an asymptotic bound. -/
namespace ThinMatrix.GraphHighFamily
open BinaryCell ExactHalfSourcePlan GraphHighRun
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

def runs (graph : GraphPrefixProgram.Prepared f p b ell) (requests : Requests n p.L p.m f.cyclic)
    (bandL bandR : ℕ) (u v : Fin (J p.m)) :=
  CountedCyclicCollection.execute (((graph.permuted.transformed.source.roots.source.sources.value.get u).get v).1) (fun run => GraphHighRun.execute graph requests bandL bandR u v run) CroppedHighQueries.get

noncomputable def runsBudget (n L m t q : ℕ) : ℕ :=
  CountedCyclicCollection.budget (fun _ : Fin (2*m+1) => GraphHighRun.budget n L m t q) (FoldedBackendExecution.windowQuerySize n) q (GraphHighRun.magnitude L m t q)

theorem runs_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
    (u v : Fin (J p.m)) (i : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((CountedCyclicCollection.output (runs (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR u v).value i).get residue)).natAbs ≤ (2*p.m+1)*(GraphHighRun.magnitude p.L p.m p.t f.cyclic) := by
  apply CountedCyclicCollection.execute_bound
  intro run
  exact GraphHighRun.fromInputs_bound f p block input bandL bandR ell requests u v run

theorem runs_work (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
    (u v : Fin (J p.m)) :
    (runs (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR u v).operations ≤ runsBudget n p.L p.m p.t f.cyclic := by
  apply CountedCyclicCollection.execute_work
  · intro run
    exact GraphHighRun.fromInputs_bound f p block input bandL bandR ell requests u v run
  · intro run
    exact GraphHighRun.fromInputs_work f p block input bandL bandR ell requests u v run

#print axioms runs_bound
#print axioms runs_work

def rightTranslations (graph : GraphPrefixProgram.Prepared f p b ell) (requests : Requests n p.L p.m f.cyclic)
    (bandL bandR : ℕ) (u : Fin (J p.m)) :=
  CountedCyclicCollection.execute (graph.permuted.transformed.source.roots.source.sources.value.get u) (fun v => runs graph requests bandL bandR u v) CountedCyclicCollection.output

noncomputable def rightTranslationsBudget (n L m t q : ℕ) : ℕ :=
  CountedCyclicCollection.budget (fun _ : Fin (J m) => runsBudget n L m t q) (FoldedBackendExecution.windowQuerySize n) q ((2*m+1)*GraphHighRun.magnitude L m t q)

theorem rightTranslations_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
    (u : Fin (J p.m)) (i : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((CountedCyclicCollection.output (rightTranslations (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR u).value i).get residue)).natAbs ≤ (J p.m)*((2*p.m+1)*GraphHighRun.magnitude p.L p.m p.t f.cyclic) := by
  apply CountedCyclicCollection.execute_bound
  intro v
  exact runs_bound f p block input bandL bandR ell requests u v

theorem rightTranslations_work (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
    (u : Fin (J p.m)) :
    (rightTranslations (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR u).operations ≤ rightTranslationsBudget n p.L p.m p.t f.cyclic := by
  apply CountedCyclicCollection.execute_work
  · intro v
    exact runs_bound f p block input bandL bandR ell requests u v
  · intro v
    exact runs_work f p block input bandL bandR ell requests u v

#print axioms rightTranslations_bound
#print axioms rightTranslations_work

def all (graph : GraphPrefixProgram.Prepared f p b ell) (requests : Requests n p.L p.m f.cyclic)
    (bandL bandR : ℕ)  :=
  CountedCyclicCollection.execute (graph.permuted.transformed.source.roots.source.sources.value) (fun u => rightTranslations graph requests bandL bandR u) CountedCyclicCollection.output

noncomputable def allBudget (n L m t q : ℕ) : ℕ :=
  CountedCyclicCollection.budget (fun _ : Fin (J m) => rightTranslationsBudget n L m t q) (FoldedBackendExecution.windowQuerySize n) q (J m*((2*m+1)*GraphHighRun.magnitude L m t q))

theorem all_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
     (i : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((CountedCyclicCollection.output (all (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR ).value i).get residue)).natAbs ≤ (J p.m)*(J p.m*((2*p.m+1)*GraphHighRun.magnitude p.L p.m p.t f.cyclic)) := by
  apply CountedCyclicCollection.execute_bound
  intro u
  exact rightTranslations_bound f p block input bandL bandR ell requests u

theorem all_work (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
     :
    (all (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR ).operations ≤ allBudget n p.L p.m p.t f.cyclic := by
  apply CountedCyclicCollection.execute_work
  · intro u
    exact rightTranslations_bound f p block input bandL bandR ell requests u
  · intro u
    exact rightTranslations_work f p block input bandL bandR ell requests u

#print axioms all_bound
#print axioms all_work

def execute (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :=
  let targets := GraphCompletionRequests.prepare f p graph.permuted.transformed.source.roots.source.shape target
  (targets,all graph targets.physical.value bandL bandR)

def work (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) : ℕ :=
  let out := execute graph target bandL bandR
  out.1.folded.geometry.bitSteps+out.1.folded.requests.bitSteps+out.1.physical.bitSteps+out.1.physical.control+out.2.operations+16

noncomputable def budget (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  let B := GraphCompletionRequests.metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic
  10000*(B+1)^2+2000000*FoldedBackendExecution.windowQuerySize n*(GraphTargetWidth.width target+B+10)^2+
    (FoldedBackendExecution.windowQuerySize n*(1000*(p.L+p.m+1)^5+32)+8)+allBudget n p.L p.m p.t f.cyclic+16

theorem fromInputs_work (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    work (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR ≤ budget f p input.target := by
  let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
  let targets := GraphCompletionRequests.prepare f p graph.permuted.transformed.source.roots.source.shape input.target
  have ht := GraphTargetWidth.prepare_formation_bits f p graph.permuted.transformed.source.roots.source.shape input.target
  have hc := GraphCompletionRequests.prepare_control f p graph.permuted.transformed.source.roots.source.shape input.target
  have hz := GraphCompletionRequests.prepare_bits f p graph.permuted.transformed.source.roots.source.shape input.target
  have ha := all_work f p block input bandL bandR ell targets.physical.value
  dsimp only at ht
  change targets.folded.geometry.bitSteps+targets.folded.requests.bitSteps+targets.physical.bitSteps+targets.physical.control+
    (all graph targets.physical.value bandL bandR).operations+16 ≤ _
  dsimp only [targets, graph] at ht hc hz ha ⊢
  dsimp only [budget]
  omega

theorem fromInputs_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    view ((CountedCyclicCollection.output (execute graph input.target bandL bandR).2.value request).get residue)=
      ∑ u, ∑ v, ∑ run, GraphHighRun.value graph bandL bandR u v run (LowRequestLocator.physical graph input.target request) residue := by
  dsimp only
  simp only [execute,all,rightTranslations,runs,CountedCyclicCollection.execute_value]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro run _
  exact GraphHighRun.fromInputs_value f p block input bandL bandR ell _ u v run request residue

theorem fromInputs_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    (view ((CountedCyclicCollection.output (execute graph input.target bandL bandR).2.value request).get residue)).natAbs ≤
      J p.m*(J p.m*((2*p.m+1)*GraphHighRun.magnitude p.L p.m p.t f.cyclic)) := by
  dsimp only
  exact all_bound f p block input bandL bandR ell _ request residue

#print axioms fromInputs_work
#print axioms fromInputs_value
#print axioms fromInputs_bound
end ThinMatrix.GraphHighFamily
