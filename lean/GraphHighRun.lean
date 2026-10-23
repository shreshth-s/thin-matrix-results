import CountedCyclicCollection

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! Feed actual retained graph-source stores to cropped HIGH preparation and
all physical queries for one translation pair and common degree run. Source
magnitudes are derived from the original graph tables, not supplied. -/
namespace ThinMatrix.GraphHighRun
open BinaryCell GoodMapEmbedding ExactHalfSourcePlan
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

abbrev Requests (n L m q : ℕ) := Vector (GraphCompletionRequests.Physical L m q) (FoldedBackendExecution.windowQuerySize n)

def execute (graph : GraphPrefixProgram.Prepared f p b ell) (requests : Requests n p.L p.m f.cyclic)
    (bandL bandR : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :=
  CroppedHighQueries.execute p.t (p.m/2) (2^(p.L+p.m)) bandL bandR graph.permuted.transformed.source.roots.source.shape requests
    (GraphShiftedRootFactors.raw graph u v run false) (GraphShiftedRootFactors.raw graph u v run true)

def magnitude (L m t q : ℕ) : ℕ := CroppedHighQueries.queryMagnitude m t (CroppedHighQueries.tableMagnitude L q (2^(L+m)))

noncomputable def budget (n L m t q : ℕ) : ℕ :=
  CroppedHighQueries.budget L m t q (FoldedBackendExecution.windowQuerySize n) (m/2) (2^(L+m))

theorem fromInputs_raw_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (right : Bool) :
    BinaryHighExecution.RawBound (GraphShiftedRootFactors.raw (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v run right) (2^(p.L+p.m)) := by
  intro normal opposite residue
  rw [← Int.natCast_natAbs]
  apply Int.ofNat_le.mpr
  cases right
  · exact ExactHalfSourceBounds.graph_left f p block input bandL bandR u v run normal opposite residue
  · exact ExactHalfSourceBounds.graph_right f p block input bandL bandR u v run normal opposite residue

theorem fromInputs_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (i : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((CroppedHighQueries.get (execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR u v run).value i).get residue)).natAbs ≤ magnitude p.L p.m p.t f.cyclic := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact CroppedHighQueries.execute_bound p.t (p.m/2) (2^(p.L+p.m)) bandL bandR _ requests _ _
    (fromInputs_raw_bound f p block input bandL bandR ell u v run false)
    (fromInputs_raw_bound f p block input bandL bandR ell u v run true) i residue

theorem fromInputs_work (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    (execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) requests bandL bandR u v run).operations ≤ budget n p.L p.m p.t f.cyclic := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact CroppedHighQueries.execute_work p.t (p.m/2) (2^(p.L+p.m)) bandL bandR p.t_le _ requests _ _
    (fromInputs_raw_bound f p block input bandL bandR ell u v run false)
    (fromInputs_raw_bound f p block input bandL bandR ell u v run true)

noncomputable def value (graph : GraphPrefixProgram.Prepared f p b ell) (bandL bandR : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (request : GraphCompletionRequests.Physical p.L p.m f.cyclic) (residue : Fin f.cyclic) : ℤ :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  CroppedHighQueries.value p.t (p.m/2) bandL bandR graph.permuted.transformed.source.roots.source.shape request
    (GraphShiftedRootFactors.raw graph u v run false) (GraphShiftedRootFactors.raw graph u v run true) residue

theorem fromInputs_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (requests : Requests n p.L p.m f.cyclic)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (i : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    view ((CroppedHighQueries.get (execute graph requests bandL bandR u v run).value i).get residue)=
      value graph bandL bandR u v run (requests.get i) residue := by
  dsimp only
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact CroppedHighQueries.execute_value p.t (p.m/2) (2^(p.L+p.m)) bandL bandR _ requests _ _
    (fromInputs_raw_bound f p block input bandL bandR ell u v run false)
    (fromInputs_raw_bound f p block input bandL bandR ell u v run true) i residue

#print axioms fromInputs_raw_bound
#print axioms fromInputs_bound
#print axioms fromInputs_work
#print axioms fromInputs_value
end ThinMatrix.GraphHighRun
