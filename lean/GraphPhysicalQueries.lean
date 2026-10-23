import CroppedHighCyclic

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2500000

/-! Identify executed LOW and HIGH with the same physical-query operators
on the actual input-derived, cropped Walsh sources. -/
namespace ThinMatrix.GraphPhysicalQueries
open CompleteThinProduct PhysicalShiftedForms PhysicalLowHighGeometry GraphPhysicalLow
open GoodMapEmbedding ExactHalfSourcePlan
open scoped BigOperators
variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

noncomputable def source (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (run : ℤ) (w : SourceWord p.L) : CyclicRing.Cyclic f.cyclic :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  CroppedSourceContraction.crop (p.m/2) (GraphLowRunSources.raw graph u v right run) w.1 w.2

theorem stored_source (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (u v : Fin (J p.m))
    (run : Fin (2*p.m+1)) (right : Bool) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    CroppedHighCyclic.source (p.m/2) (GraphShiftedRootFactors.raw graph u v run right)=
      source graph u v right (SourceFormation.runValue p.m run) := by
  dsimp only
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  funext w residue
  unfold CroppedHighCyclic.source source CroppedSourceContraction.crop
  split
  · exact GraphLowRunSources.fromInputs_raw f p block input bandL bandR ell u v run right w.1 w.2 residue
  · rfl

theorem absorbed_left (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m)) (run : ℤ)
    (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (w : SourceWord p.L) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    GraphPhysicalLow.absorbed graph u v false run a b target request w=
      Polynomial.C (absorbedInput (embedding (mask graph a) (mask graph b))
        (LowRequestLocator.physical graph target request).outside.get (source graph u v false run) (lift true) w) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold GraphPhysicalLow.absorbed absorbedInput
  rw [←outside_left]
  simp only [source,map_mul,map_intCast,mul_comm]

theorem absorbed_right (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m)) (run : ℤ)
    (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (w : SourceWord p.L) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    GraphPhysicalLow.absorbed graph u v true run b a target request w=
      Polynomial.C (absorbedInput (embedding (mask graph a) (mask graph b))
        (LowRequestLocator.physical graph target request).outside.get (source graph u v true run) (lift false) w) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold GraphPhysicalLow.absorbed absorbedInput
  rw [←outside_right]
  simp only [source,map_mul,map_intCast,mul_comm]

theorem pencil_query (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m)) (run : ℤ)
    (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    GraphPhysicalLow.pencil graph u v run a b target request=
      TensorContraction.pencilQuery (2*p.m)
        (absorbedInput (embedding (mask graph a) (mask graph b)) (LowRequestLocator.physical graph target request).outside.get
          (source graph u v false run) (lift true))
        (absorbedInput (embedding (mask graph a) (mask graph b)) (LowRequestLocator.physical graph target request).outside.get
          (source graph u v true run) (lift false))
        (privateKernel (fun i => lift true (embedding (mask graph a) (mask graph b) i))
          (fun i => lift false (embedding (mask graph a) (mask graph b) i)))
        (fullKernel (fun i => lift true (embedding (mask graph a) (mask graph b) i))
          (fun i => lift false (embedding (mask graph a) (mask graph b) i))) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold GraphPhysicalLow.pencil TensorContraction.pencilQuery TensorContraction.bilinear
  simp_rw [absorbed_left,absorbed_right,PhysicalLowHighGeometry.kernel]
  rfl

theorem matched_embedding (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let q := LowRequestLocator.physical graph input.target request
    embedding (mask graph (RootRequestSelection.rowRank q.row)) (mask graph (RootRequestSelection.rowRank q.column))=
      (CroppedHighQueries.geometry graph.permuted.transformed.source.roots.source.shape q).embedding := by
  dsimp only
  obtain ⟨ha,hb⟩ := LowRequestLocator.fromInputs_masks f p block input bandL bandR ell request
  unfold embedding CroppedHighQueries.geometry BinaryBackendExecution.queryGeometry BinaryBackendExecution.physicalEmbeddingRuntime
  simp only [PhysicalSupportProducts.support,mask,ha,hb]
  rfl

#print axioms stored_source
#print axioms absorbed_left
#print axioms absorbed_right
#print axioms pencil_query
#print axioms matched_embedding
end ThinMatrix.GraphPhysicalQueries
