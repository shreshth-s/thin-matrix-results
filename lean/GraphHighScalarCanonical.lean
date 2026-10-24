import GraphHighScalarResult
import GraphSelectedNormalize

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphHighScalarCanonical
open BinaryCell ExactHalfSourcePlan
open scoped BigOperators
variable {n h r K : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
  (sources : GraphRetainedHigh.Sources f p (K:=K))
  (hc : GraphRetainedHigh.Correct f p block input (Vector.ofFn (fun a : Fin K => a.val)) sources)
  (requests : GraphHighRun.Requests n p.L p.m f.cyclic)
  (hreq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
  (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)
  (tables : GraphHighPreparation.Tables p.L p.m f.cyclic K)
  (htables : tables=(GraphHighPreparation.execute f p sources).value.2)

include hc hreq htables

theorem scalar (j : Fin (FoldedBackendExecution.windowQuerySize n))
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    GraphHighScalarResult.scalar p.t (GraphSharedTargets.shape f p) requests hb tables j u v run=
      GraphHighRun.value (GraphOwnRootSpec.graph f p input block j)
        (GraphOwnRootSpec.physical f p input.target j).bandL (GraphOwnRootSpec.physical f p input.target j).bandR
        u v run (GraphOwnRootSpec.physical f p input.target j) (GraphOwnRootSpec.physical f p input.target j).coefficient := by
  let q := requests.get j
  have hq : q=GraphOwnRootSpec.physical f p input.target j := by dsimp only [q];rw [hreq];rfl
  have hi := GraphHighRun.fromInputs_value f p block input q.bandL q.bandR 0 requests u v run j q.coefficient
  dsimp only at hi
  unfold GraphHighScalarResult.scalar GraphHighScalarResult.ownTable
  rw [htables,GraphHighPreparation.execute_get f p block input _ sources hc]
  simp only [Vector.get_ofFn]
  have he : view ((CroppedHighQueries.get (GraphHighRun.execute
      (GraphPrefixProgram.fromInputs f p block input q.bandL q.bandR 0) requests q.bandL q.bandR u v run).value j).get q.coefficient)=
      view ((SelectedHighQueries.lookup p.t (GraphSharedTargets.shape f p) q
        (BinaryCroppedHighBoxes.execute p.L p.m p.t f.cyclic (p.m/2) (2^(p.L+p.m))
          (RetainedHighSources.raw (ExactHalfGraphSources.execute f p block input q.bandL q.bandR).sources.value false u v run)
          (RetainedHighSources.raw (ExactHalfGraphSources.execute f p block input q.bandL q.bandR).sources.value true u v run)).boxes).value) := by
    simp only [q,GraphHighRun.execute,CroppedHighQueries.get,CroppedHighQueries.execute,
      GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn,CroppedHighQueries.row_value,
      CroppedHighQueries.accepts,and_self,decide_true,ite_true]
    rfl
  exact he.symm.trans (by simpa only [hq,hreq,GraphOwnRootSpec.graph,GraphOwnRootSpec.physical] using hi)

theorem correct (j : Fin (FoldedBackendExecution.windowQuerySize n)) (c : Fin 1) :
    view (((GraphHighScalarResult.execute p.t (GraphSharedTargets.shape f p) requests hb tables).value.get j).get c)=
      GraphSelectedNormalize.highValue f p input j block := by
  rw [GraphHighScalarResult.value]
  simp_rw [scalar f p block input sources hc requests hreq hb tables htables]
  unfold GraphSelectedNormalize.highValue GraphOwnRootSpec.graph
  rw [GraphHighFamily.fromInputs_value]
  rfl

#print axioms scalar
#print axioms correct
end ThinMatrix.GraphHighScalarCanonical
