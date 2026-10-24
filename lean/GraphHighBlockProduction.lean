import GraphHighScalarCanonical

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphHighBlockProduction
open BinaryCell SourceFormation
open scoped BigOperators
variable {n h r K : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev B := CompactBlocks.blockCount n h
abbrev Rows := Vector (Vector Cell (B (n:=n) (h:=h))) (M (n:=n))
variable (shape : ThinMatrixBackend.ShapePlan p.L p.m)
  (sources : Fin (B (n:=n) (h:=h)) → GraphRetainedHigh.Sources f p (K:=K))
  (requests : GraphHighRun.Requests n p.L p.m f.cyclic)
  (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)

def block (b : Fin (B (n:=n) (h:=h))) : Program (Vector (Vector Cell 1) (M (n:=n))) :=
  let prep := GraphHighPreparation.execute f p (sources b)
  let out := GraphHighScalarResult.execute p.t shape requests hb prep.value.2
  ⟨out.value,prep.operations+out.operations+8⟩

/-- Retain source stores from the shared pipeline. Each middle block builds
shared encoders and pair tables once, then gathers only requested scalars. -/
def execute : Program (Rows (n:=n) (h:=h)) :=
  let cols := vectorBuild (B (n:=n) (h:=h)) (block f p shape sources requests hb)
  let out := Vector.ofFn (fun i : Fin (M (n:=n)) => Vector.ofFn (fun b =>
    (((cols.value.get b).get i).get ⟨0,by decide⟩)))
  ⟨out,cols.operations+32*M (n:=n)*(B (n:=n) (h:=h)+1)+16⟩

variable (input : BinaryFoldedFormation.Inputs n)
  (hc : ∀ b,GraphRetainedHigh.Correct f p b input (Vector.ofFn (fun a : Fin K => a.val)) (sources b))
  (hshape : shape=GraphSharedTargets.shape f p)
  (hreq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
include hc hreq hshape

theorem correct (i : Fin (M (n:=n))) (b : Fin (B (n:=n) (h:=h))) :
    view (((execute f p shape sources requests hb).value.get i).get b)=
      GraphSelectedNormalize.highValue f p input i b := by
  subst shape
  simp only [execute,Vector.get_ofFn,vectorBuild_get,block]
  exact GraphHighScalarCanonical.correct f p b input (sources b) (hc b) requests hreq hb _ rfl i _

omit hreq hshape in
 theorem table_bound (b : Fin (B (n:=n) (h:=h))) (a a' : Fin K)
    (u v : Fin (ExactHalfSourcePlan.J p.m)) (run : Fin (2*p.m+1)) :
    BinaryHighTable.Bounds.TableBound (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m)))
      ((((((GraphHighPreparation.execute f p (sources b)).value.2.get a).get a').get u).get v).get run) := by
  simp only [GraphHighPreparation.execute,GraphHighPreparation.tables_get]
  exact GraphSelectedHigh.table_bound f p b input _ (sources b) (hc b) a a' u v run

noncomputable def budget : ℕ :=
  B (n:=n) (h:=h)*(GraphHighPreparation.budget p.L p.m p.t f.cyclic K+
    GraphHighScalarResult.budget K p.L p.m p.t (M (n:=n))
      (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m)))+16)+
    32*M (n:=n)*(B (n:=n) (h:=h)+1)+16

omit hreq hshape in
 theorem work : (execute f p shape sources requests hb).operations≤budget f p (K:=K) := by
  have hblock (b : Fin (B (n:=n) (h:=h))) := GraphHighPreparation.execute_work f p b input _ (sources b) (hc b)
  have hquery (b : Fin (B (n:=n) (h:=h))) := GraphHighScalarResult.work p.t shape
    requests hb (GraphHighPreparation.execute f p (sources b)).value.2 _ p.t_le
    (table_bound f p sources input hc b)
  have hb' (b : Fin (B (n:=n) (h:=h))) : (block f p shape sources requests hb b).operations≤
      GraphHighPreparation.budget p.L p.m p.t f.cyclic K+
        GraphHighScalarResult.budget K p.L p.m p.t (M (n:=n))
          (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m)))+8 := by
    dsimp only [block]
    exact Nat.add_le_add_right (Nat.add_le_add (hblock b) (hquery b)) 8
  have hh := vectorBuild_cost (B (n:=n) (h:=h)) _ (block f p shape sources requests hb) hb'
  dsimp only [execute]
  unfold budget
  nlinarith only [hh]

#print axioms correct
#print axioms table_bound
#print axioms work
end ThinMatrix.GraphHighBlockProduction
