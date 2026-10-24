import GraphRetainedHigh

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 10000

/-! Scalar HIGH queries consume retained pair tables and preserve original
request IDs. Both source encoders were shared before pair-table construction.
Only the requested cyclic coefficient is read for each occurrence. -/
namespace ThinMatrix.GraphSelectedHigh
open ExactHalfSourcePlan RetainedHighSources
variable {n h r K M : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
  (ids : Vector ℕ K) (sources : GraphRetainedHigh.Sources f p (K:=K))
  (hc : GraphRetainedHigh.Correct f p block input ids sources)
include hc

 theorem table_bound (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    BinaryHighTable.Bounds.TableBound (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m)))
      (GraphRetainedHigh.boxes f p (bank p.t (p.m/2) sources).value
        (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run).value := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [GraphRetainedHigh.boxes_match f p block input ids sources hc]
  exact CroppedHighQueries.table_bound _ _ _ _
    (GraphRetainedHigh.raw_bound f p block input _ _ false u v run)
    (GraphRetainedHigh.raw_bound f p block input _ _ true u v run)

variable (shape : ThinMatrixBackend.ShapePlan p.L p.m)
  (requests : Vector (GraphCompletionRequests.Physical p.L p.m f.cyclic) M)

/-- The table is retained input; this query performs no preprocessing. -/
def query (indices : List (Fin M)) (table : BinaryHighTable.Table f.cyclic) :=
  SelectedHighQueries.query p.t shape requests indices table

omit hc in
 theorem query_ids (indices : List (Fin M)) (table : BinaryHighTable.Table f.cyclic) :
    (query f p shape requests indices table).value.indices=indices := rfl

 theorem query_work (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (indices : List (Fin M)) :
    (query f p shape requests indices
      (GraphRetainedHigh.boxes f p (bank p.t (p.m/2) sources).value
        (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run).value).operations ≤
    indices.length*(SelectedHighQueries.rowBudget p.L p.m p.t
      (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m)))+32)+8 :=
  SelectedHighQueries.query_work _ _ p.t_le _ _ _ _ (table_bound f p block input ids sources hc a b u v run)

 theorem query_bound (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (indices : List (Fin M)) (i : Fin indices.length) :
    (((query f p shape requests indices
      (GraphRetainedHigh.boxes f p (bank p.t (p.m/2) sources).value
        (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run).value).value.values.get i).view).natAbs ≤
      GraphHighRun.magnitude p.L p.m p.t f.cyclic := by
  unfold query
  rw [SelectedHighQueries.query_value]
  exact SelectedHighQueries.lookup_bound _ _ _ _ _ (table_bound f p block input ids sources hc a b u v run)

 theorem query_matches (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (indices : List (Fin M)) (i : Fin indices.length)
    (hown : ∀ j∈indices,CroppedHighQueries.accepts (ids.get a) (ids.get b) (requests.get j)=true) :
    ((query f p shape requests indices
      (GraphRetainedHigh.boxes f p (bank p.t (p.m/2) sources).value
        (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run).value).value.values.get i).view=
      BinaryCell.view ((CroppedHighQueries.get (CroppedHighQueries.execute p.t (p.m/2) (2^(p.L+p.m))
        (ids.get a) (ids.get b) shape requests
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value false u v run)
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value true u v run)).value
        (indices.get i)).get (requests.get (indices.get i)).coefficient) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [GraphRetainedHigh.boxes_match f p block input ids sources hc]
  exact SelectedHighQueries.stored_matches _ _ _ _ _ _ _ _ _ _ _ hown

 theorem routed_matches
    (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)
    (hid : ∀ i,ids.get i=i.val) (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i : Fin (SelectedHighQueries.ids (SelectedHighQueries.route requests hb).value a b).value.length) :
    ((query f p shape requests (SelectedHighQueries.ids (SelectedHighQueries.route requests hb).value a b).value
      (GraphRetainedHigh.boxes f p (bank p.t (p.m/2) sources).value
        (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run).value).value.values.get i).view=
      BinaryCell.view ((CroppedHighQueries.get (CroppedHighQueries.execute p.t (p.m/2) (2^(p.L+p.m))
        (ids.get a) (ids.get b) shape requests
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value false u v run)
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value true u v run)).value
        ((SelectedHighQueries.ids (SelectedHighQueries.route requests hb).value a b).value.get i)).get
        (requests.get ((SelectedHighQueries.ids (SelectedHighQueries.route requests hb).value a b).value.get i)).coefficient) := by
  apply query_matches f p block input ids sources hc shape requests
  intro j hj
  rw [hid a,hid b]
  exact (SelectedHighQueries.ids_mem requests hb a b j).mp hj

#print axioms table_bound
#print axioms query_ids
#print axioms query_work
#print axioms query_bound
#print axioms query_matches
#print axioms routed_matches
end ThinMatrix.GraphSelectedHigh
