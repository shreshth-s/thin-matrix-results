import GraphPhysicalLow
import BinaryCroppedHighBoxes

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Execute physical HIGH key generation, lookup and accumulation for every
request and cyclic coefficient. Rejected band requests are executed first,
then copied or zeroed. Work combines the existing binary arithmetic and
indexed-register charges; it is not a binary-address machine bound. -/
namespace ThinMatrix.CroppedHighQueries
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GoodMapEmbedding
open scoped BigOperators

def geometry {L m q : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) : ThinMatrixBackend.QueryMetadata L m :=
  BinaryBackendExecution.queryGeometry shape.environment
    (RowIndexing.rowUnrank shape.layout request.row) (RowIndexing.rowUnrank shape.layout request.column)

def accepts {L m q : ℕ} (bandL bandR : ℕ) (request : GraphCompletionRequests.Physical L m q) : Bool :=
  decide (request.bandL=bandL ∧ request.bandR=bandR)

structure Row (L m q : ℕ) where
  metadata : ThinMatrixBackend.QueryMetadata L m
  queries : Vector (ToomCook.Counted Cell) q
  payload : Vector Cell q
  selected : Run (RootRequestSelection.Selected q)

def row {L m q : ℕ} (t bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q) : ToomCook.Counted (Row L m q) :=
  let d := geometry shape request
  let queries := Vector.ofFn (fun r => BinaryHighTable.query t d.embedding request.outside table r)
  let payload := GroupedPreparation.ofStoredFn queries (fun r => (queries.get r).value)
  let selected := RootRequestSelection.selectRow (accepts bandL bandR request) payload
  ⟨⟨d,queries,payload,selected⟩,(∑ r, (queries.get r).operations)+selected.bitSteps+selected.control+1000*(L+m+1)^5+32*q+16⟩

def output {L m q : ℕ} (r : Row L m q) : Vector Cell q := r.selected.value.output

theorem row_value {L m q : ℕ} (t bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q) (residue : Fin q) :
    view ((output (row t bandL bandR shape request table).value).get residue)=
      if accepts bandL bandR request then (BinaryHighTable.query t (geometry shape request).embedding request.outside table residue).value.view else 0 := by
  simp only [output,row,RootRequestSelection.selectRow_value,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn]
  rfl

def queryMagnitude (m t A : ℕ) : ℕ := ((2*m).choose t*4^t)*A

theorem row_bound {L m q : ℕ} (t bandL bandR A : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q)
    (hA : BinaryHighTable.Bounds.TableBound A table) (residue : Fin q) :
    (view ((output (row t bandL bandR shape request table).value).get residue)).natAbs≤queryMagnitude m t A := by
  rw [row_value]
  split
  · exact BinaryHighTable.query_bound t A _ _ _ _ hA
  · exact Nat.zero_le _

def rowBudget (L m t q A : ℕ) : ℕ :=
  q*(((2*m).choose t*4^t)*BinaryHighTable.queryUnit L (2*m) (queryMagnitude m t A).size)+
    q*BackendScalarBits.backendScalarUnit (queryMagnitude m t A).size+(40*q+16)+1000*(L+m+1)^5+32*q+16

theorem row_work {L m q : ℕ} (t bandL bandR A : ℕ) (ht : t≤2*m) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q)
    (hA : BinaryHighTable.Bounds.TableBound A table) :
    (row t bandL bandR shape request table).operations≤rowBudget L m t q A := by
  have hq := BinaryHighTable.query_work t A (geometry shape request).embedding request.outside table
  have hs : (∑ r, (BinaryHighTable.query t (geometry shape request).embedding request.outside table r).operations)≤
      q*(((2*m).choose t*4^t)*BinaryHighTable.queryUnit L (2*m) (queryMagnitude m t A).size) := by
    calc
      _ ≤ ∑ _ : Fin q, ((2*m).choose t*4^t)*BinaryHighTable.queryUnit L (2*m) (queryMagnitude m t A).size :=
        Finset.sum_le_sum (fun r _ => hq r ht hA)
      _ = _ := by simp
  let payload := (row t bandL bandR shape request table).value.payload
  have hb : ∀ r, (view (payload.get r)).natAbs≤queryMagnitude m t A := by
    intro r
    simp only [payload,row,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn]
    exact BinaryHighTable.query_bound t A _ _ _ _ hA
  have hp := RootRequestSelection.selectRow_bits (accepts bandL bandR request) payload (queryMagnitude m t A) hb
  have hc := RootRequestSelection.selectRow_control (accepts bandL bandR request) payload
  simp only [row,Vector.get_ofFn,rowBudget]
  change _ ≤ _ at hs
  simp only [payload,row,Vector.get_ofFn] at hp hc
  omega

def tableMagnitude (L q A : ℕ) : ℕ := 5^(2*L+1)*(q*(BinaryCroppedHighBoxes.magnitude L A)^2)

theorem table_bound {L m t q : ℕ} [NeZero q] (cap A : ℕ)
    (X Y : BinarySourceFormation.RawStore L q) (hX : BinaryHighExecution.RawBound X A) (hY : BinaryHighExecution.RawBound Y A) :
    BinaryHighTable.Bounds.TableBound (tableMagnitude L q A) (BinaryCroppedHighBoxes.execute L m t q cap A X Y).boxes := by
  simp only [BinaryCroppedHighBoxes.execute,BinaryCroppedHighBoxes.setup_value]
  exact BinaryHighTable.prepare_bound _ (BinaryCroppedHighBoxes.magnitude_pos L A) _ _
    (BinaryCroppedHighBoxes.read_bound cap A true X hX) (BinaryCroppedHighBoxes.read_bound cap A false Y hY)

structure Prepared (L m q M : ℕ) where
  high : BinaryCroppedHighBoxes.Execution L q
  rows : Vector (ToomCook.Counted (Row L m q)) M

def execute {L m q M : ℕ} (t cap A bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (X Y : BinarySourceFormation.RawStore L q) :
    ToomCook.Counted (Prepared L m q M) :=
  let high := BinaryCroppedHighBoxes.execute L m t q cap A X Y
  let rows := GroupedPreparation.ofStoredFn requests (fun i => row t bandL bandR shape (requests.get i) high.boxes)
  ⟨⟨high,rows⟩,high.work+(∑ i, (rows.get i).operations)+32*M+8⟩

def get {L m q M : ℕ} (out : Prepared L m q M) (i : Fin M) : Vector Cell q := output (out.rows.get i).value

noncomputable def leaf {L q : ℕ} [NeZero q] (cap : ℕ) (X Y : BinarySourceFormation.RawStore L q)
    (residue : Fin q) (word : HighBoxDP.LeafWord (2*L)) : ℤ :=
  CyclicRing.convolution (BinaryCroppedHighEncoder.leafValues true cap X word).get
    (BinaryCroppedHighEncoder.leafValues false cap Y word).get residue

noncomputable def value {L m q : ℕ} [NeZero q] (t cap bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (X Y : BinarySourceFormation.RawStore L q) (residue : Fin q) : ℤ :=
  let d := geometry shape request
  if accepts bandL bandR request then
    CompleteThinProduct.storedHigh (t:=t) rfl d.embedding request.outside.get d.left_cap d.right_cap (leaf cap X Y residue)
  else 0

theorem execute_value {L m q M : ℕ} [NeZero q] (t cap A bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (X Y : BinarySourceFormation.RawStore L q)
    (hX : BinaryHighExecution.RawBound X A) (hY : BinaryHighExecution.RawBound Y A) (i : Fin M) (residue : Fin q) :
    view ((get (execute t cap A bandL bandR shape requests X Y).value i).get residue)=
      value t cap bandL bandR shape (requests.get i) X Y residue := by
  simp only [get,execute,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn,row_value,value]
  split
  · exact BinaryHighTable.query_boxes rfl _ _ _ _ _ _ _
      (fun w => BinaryCroppedHighBoxes.execute_correct cap A X Y hX hY w residue)
  · rfl

noncomputable def budget (L m t q M cap A : ℕ) : ℕ :=
  BinaryCroppedHighBoxes.totalBudget L m t q cap A+M*rowBudget L m t q (tableMagnitude L q A)+32*M+8

theorem execute_work {L m q M : ℕ} [NeZero q] (t cap A bandL bandR : ℕ) (ht : t≤2*m) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (X Y : BinarySourceFormation.RawStore L q)
    (hX : BinaryHighExecution.RawBound X A) (hY : BinaryHighExecution.RawBound Y A) :
    (execute t cap A bandL bandR shape requests X Y).operations≤budget L m t q M cap A := by
  have hp := BinaryCroppedHighBoxes.execute_price (m:=m) (t:=t) cap A X Y hX hY
  have hb := table_bound (m:=m) (t:=t) cap A X Y hX hY
  have hs : (∑ i : Fin M, (row t bandL bandR shape (requests.get i) (BinaryCroppedHighBoxes.execute L m t q cap A X Y).boxes).operations)≤
      M*rowBudget L m t q (tableMagnitude L q A) := by
    calc
      _ ≤ ∑ _ : Fin M, rowBudget L m t q (tableMagnitude L q A) := Finset.sum_le_sum (fun i _ => row_work t bandL bandR _ ht _ _ _ hb)
      _ = _ := by simp
  simp only [execute,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn,budget]
  omega

theorem execute_bound {L m q M : ℕ} [NeZero q] (t cap A bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (X Y : BinarySourceFormation.RawStore L q)
    (hX : BinaryHighExecution.RawBound X A) (hY : BinaryHighExecution.RawBound Y A) (i : Fin M) (residue : Fin q) :
    (view ((get (execute t cap A bandL bandR shape requests X Y).value i).get residue)).natAbs≤queryMagnitude m t (tableMagnitude L q A) := by
  simp only [execute,get,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn]
  exact row_bound t bandL bandR _ shape (requests.get i) _ (table_bound cap A X Y hX hY) residue

#print axioms row_value
#print axioms row_bound
#print axioms row_work
#print axioms table_bound
#print axioms execute_value
#print axioms execute_work
#print axioms execute_bound
end ThinMatrix.CroppedHighQueries
