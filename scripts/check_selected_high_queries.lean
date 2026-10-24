import SelectedHighQueries

set_option maxHeartbeats 1600000

open ThinMatrix

def request (q : Nat) (hq : 0<q) (i : Fin 19) : GraphCompletionRequests.Physical 0 0 q :=
  ⟨i.val%3,(i.val/3)%3,⟨0,ThinMatrixBackend.tileWidth_pos 0 0 (by omega)⟩,⟨0,ThinMatrixBackend.tileWidth_pos 0 0 (by omega)⟩,⟨i.val%q,Nat.mod_lt _ hq⟩,Vector.replicate 0 0⟩

def selectedRows {q M : Nat} (shape : ThinMatrixBackend.ShapePlan 0 0)
    (requests : Vector (GraphCompletionRequests.Physical 0 0 q) M)
    (ids : List (Fin M)) (table : BinaryHighTable.Table q) : Vector BinaryCell.Cell ids.length :=
  (SelectedHighQueries.query 0 shape requests ids table).value.values

def checkRows {q M : Nat} (shape : ThinMatrixBackend.ShapePlan 0 0)
    (requests : Vector (GraphCompletionRequests.Physical 0 0 q) M)
    (a b : Nat) (ids : List (Fin M)) (table : BinaryHighTable.Table q) : IO Nat := do
  let values := selectedRows shape requests ids table
  for i in List.finRange ids.length do
    let r := requests.get (ids.get i)
    let expected := (r.coefficient.val: Int)-4
    let actual := (values.get i).view
    let old := (CroppedHighQueries.output (CroppedHighQueries.row 0 a b shape r table).value).get r.coefficient
    if actual != expected || actual != old.view then throw (IO.userError "selected HIGH mismatch")
    if r.bandL != a || r.bandR != b then throw (IO.userError "own-band routing mismatch")
  return ids.length

def requests (q : Nat) (hq : 0<q) : Vector (GraphCompletionRequests.Physical 0 0 q) 19 :=
  Vector.ofFn (request q hq)

theorem request_bands (q : Nat) (hq : 0<q) (i : Fin 19) :
    ((requests q hq).get i).bandL<3 ∧ ((requests q hq).get i).bandR<3 := by
  simp only [requests,Vector.get_ofFn,request]
  exact ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩

def runCase (q : Nat) (hq : 0<q) : IO Nat := do
  let shape : ThinMatrixBackend.ShapePlan 0 0 := BinaryBackendExecution.prepareShapeRuntime 0 0
  let rs := requests q hq
  let table : BinaryHighTable.Table q := .node (some (Vector.ofFn (fun r : Fin q => (BinaryArrayFFT.loadInteger ((r.val: Int)-4)).value))) #[]
  let routing := SelectedHighQueries.route rs (request_bands q hq)
  let mut seen := 0
  for a in List.finRange 3 do
    for b in List.finRange 3 do
      let ids := (SelectedHighQueries.ids routing.value a b).value
      seen := seen + (← checkRows shape rs a.val b.val ids table)
  if seen != 19 then throw (IO.userError "routing dropped or duplicated occurrences")
  let empty := SelectedHighQueries.query 0 shape rs [] table
  if empty.value.values.size != 0 then throw (IO.userError "empty query is nonempty")
  let duplicates := [⟨0,by decide⟩,⟨0,by decide⟩,⟨9,by decide⟩,⟨18,by decide⟩]
  let extra ← checkRows shape rs 0 0 duplicates table
  return seen+extra

def payload (a b r : Nat) : Int := 17*(a: Int)-11*(b: Int)+3*(r: Int)-5

def richTable (q : Nat) : BinaryHighTable.Table q := Id.run do
  let mut out : BinaryHighTable.Table q := .empty
  for a in List.finRange 6 do
    for b in List.finRange 6 do
      out := out.write [a,b] (Vector.ofFn (fun r : Fin q => (BinaryArrayFFT.loadInteger (payload a.val b.val r.val)).value))
  return out

def richRequest (q : Nat) (hq : 0<q) (i : Fin 19) : GraphCompletionRequests.Physical 1 1 q :=
  ⟨i.val%3,(i.val/3)%3,⟨0,ThinMatrixBackend.tileWidth_pos 1 1 (by omega)⟩,⟨0,ThinMatrixBackend.tileWidth_pos 1 1 (by omega)⟩,
    ⟨i.val%q,Nat.mod_lt _ hq⟩,Vector.ofFn (fun j => ⟨(i.val+j.val)%4,Nat.mod_lt _ (by decide)⟩)⟩

def richCase (q : Nat) (hq : 0<q) : IO Nat := do
  let shape : ThinMatrixBackend.ShapePlan 1 1 := BinaryBackendExecution.prepareShapeRuntime 1 1
  let table := richTable q
  let mut checks := 0
  for t in [0,1,2] do
    for i in List.finRange 19 do
      let r := richRequest q hq i
      let selected := SelectedHighQueries.lookup t shape r table
      let old := (CroppedHighQueries.output (CroppedHighQueries.row t r.bandL r.bandR shape r table).value).get r.coefficient
      let embedding := (CroppedHighQueries.geometry shape r).embedding
      let keys := HighQueryKeys.generatedKeys t 2 2 embedding r.outside
      let expected := (keys.map (fun key => payload (key.get ⟨0,by decide⟩).val (key.get ⟨1,by decide⟩).val r.coefficient.val)).sum
      if selected.value.view != expected || selected.value.view != old.view then
        throw (IO.userError "nontrivial selected HIGH mismatch")
      if selected.operations > SelectedHighQueries.rowBudget 1 1 t 80 then
        throw (IO.userError "nontrivial selected HIGH cost mismatch")
      checks := checks+1
  return checks

def main : IO Unit := do
  let mut checks := 0
  let mut richChecks := 0
  for q in [1,3,8] do
    if hq : 0<q then
      checks := checks + (← runCase q hq)
      richChecks := richChecks + (← richCase q hq)
  IO.println s!"PASS {checks} selected HIGH coefficient reads against explicit values and full-vector queries"
  IO.println "PASS own-band routing, duplicates, and empty queries for q=1,3,8"
  IO.println s!"PASS {richChecks} nontrivial HIGH key sums and cost bounds, L=m=1, t=0,1,2, q=1,3,8"
