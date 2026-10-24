import GraphHighScalarResult
import SelectedScalarRows
open ThinMatrix
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private def requests (q M : Nat) (hq : 0<q) : Vector (GraphCompletionRequests.Physical 0 0 q) M :=
  Vector.ofFn fun i => let j:=i.val%9
    ⟨j%3,(j/3)%3,⟨0,ThinMatrixBackend.tileWidth_pos 0 0 (by omega)⟩,
      ⟨0,ThinMatrixBackend.tileWidth_pos 0 0 (by omega)⟩,⟨j%q,Nat.mod_lt _ hq⟩,Vector.replicate 0 0⟩

private def value (a b c : Nat) : Int := 10*(a:Int)-7*(b:Int)+(c:Int)-4

private def tables (q : Nat) : GraphHighPreparation.Tables 0 0 q 3 :=
  Vector.ofFn fun a => Vector.ofFn fun b => Vector.ofFn fun _ => Vector.ofFn fun _ => Vector.ofFn fun _ =>
    .node (some (Vector.ofFn fun c : Fin q => (BinaryMultiplierAdapter.encodeInteger (value a.val b.val c.val)).value)) #[]

private def check (q M : Nat) (hq : 0<q) : IO Nat := do
  let shape := BinaryBackendExecution.prepareShapeRuntime 0 0
  let rs := requests q M hq
  have hb (i : Fin M) : (rs.get i).bandL<3 ∧ (rs.get i).bandR<3 := by
    simp only [rs,requests,Vector.get_ofFn]
    exact ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩
  let out := GraphHighScalarResult.execute 0 shape rs hb (tables q)
  for i in List.finRange M do
    let req := rs.get i
    unless ((out.value.get i).get ⟨0,by decide⟩).view=value req.bandL req.bandR req.coefficient.val do
      throw (IO.userError "HIGH collected scalar differs or original occurrence was lost")
  unless out.operations≤GraphHighScalarResult.budget 3 0 0 0 M (q+30) do
    throw (IO.userError "HIGH scalar schedule exceeded complete loop budget")
  return M

private def richTable (q : Nat) : BinaryHighTable.Table q := Id.run do
  let mut out : BinaryHighTable.Table q := .empty
  for a in List.finRange 6 do
    for b in List.finRange 6 do
      out := out.write [a,b] (Vector.ofFn (fun c : Fin q =>
        (BinaryArrayFFT.loadInteger (value a.val b.val c.val)).value))
  return out

private def rich : IO Nat := do
  let shape := BinaryBackendExecution.prepareShapeRuntime 1 1
  let rs : Vector (GraphCompletionRequests.Physical 1 1 3) 3 := Vector.ofFn fun i =>
    ⟨0,0,⟨0,ThinMatrixBackend.tileWidth_pos 1 1 (by omega)⟩,
      ⟨0,ThinMatrixBackend.tileWidth_pos 1 1 (by omega)⟩,⟨i.val%2,by omega⟩,
      Vector.ofFn (fun j => ⟨(i.val%2+j.val)%4,Nat.mod_lt _ (by decide)⟩)⟩
  have hb (i : Fin 3) : (rs.get i).bandL<1 ∧ (rs.get i).bandR<1 := by simp only[rs,Vector.get_ofFn];decide
  let tab := richTable 3
  let tables : GraphHighPreparation.Tables 1 1 3 1 :=
    Vector.ofFn fun _ => Vector.ofFn fun _ => Vector.ofFn fun _ => Vector.ofFn fun _ => Vector.ofFn fun _ => tab
  let out := GraphHighScalarResult.execute 1 shape rs hb tables
  for i in List.finRange 3 do
    let req := rs.get i
    let keys := HighQueryKeys.generatedKeys 1 2 2 (CroppedHighQueries.geometry shape req).embedding req.outside
    let one := (keys.map (fun key => value (key.get ⟨0,by decide⟩).val (key.get ⟨1,by decide⟩).val req.coefficient.val)).sum
    let expected := (GraphHighScalarCollection.H 1:Int)*one
    unless ((out.value.get i).get ⟨0,by decide⟩).view=expected do
      throw (IO.userError "HIGH J²/run scalar sum differs from explicit key oracle")
  unless out.operations≤GraphHighScalarResult.budget 1 1 1 1 3 100 do
    throw (IO.userError "HIGH complete result exceeded loop+sum+scatter budget")
  return 3

def main : IO Unit := do
  let mut total := 0
  for q in [1,3,8] do
    if hq : 0<q then
      for M in [0,1,19,53] do total := total+(←check q M hq)
  let richCount ← rich
  IO.println s!"PASS {total} HIGH scalar schedule occurrences across retained pair tables"
  IO.println s!"PASS {richCount} nontrivial original-ID scalar totals over every J² degree-run child, L=m=t=1, q=3"
  IO.println "PASS original IDs, duplicates, empty input, distinct signed tables for every band pair, q=1,3,8, and full route/pair/query loop budget"
