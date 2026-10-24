import GraphHighScalarSchedule
open ThinMatrix
set_option maxHeartbeats 2000000

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
  let out := GraphHighScalarSchedule.execute 0 shape rs hb (tables q)
  let u : Fin (ExactHalfSourcePlan.J 0) := ⟨0,ExactHalfCroppedEmbedding.shifts_nonempty 0⟩
  let mut seen := Array.replicate M 0
  for g in List.finRange 9 do
    let rows := (((out.value.get g).get u).get u).get ⟨0,by decide⟩
    for j in List.finRange rows.indices.length do
      let original := rows.indices[j.val]
      let req := rs.get original
      unless (rows.values.get j).view=value req.bandL req.bandR req.coefficient.val do
        throw (IO.userError "HIGH scalar schedule selected value differs")
      seen := seen.modify original.val (·+1)
  unless seen.all (·=1) do throw (IO.userError "HIGH scalar schedule lost original IDs")
  unless out.operations≤GraphHighScalarSchedule.budget 3 0 0 0 M (q+30) do
    throw (IO.userError "HIGH scalar schedule exceeded complete loop budget")
  return M

def main : IO Unit := do
  let mut total := 0
  for q in [1,3,8] do
    if hq : 0<q then
      for M in [0,1,19,53] do total := total+(←check q M hq)
  IO.println s!"PASS {total} HIGH scalar schedule occurrences across retained pair tables"
  IO.println "PASS original IDs, duplicates, empty input, distinct signed tables for every band pair, q=1,3,8, and full route/pair/query loop budget"
