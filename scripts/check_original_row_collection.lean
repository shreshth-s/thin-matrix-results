import OriginalRowCollection
open ThinMatrix BinaryCell BinaryGroupedCoordinates

private def ensure (ok : Bool) (message : String) : IO Unit :=
  if ok then pure () else throw (IO.userError message)

private def value (seed : Int) (i c : Nat) : Int :=
  let x := seed+(i/2:Int)*11+(c:Int)*7
  if (i+c)%3=0 then -x else x

private def check (M C G : Nat) (hG : 0<G) (seed : Int) : IO Nat := do
  let keys : Vector (Fin G) M := Vector.ofFn (fun i => ⟨(i.val*7+3)%G,Nat.mod_lt _ hG⟩)
  let child : Fin G → Run (OriginalRowCollection.Rows M C) := fun g =>
    let ids := FiniteRequestRouter.selected keys g
    ⟨⟨ids,Vector.ofFn (fun j => Vector.ofFn (fun c =>
      (BinaryMultiplierAdapter.encodeInteger (value seed ids[j.val].val c.val)).value))⟩,
      13*ids.length,19*ids.length+5⟩
  let out := OriginalRowCollection.execute child
  ensure (decide (out.bitSteps=13*M)) "Scatter bit sum mismatch"
  ensure (decide (out.control=5*G+19*M+48*G+80*M+16*C+36)) "Scatter control sum mismatch"
  for i in List.finRange M do
    for c in List.finRange C do
      ensure (decide (view ((out.value.get i).get c)=value seed i.val c.val)) "Original occurrence reconstruction mismatch"
  return M*C

def main : IO Unit := do
  let mut checked := 0
  for G in [1,2,5,17] do
    if hG : 0<G then
      for M in [0,1,3,9,23] do
        for C in [0,1,4,15] do
          for seed in ([-3,0,65537]:List Int) do
            checked := checked+(←check M C G hG seed)
  let empty : Fin 0 → Run (OriginalRowCollection.Rows 0 7) := fun i => Fin.elim0 i
  let emptyOut := OriginalRowCollection.execute empty
  ensure (decide (emptyOut.bitSteps=0 ∧ emptyOut.control=16*7+36)) "Empty shape cost mismatch"
  IO.println s!"PASS: {checked} original-ID coefficient outputs across reordered groups, duplicate values, empty buckets/axes, signed bit boundaries, and exact child/collection counters."
  IO.println "SCOPE: one shared side-output collection; complete APSP integration remains open."
