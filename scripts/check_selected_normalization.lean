import GraphSelectedIncidences
open ThinMatrix BinaryCell

private def ensure (ok : Bool) (message : String) : IO Unit :=
  if ok then pure () else throw (IO.userError message)

private def check (n h L : Nat) : IO Nat := do
  let M := FoldedBackendExecution.windowQuerySize n
  let B := CompactBlocks.blockCount n h
  let low : Vector (Vector Cell B) M := Vector.ofFn (fun j => Vector.ofFn (fun b =>
    (BinaryMultiplierAdapter.encodeInteger (1-(j.val:Int)*11+(b.val:Int)*3)).value))
  let high : Vector (Vector Cell B) M := Vector.ofFn (fun j => Vector.ofFn (fun b =>
    (BinaryMultiplierAdapter.encodeInteger
      ((4:Int)^L*((j.val:Int)*17+(b.val:Int))-view ((low.get j).get b))).value))
  let normalized := BinaryLowHighNormalize.table L low high
  let out := GraphSelectedIncidences.execute normalized.2.value
  let I := EndToEndAPSP.incidenceSize n h
  ensure (decide (out.control≤I*(64*I.size^2+40)+8)) "Output-address control bound failed"
  for i in List.finRange I do
    let x := (EndToEndAPSP.incidenceEquiv n h).symm i
    let j := FoldedBackendExecution.windowQueryEquiv n (x.1,x.2.2)
    ensure (decide (view (out.value.get i)=(j.val:Int)*17+(x.2.1.val:Int)))
      "Selected normalization or incidence-order mismatch"
  return I

def main : IO Unit := do
  let mut checked := 0
  for n in [0,1,2,3,4,7] do
    for h in [1,2,3,5] do
      for L in [0,1,3,7] do
        checked := checked+(←check n h L)
  IO.println s!"PASS: {checked} selected normalized incidence outputs across empty/singleton grids, partial middle blocks, signed LOW/HIGH cancellation, nondivisible component numerators, and charged output addressing."
  IO.println "SCOPE: complete-numerator normalization and controller incidence ordering; full APSP endpoint remains open."
