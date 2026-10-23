import ExactHalfSourcePlan

open ThinMatrix ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceList
open ThinMatrix.HalfSourceBinaryState
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def require (b : Bool) (message : String) : IO Unit :=
  if b then do
    IO.println ("PASS: "++message)
    (← IO.getStdout).flush
  else throw (IO.userError ("FAIL: "++message))

def encode (z : Int) : BinaryCell.Cell := (BinaryMultiplierAdapter.encodeInteger z).value

def referenceBits (m code : Nat) : Vector Bool m :=
  Vector.ofFn fun i => code.testBit i.val

def checkKeys (m : Nat) : Bool :=
  let out := HalfSourceStoredKeys.produce m
  out.value.toList.length==2^m && out.bitSteps==0 &&
    out.control≤2^m*(4*m*m+20*m+50)+4*m+17 &&
    (List.finRange (2^m)).all fun i =>
      let row := out.value.get i
      row.row==referenceBits m i.val && row.active==(i.val != 0)

/-- Native integer arithmetic here is an independent fixture reference. -/
def checkUpdate (m : Nat) : Bool := Id.run do
  let keys := HalfSourceStoredKeys.produce m
  for i in List.finRange (2^m) do
    for code in List.range (2^m) do
      let d := referenceBits m code
      let parity := ((List.finRange m).map fun b => if (keys.value.get i).row.get b && d.get b then 1 else 0).sum%2
      for k in List.range 9 do
        let z : Int := (k:Int)-4
        let out := update (keys.value.get i) d (encode z,z)
        let want := if i.val==0 then 0 else z+(if parity==1 then -1 else 1)
        if BinaryCell.view out.value.1!=want || out.value.2!=want ||
          out.bitSteps>updateBudget 4 || out.control>6*m+13 then return false
  return true

/-- Independent exact powers are fixture inputs, avoiding a repeated expensive
production-table evaluation. This tests the actual selector and state loop. -/
def fixtureTables (m : Nat) : HalfSourceBinaryScores.Tables :=
  (Array.ofFn fun i : Fin (2*HalfSourceIntegerScores.K m+1) => encode ((HalfSourceIntegerScores.A m)^i.val:Int),
   Array.ofFn fun i : Fin (2*HalfSourceIntegerScores.K m+1) => encode ((HalfSourceIntegerScores.B m)^i.val:Int))

def checkBuild : Bool := Id.run do
  let m := 1
  let keys := HalfSourceStoredKeys.produce m
  let ts := fixtureTables m
  let native := HalfSourceIntegerGreedy.tables m
  for j in List.range 9 do
    let out := HalfSourceRetainedTranslations.build m ts keys.value j
    let old := HalfSourceBinarySelection.build m ts j
    let reference := HalfSourceIntegerGreedy.build m native j
    if !decide (out.value.entries=reference.entries) || out.bitSteps<old.bitSteps ||
        out.bitSteps>j*(m*HalfSourceBinarySelection.choiceBound m+1+2^m*updateBudget (64*m^3))+1 ||
        out.control>8*2^m+8+j*(2^m*(6*m+45)+20) then return false
    for i in List.finRange (2^m) do
      let expected := if i.val==0 then 0 else
        ((out.value.entries.map fun d => if d 0 then (-1:Int) else 1).sum)
      let cell := out.value.memory.get i
      if BinaryCell.view cell.1!=expected || cell.2!=expected || expected.natAbs>j then return false
  return true

def checkPrepare (L : Nat) : Bool :=
  let shape := BinaryBackendExecution.prepareShapeRuntime L 0
  let out := ExactHalfSourcePlan.prepare shape
  let generated := HalfSourceRetainedTranslations.produce 0
  let inv := ExactHalfWeightTable.candidates shape.environment.gammaColumns
  out.value.shifts.toArray.size==1 && out.value.construction.state.entries.isEmpty &&
    out.value.construction.keys.toArray.size==1 && out.value.construction.powers.1.size==3 &&
    out.bitSteps==generated.bitSteps+inv.bitSteps && generated.bitSteps>0 &&
    out.bitSteps≤HalfSourceRetainedTranslations.arithmeticBudget 0+2^L*ExactHalfWeightTable.candidateBitBudget L &&
    out.control≤ExactHalfSourcePlan.retainedControlBudget L 0 &&
    (List.finRange (2^L)).all fun i =>
      (ExactHalfSourcePlan.readPick out.value.picks (Finset.univ.filter fun b => (referenceBits L i.val).get b) (zeroBits 0)).val==0

def main : IO Unit := do
  require ((List.range 7).all checkKeys) "materialized character keys and active flags versus independent testBit enumeration, m=0..6"
  require ((List.range 4).all checkUpdate) "actual signed binary state updates, decoded caches and charges against integer parity, m=0..3, sums=-4..4"
  require checkBuild "actual binary selector/state loop for eight steps, reference exact integer greedy choices, retained arithmetic and magnitude/control bounds"
  require ((List.range 4).all checkPrepare) "actual zero-dimensional source preparation retains generator payload and arithmetic, first valid picks and setup bounds, L=0..3"
  IO.println "PASS: bounded shared-selector cost suite finished; no full graph or production FFT evaluation."
