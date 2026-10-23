import HalfSourceBinarySelection
open ThinMatrix ThinMatrix.HalfSourceIntegerScores ThinMatrix.WalshEmbedding
open ThinMatrix.HalfSourceList
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def binaryChecks : Bool × Nat × Nat := Id.run do
  let m := 1
  let ts := HalfSourceBinaryScores.tables m
  let powersOK := (List.range (2*K m+1)).all fun k =>
    let t : Int := (k:Int)-(K m:Int)
    BinaryCell.view (HalfSourceBinaryScores.numerator m ts.value t).value == powerNumerator m t
  let termsOK := (List.range (2*(64*m^3)+1)).all fun k =>
    let s : Int := (k:Int)-(64*m^3:Int)
    (BinaryCell.view (HalfSourceBinaryScores.unresolved m ts.value s).value == unresolved m s) &&
    ([false,true].all fun b =>
      BinaryCell.view (HalfSourceBinaryScores.resolved m ts.value s b).value == resolved m s b)
  let choiceOK := (List.range 5).all fun k =>
    let sums : Characters 1 → Int := fun _ => (k:Int)-2
    let r := HalfSourceBinarySelection.chosen m ts.value sums (fun a => a.val) (fun _ => false)
    r.value == HalfSourceIntegerScores.chosen m sums (fun a => a.val) (fun _ => false)
  let b := HalfSourceBinarySelection.build m ts.value 4
  let expected := HalfSourceIntegerGreedy.build m (HalfSourceIntegerGreedy.tables m) 4
  let listOK := decide (b.value.entries = expected.entries)
  let countsOK := decide (ts.bitSteps ≤ 2*(HalfSourceBinaryScores.width m+2)+
    2*((2*K m+1)*(2*K m*HalfSourceBinaryScores.unit m+1))) &&
    decide (b.bitSteps ≤ 4*(m*HalfSourceBinarySelection.choiceBound m+1)+1)
  return (powersOK && termsOK && choiceOK && listOK && countsOK,ts.bitSteps,b.bitSteps)
#eval binaryChecks
#eval (HalfSourceBinarySelection.translations 0).value.length
#print axioms HalfSourceBinarySelection.translations_value
#print axioms HalfSourceBinarySelection.translations_arithmetic_price
