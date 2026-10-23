import BinaryCroppedHighBoxes
open ThinMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Independent literal coefficient tables and raw-word enumeration. -/
def referenceNormal (row col : Nat) : Int :=
  ([[1,0,0,1],[1,0,0,0],[0,1,0,-1],[0,1,0,0],[-1,-1,1,0]].getD row []).getD col 0

def referenceOpposite (row col : Nat) : Int :=
  ([[1,1,0],[1,-1,0],[1,1,-1],[1,-1,1],[2,0,0]].getD row []).getD col 0

def digit (base code position : Nat) : Nat := code/base^position%base

def sourceValue {L : Nat} (seed A : Nat) (normal : Fin L → WalshEmbedding.NormalLetter)
    (opposite : Fin L → WalshEmbedding.OppositeLetter) (r : Nat) : Int :=
  let h := (List.ofFn (fun i : Fin L => (i.val+1)*(SourceFormation.normalIndex (normal i)).val+
    (i.val+3)*(SourceFormation.oppositeIndex (opposite i)).val)).sum+seed+r
  if h%3=0 then (A : Int) else if h%3=1 then -(A : Int) else 0

def rawFixture (L q seed A : Nat) : BinarySourceFormation.RawStore L q :=
  (BinarySourceFormation.rawBuild fun normal opposite =>
    ⟨Vector.ofFn (fun r => (BinaryMultiplierAdapter.encodeInteger (sourceValue seed A normal opposite r.val)).value),0⟩).value

def directLeaf (L q cap seed A : Nat) (side : Bool) (key : ArrayKeys.Key (2*L)) : Vector Int q :=
  Vector.ofFn fun r => ((List.range (4^L)).map fun nc =>
    ((List.range (3^L)).map fun oc =>
      let normal := fun i : Fin L => SourceFormation.indexNormal ⟨digit 4 nc i.val,Nat.mod_lt _ (by decide)⟩
      let opposite := fun i : Fin L => SourceFormation.indexOpposite ⟨digit 3 oc i.val,Nat.mod_lt _ (by decide)⟩
      let weight := ((List.range L).filter fun i => digit 3 oc i==2).length
      if weight≤cap then sourceValue seed A normal opposite r.val *
        ((List.finRange (2*L)).map fun i =>
          let normalHere := if i.val<L then side else !side
          let j := i.val%L
          if normalHere then referenceNormal (key.get i).val (digit 4 nc j)
          else referenceOpposite (key.get i).val (digit 3 oc j)).prod
      else 0).sum).sum

def wordKeys (L alphabet : Nat) (h : alphabet≤6) (hp : 0<alphabet) : List (ArrayKeys.Key (2*L)) :=
  (List.range (alphabet^(2*L))).map fun code => Vector.ofFn fun i =>
    ⟨digit alphabet code i.val,(Nat.mod_lt _ hp).trans_le h⟩

def baseCountCheck (L m t : Nat) : Nat :=
  ((List.range (m+1)).map fun j => ((List.range (m+1)).map fun k =>
    if j+k≤2*m-t then L.choose j*L.choose k*4^(2*L-j-k) else 0).sum).sum

def encoderBudgetCheck (L m t q cap A : Nat) : Nat :=
  10*(cap.size+1)^2+2+(BinaryCroppedHighInput.payloadBudget L q cap A+4*L+
    BinaryHighCost.storedFactor L A*BinaryCroppedHighEncoder.encoderShape L*q)*baseCountCheck L m t

def checkEncoder (L m t q cap seed A : Nat) (side : Bool) : Bool := Id.run do
  let raw := rawFixture L q seed A
  let out := BinaryCroppedHighEncoder.execute L m t q cap side raw
  let keys := out.encoding.leaves.map Prod.fst
  let expected := (wordKeys L 5 (by decide) (by decide)).filter fun k => (ArrayKeys.baseTest L m t k).1
  let correct := expected.all fun key =>
    let stored := (BinaryHighExecution.readBase out key).value
    let ref := directLeaf L q cap seed A side key
    (List.finRange q).all fun r => BinaryCell.view (stored.get r)==ref.get r
  let cells := (out.encoding.formed.map fun s => q*SharedEncoder.volume s.remaining s.dims).sum
  return correct && keys.length==baseCountCheck L m t && keys.length==expected.length &&
    keys.all (fun k => expected.contains k) && decide keys.Nodup &&
    decide (cells≤q*(2*L+1)*baseCountCheck L m t) &&
    decide (out.bitSteps≤encoderBudgetCheck L m t q cap A)

def compatibleKey {n : Nat} (box leaf : ArrayKeys.Key n) : Bool :=
  (List.finRange n).all fun i => (box.get i).val==5 || box.get i==leaf.get i

/-- Bounded runtime reference for the cyclic base operation. The production
FFT composition is kernel-checked; its unreduced root evaluation is deliberately
not executed in this fixture. The actual binary HIGH recurrence is executed. -/
def elementaryProduct {q : Nat} (a b : Vector BinaryCell.Cell q) :
    Vector BinaryCell.Cell q × Nat :=
  let rows := Vector.ofFn fun r : Fin q =>
    (List.finRange q).foldl (fun acc j =>
      let p := BinaryCell.mul (a.get j) (b.get (r-j))
      let n := BinaryCell.add acc.value p.value
      (⟨n.value,acc.bitSteps+p.bitSteps+n.bitSteps+4⟩ : BinaryCell.Result BinaryCell.Cell))
      ⟨BinaryCell.zero,1⟩
  (rows.map (fun r => r.value),(rows.toList.map (fun r => r.bitSteps)).sum+2*q)

def checkBoxes (L m t cap A : Nat) : Bool := Id.run do
  let q := 3
  let left := BinaryCroppedHighEncoder.execute L m t q cap true (rawFixture L q 0 A)
  let right := BinaryCroppedHighEncoder.execute L m t q cap false (rawFixture L q 1 A)
  let base := BinaryHighTable.guardedBase (L:=L) (m:=m) (t:=t) fun w =>
    let key := ArrayKeys.materialize w.val
    let a := BinaryHighExecution.readBase left key
    let b := BinaryHighExecution.readBase right key
    let p := elementaryProduct a.value b.value
    (p.1,a.bitSteps+b.bitSteps+p.2)
  let out := BinaryHighTable.execute (L:=L) (m:=m) (t:=t) base (2*L+1)
  let leaves := (wordKeys L 5 (by decide) (by decide)).map fun key =>
    let a := directLeaf L q cap 0 A true key
    let b := directLeaf L q cap 1 A false key
    let product := Vector.ofFn fun r : Fin q =>
      ((List.finRange q).map fun j => a.get j*b.get ⟨(r.val+q-j.val)%q,Nat.mod_lt _ (by decide)⟩).sum
    (key,product)
  let boxes := (wordKeys L 6 (by decide) (by decide)).filter fun key => (ArrayKeys.highTest L m t key).1
  let correct := boxes.all fun key =>
    let actual := BinaryHighTable.lookup out.value key
    (List.finRange q).all fun r =>
      let ref := ((leaves.filter fun pair => compatibleKey key pair.1).map fun pair => pair.2.get r).sum
      BinaryCell.view (actual.get r)==ref
  let mag := 8^(2*L)*A+1
  return correct && decide (left.bitSteps≤encoderBudgetCheck L m t q cap A) &&
    decide (right.bitSteps≤encoderBudgetCheck L m t q cap A) &&
    decide (out.work≤out.sites*BinaryHighTable.arithmeticUnit (5^(2*L+1)*(q*mag^2)).size+out.baseWork)

def croppedHighChecks : Bool :=
  ((List.range 3).all fun L => (List.range (L+1)).all fun m =>
    (List.range (2*m+2)).all fun t => (List.range (L+2)).all fun cap =>
      [false,true].all fun side => checkEncoder L m t 3 cap 1 2 side) &&
  ((List.range 2).all fun L => (List.range (L+1)).all fun m =>
    (List.range (2*m+2)).all fun t => (List.range (L+2)).all fun cap => checkBoxes L m t cap 2) &&
  ([0,1,2,3,7,8,255,256,65535,65536].all fun A =>
    let s := BinaryCroppedHighBoxes.setup 2 A
    s.value==8^4*A+1 && decide (s.bitSteps≤BinaryCroppedHighBoxes.setupBudget 2 A)) &&
  checkEncoder 2 1 1 0 0 1 0 true && checkBoxes 1 1 1 0 0

#eval do
  if croppedHighChecks then
    IO.println "PASS: cropped shifted HIGH encoders through L=2, both orientations, every joint cap, all cyclic slots, retained cells and work; binary box recurrence with elementary full cyclic bases through L=1 against independent raw tensor and cyclic sums; production FFT composition is kernel-checked only; zero-length/zero-input boundaries and binary setup bit boundaries."
  else throw (IO.userError "Cropped HIGH fixture failed")
