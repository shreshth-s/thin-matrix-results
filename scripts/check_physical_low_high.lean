import ShiftedPhysicalHigh
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


def require (b : Bool) (label : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++label))
  IO.println ("PASS: "++label)
  (← IO.getStdout).flush

def checkPhysical (L m : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let masks := (ResidualFamilyKeys.masks shape.layout).value
  return (List.finRange masks.size).all fun a => (List.finRange masks.size).all fun b =>
    let left := masks.get a; let right := masks.get b
    (List.range (4^L)).all fun nc => (List.range (3^L)).all fun oc =>
      let w : PhysicalWordReindex.Words L :=
        (fun i => SourceFormation.indexNormal ⟨digit 4 nc i.val,Nat.mod_lt _ (by decide)⟩,
         fun i => SourceFormation.indexOpposite ⟨digit 3 oc i.val,Nat.mod_lt _ (by decide)⟩)
      let permitted := (List.finRange L).all fun i => left.bits.get i || digit 4 nc i.val != 2
      let back := PhysicalWordReindex.pack left right (PhysicalWordReindex.unpack left right w)
      let equal := (List.finRange L).all fun i => back.1 i==w.1 i && back.2 i==w.2 i
      let normalOutside := (List.finRange L).filter fun i => !left.bits.get i
      let oppositeOutside := (List.finRange L).filter fun i => !right.bits.get i
      permitted==equal && ([false,true].all fun orientation => (List.range (4^(2*L))).all fun code =>
        let labels : Vector (Fin 4) (2*L) := Vector.ofFn fun i => ⟨digit 4 code i.val,Nat.mod_lt _ (by decide)⟩
        let ref := (normalOutside.map fun i => referenceNormal (digit 4 code (if orientation then L+i.val else i.val)) (digit 4 nc i.val)).prod *
          (oppositeOutside.map fun i => referenceOpposite (digit 4 code (if orientation then i.val else L+i.val)) (digit 3 oc i.val)).prod
        PhysicalOrdinaryForms.ordinary left right orientation labels w==ref)

/-- Actual binary key/query/selection execution on independently checked
encoder bases and the actual HIGH recurrence. Production FFT is not evaluated. -/
def checkRows (L m t cap A : Nat) (hm : m≤L) : Bool := Id.run do
  let q := 3
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let B := ThinMatrixBackend.tileWidth L m
  let hp := ThinMatrixBackend.tileWidth_pos L m hm
  let left := BinaryCroppedHighEncoder.execute L m t q cap true (rawFixture L q 0 A)
  let right := BinaryCroppedHighEncoder.execute L m t q cap false (rawFixture L q 1 A)
  let base := BinaryHighTable.guardedBase (L:=L) (m:=m) (t:=t) fun w =>
    let key := ArrayKeys.materialize w.val
    let a := BinaryHighExecution.readBase left key
    let b := BinaryHighExecution.readBase right key
    let p := elementaryProduct a.value b.value
    (p.1,a.bitSteps+b.bitSteps+p.2)
  let table := (BinaryHighTable.execute (L:=L) (m:=m) (t:=t) base (2*L+1)).value
  let leaves := (wordKeys L 5 (by decide) (by decide)).map fun key =>
    let a := directLeaf L q cap 0 A true key
    let b := directLeaf L q cap 1 A false key
    (key,Vector.ofFn fun r : Fin q => ((List.finRange q).map fun j =>
      a.get j*b.get ⟨(r.val+q-j.val)%q,Nat.mod_lt _ (by decide)⟩).sum)
  let requests : Vector (TilingCosts.Request (2*B) q) 4 := Vector.ofFn fun j =>
    ⟨⟨if j.val==3 then B else if j.val==1 then B-1 else 0,by dsimp [B] at *; split <;> (try split) <;> omega⟩,
     ⟨if j.val==3 then B else if j.val==1 then 0 else B-1,by dsimp [B] at *; split <;> (try split) <;> omega⟩,0⟩
  let physical := requests.map fun request => (GraphCompletionRequests.locate shape hm request).value
  let run := CountedCyclicCollection.execute physical
    (fun i => CroppedHighQueries.row t 0 0 shape (physical.get i) table)
    (fun row (_ : Fin 1) => CroppedHighQueries.output row)
  let outputs := physical.map fun request => CroppedHighQueries.row t 0 0 shape request table
  let mag := CroppedHighQueries.tableMagnitude L q A
  let correct := (List.finRange 4).all fun j =>
    let request := physical.get j
    let nmask := (RowIndexing.rowUnrank shape.layout request.row).1.val
    let omask := (RowIndexing.rowUnrank shape.layout request.column).1.val
    let support := (List.finRange (2*L)).filter fun i =>
      if hi : i.val<L then decide ((⟨i.val,hi⟩ : Fin L)∈nmask)
      else decide ((⟨i.val-L,by omega⟩ : Fin L)∈omask)
    let filtered := leaves.filter fun pair =>
      let outsideOK := (List.finRange (2*L)).all fun i => support.contains i || (pair.1.get i).val==(request.outside.get i).val
      let ordinary := (support.filter fun i => (pair.1.get i).val<4).length
      outsideOK && ordinary≥t
    (List.finRange q).all (fun r =>
      let ref := if request.bandL==0 && request.bandR==0 then (filtered.map fun pair => pair.2.get r).sum else 0
      BinaryCell.view ((CroppedHighQueries.output (outputs.get j).value).get r)==ref) &&
      decide ((outputs.get j).operations≤CroppedHighQueries.rowBudget L m t q mag)
  let sumCorrect := (List.finRange q).all fun r =>
    BinaryCell.view ((CountedCyclicCollection.output run.value 0).get r)==
      ((List.finRange 4).map fun j => BinaryCell.view ((CroppedHighQueries.output (outputs.get j).value).get r)).sum
  return correct && sumCorrect &&
    decide (run.operations≤CountedCyclicCollection.budget (fun _ : Fin 4 => CroppedHighQueries.rowBudget L m t q mag) 1 q (CroppedHighQueries.queryMagnitude m t mag))

def checkCollections (S M q : Nat) : Bool := Id.run do
  let shape := Vector.replicate S ()
  let children : Fin S → ToomCook.Counted (Vector (Vector BinaryCell.Cell q) M) := fun s =>
    ⟨Vector.ofFn (fun j => Vector.ofFn fun r => (BinaryMultiplierAdapter.encodeInteger
      (if s.val%2==0 then ((s.val+1)*(j.val%2+1)*(r.val+1):Int) else -((s.val+1)*(j.val%2+1)*(r.val+1):Int))).value),s.val+7⟩
  let out := CountedCyclicCollection.execute shape children (fun a i => a.get i)
  let A := (S+1)*2*(q+1)
  return ((List.finRange M).all fun i => (List.finRange q).all fun r =>
    BinaryCell.view ((CountedCyclicCollection.output out.value i).get r)==
      ((List.range S).map fun s => if s%2==0 then ((s+1)*(i.val%2+1)*(r.val+1):Int) else -((s+1)*(i.val%2+1)*(r.val+1):Int)).sum) &&
    decide (out.operations≤CountedCyclicCollection.budget (fun s : Fin S => s.val+7) M q A)

#eval do
  require (checkPhysical 0 0 && checkPhysical 1 0 && checkPhysical 1 1) "physical word inverse and ordinary forms, zero and one-dimensional masks, every physical word/label/orientation"
  require (checkPhysical 2 1) "physical word inverse and outside p1 annihilation, all actual L=2,m=1 mask pairs and physical words/labels"
  require ((List.range 3).all fun cap => checkRows 0 0 0 cap 2 (by decide)) "zero-dimensional executed HIGH queries, duplicate/rejected requests, cyclic sums and finite work"
  require ((List.range 2).all fun cap => checkRows 1 0 0 cap 2 (by decide)) "all-outside executed HIGH queries against independent physical leaf threshold sum"
  require ((List.range 3).all fun t => (List.range 2).all fun cap => checkRows 1 1 t cap 2 (by decide)) "all thresholds/crops for L=m=1, actual binary HIGH recurrence, key scans and all cyclic coefficients"
  require (checkRows 1 1 1 0 0 (by decide)) "zero raw coefficients preserve executable request/selection work"
  require ((List.range 5).all fun S => [0,1,3,4].all fun M => [0,1,3].all fun q => checkCollections S M q) "counted retained collection: empty dimensions, signed sums and duplicate request values"
  IO.println "PASS: bounded physical LOW/HIGH suite finished; no full graph or production FFT evaluation."
