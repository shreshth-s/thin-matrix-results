import BinaryPreparedGroupedProgram
open ThinMatrix ThinMatrix.CappedBitPreparation ThinMatrix.CroppedGroupedSuffix
open ThinMatrix.GroupedPreparation (keyVector)
open ThinMatrix.BinaryGroupedPreparation ThinMatrix.BinaryPreparedGroupedProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def directBinaryGrouped {n C : Nat} (r : Nat) (X : Source n C)
    (c : Fin C) (p a : Key n) : Int :=
  (List.ofFn (fun i : Fin (3^n) =>
    let w := (StoredGroupedCompletion.rawIndex n).symm i
    kernel p.get (support a) w * crop r (StoredGroupedCompletion.readSource X c) w)).sum

def checkBinaryGrouped (n r C A : Nat) : Bool := Id.run do
  let X : Source n C := Vector.ofFn (fun c => Vector.ofFn (fun w =>
    if (w.val+c.val)%3=0 then (A : Int) else if (w.val+c.val)%3=1 then -(A : Int) else 0))
  let full := (keyVector n n).toArray
  let requests : Requests n := Vector.ofFn (fun p =>
    if p.val%5=4 then #[] else if p.val%3=0 then full.push (Vector.replicate n false) else full)
  let result := execute r X requests
  let prep := prepare r X
  let pairs := prep.value.pairs
  let s := CappedSubsetList.count n r
  let correct := (List.finRange (2^n)).all fun p =>
    let rows := result.value.get p
    rows.size == (requests.get p).size &&
    ((List.finRange rows.size).all fun i =>
      (List.finRange C).all fun c =>
        BinaryCell.view ((rows[i.val]).get c) == directBinaryGrouped r X c (pairs.get p)
          ((requests.get p).getD i.val (Vector.replicate n false)))
  let addressOK := (List.finRange (2^n)).all fun p =>
    (List.finRange s).all fun j =>
      let loc := BinaryGroupedCoordinates.locate (pairs.get p) (prep.value.keys.get j)
      loc.value.index == (GroupedCoordinates.coordinates (pairs.get p) (prep.value.keys.get j)).index &&
      decide (loc.bitSteps ≤ BinaryGroupedCoordinates.addressBudget n)
  let groupCells := (prep.value.groups.toList.map fun g => (g.toList.map fun v => v.toList.length).sum).sum
  let outputCells := (result.value.toList.map fun g => (g.toList.map fun v => v.toList.length).sum).sum
  let M := StoredGroupedCompletion.requestCount requests
  let widthsOK := (prep.value.groups.toList.all fun g => g.toList.all fun row => row.toList.all fun v =>
    decide ((BinaryCell.view v).natAbs ≤ A)) &&
    result.value.toList.all fun g => g.toList.all fun row => row.toList.all fun v =>
      decide ((BinaryCell.view v).natAbs.size ≤ n+A.size)
  let emptyRequests : Requests n := Vector.replicate (2^n) #[]
  let empty := execute r X emptyRequests
  let emptyOK := empty.value.toList.all Array.isEmpty && empty.bitSteps == prep.bitSteps &&
    decide (empty.bitSteps ≤ totalBits n r C A 0) && decide (empty.control ≤ totalControl n r C 0)
  return correct && addressOK && widthsOK && groupCells == 2^n*s*C && outputCells == M*C && emptyOK &&
    decide (prep.bitSteps ≤ preparationBits n r C A) && decide (prep.control ≤ preparationControl n r C) &&
    decide (result.bitSteps ≤ totalBits n r C A M) && decide (result.control ≤ totalControl n r C M)

def binaryGroupedChecks : Bool :=
  ((List.range 5).all fun n => (List.range (n+2)).all fun r => checkBinaryGrouped n r (2*3*2) 17) &&
  ((List.range 4).all fun n => (List.range (n+2)).all fun r => checkBinaryGrouped n r 0 0) &&
  ([0,1,2,3,7,8,15,16,255,256,65535,65536].all fun A =>
    (List.range 4).all fun r => checkBinaryGrouped 2 r 3 A)

#eval do
  if binaryGroupedChecks then
    IO.println "PASS: binary grouped preparation/completion through n=4; independent raw-tensor equality for every coefficient, charged binary addresses, signed/zero inputs and bit boundaries through 65536, partial-sum widths, full B*q*F cells, duplicate/empty requests, zero-column boundary, and both counters."
  else throw (IO.userError "Binary grouped program failed")
