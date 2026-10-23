import PreparedGroupedProgram
open ThinMatrix ThinMatrix.CappedBitPreparation ThinMatrix.CroppedGroupedSuffix
open ThinMatrix.GroupedPreparation
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def directPrepared {n C : Nat} (r : Nat) (X : StoredGroupedCompletion.Source n C Int)
    (c : Fin C) (p a : Key n) : Int :=
  (List.ofFn (fun i : Fin (3^n) =>
    let w := (StoredGroupedCompletion.rawIndex n).symm i
    kernel p.get (support a) w * crop r (StoredGroupedCompletion.readSource X c) w)).sum

def checkPrepared (n r C : Nat) : Bool := Id.run do
  let X : StoredGroupedCompletion.Source n C Int := Vector.ofFn (fun c => Vector.ofFn (fun w =>
    (((17*w.val+11*c.val+w.val*c.val)%29 : Nat):Int)-14))
  let full := (keyVector n n).toArray
  let requests := Vector.ofFn (fun p : Fin (2^n) =>
    if p.val%5=4 then #[] else if p.val%3=0 then full.push (Vector.replicate n false) else full)
  let result := PreparedGroupedProgram.execute r X requests
  let prep := prepare r X
  let pairs := prep.value.pairs
  let s := CappedSubsetList.count n r
  let correct := (List.finRange (2^n)).all fun p =>
    let rows := result.value.get p
    rows.size == (requests.get p).size &&
    ((List.finRange rows.size).all fun i =>
      (List.finRange C).all fun c =>
        (rows[i.val]).get c == directPrepared r X c (pairs.get p)
          ((requests.get p).getD i.val (Vector.replicate n false)))
  let keysOK := decide prep.value.keys.toList.Nodup &&
    prep.value.keys.toList.length == s && pairs.toList.length == 2^n && decide pairs.toList.Nodup
  let groupCells := (prep.value.groups.toList.map fun g => (g.toList.map fun v => v.toList.length).sum).sum
  let outputCells := (result.value.toList.map fun g => (g.toList.map fun v => v.toList.length).sum).sum
  let M := StoredGroupedCompletion.requestCount requests
  let emptyRequests : PreparedGroupedProgram.Requests n := Vector.replicate (2^n) #[]
  let empty := PreparedGroupedProgram.execute r X emptyRequests
  let emptyOK := empty.value.toList.all Array.isEmpty && decide (prep.work ≤ empty.work) &&
    decide (empty.work ≤ PreparedGroupedProgram.totalBudget n r C 0)
  return correct && keysOK && groupCells == 2^n*s*C && outputCells == M*C && emptyOK &&
    decide (prep.work ≤ prepareBudget n r C) &&
    decide (result.work ≤ PreparedGroupedProgram.totalBudget n r C M)

def preparationChecks : Bool :=
  ((List.range 5).all fun n => (List.range (n+2)).all fun r => checkPrepared n r (2*3*2)) &&
  ((List.range 4).all fun n => (List.range (n+2)).all fun r => checkPrepared n r 0)

#eval do
  if preparationChecks then
    IO.println "PASS: preparation through n=4; every capped group, raw-tensor output coefficient, full B*q*F volume, duplicate/empty requests, zero-column boundary, and total preparation/completion counters."
  else throw (IO.userError "Counted grouped preparation failed")
