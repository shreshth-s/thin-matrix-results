import StoredGroupedCompletion
open ThinMatrix ThinMatrix.CroppedGroupedSuffix ThinMatrix.StoredGroupedCompletion
open ThinMatrix.WalshEmbedding
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def direct {n C : Nat} (r : Nat) (X : Source n C Int) (c : Fin C)
    (p : Cube n) (A : Finset (Fin n)) : Int :=
  (List.ofFn (fun i : Fin (3^n) =>
    let w := (rawIndex n).symm i
    kernel p A w * crop r (readSource X c) w)).sum

def checkShape (n r : Nat) : Bool := Id.run do
  let C := 2*3*2 -- two batches, three cyclic slots, two formal coefficients
  let X : Source n C Int := Vector.ofFn (fun c => Vector.ofFn (fun w =>
    (((17*w.val+11*c.val+w.val*c.val)%29 : Nat):Int)-14))
  let stored := prepare r X
  let full := (CappedSubsetList.generate n n).toArray
  let requests := Vector.ofFn (fun p : Fin (2^n) =>
    if p.val%3=0 then full.push ∅ else full)
  let masks := selectorFamilies stored.keys requests
  let result := runAll stored masks
  let correct := (List.finRange (2^n)).all fun p =>
    let rows := (result.groups.get p).outputs
    rows.size == (requests.get p).size &&
    ((List.finRange rows.size).all fun i =>
      (List.finRange C).all fun c =>
        (rows[i.val]).get c == direct r X c ((HalfSourceIntegerGreedy.cubeIndex n).symm p)
          ((requests.get p).getD i.val ∅))
  let s := CappedSubsetList.count n r
  let cells := (stored.groups.toList.map fun g =>
    (g.toList.map fun v => v.toList.length).sum).sum
  let outCells := (result.groups.toList.map fun g =>
    (g.outputs.toList.map fun v => v.toList.length).sum).sum
  let price := requestCount masks*(s*(8*C+16)+3*C+20)+20*2^n+4
  let empty := runGroup stored ⟨0,Nat.two_pow_pos n⟩ #[]
  return correct && cells == 2^n*s*C && outCells == requestCount requests*C &&
    decide (result.work ≤ price) && empty.outputs.isEmpty && decide (empty.work ≤ 4)

def checks : Bool := (List.range 5).all fun n => (List.range (n+2)).all (checkShape n)
#eval do
  if checks then
    IO.println "PASS: n=0..4, all capped suffix groups and activity sets, duplicate and empty requests, every B*q*F coefficient, and returned completion counters."
  else throw (IO.userError "Grouped completion runtime check failed")
