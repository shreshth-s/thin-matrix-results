import BinaryWindowPartition
open ThinMatrix ThinMatrix.BinaryWindowPartition
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def refDigit (index position : Nat) : Nat := index/3^position%3

def refRare (k : Nat) (normal : Bool) (index position : Nat) : Bool :=
  refDigit index (if normal then position else k+position)==2

def refCount (k : Nat) (normal : Bool) (index : Nat) : Nat :=
  ((List.range k).filter fun j => refRare k normal index j).length

def refWindow (k ell : Nat) (normal : Bool) (index start : Nat) : Nat :=
  ((List.range ell).filter fun j => refRare k normal index ((start+j)%k)).length

def refOwner (k ell r : Nat) (normal : Bool) (index : Nat) : Option Nat :=
  if refCount k normal index≤r then
    (List.range k).find? fun s => decide (refWindow k ell normal index s≤r*ell/k)
  else none

def rawNumber (index c A : Nat) : Int :=
  if (index+2*c)%3=0 then (A : Int) else if (index+2*c)%3=1 then -(A : Int) else 0

def fixture (k C A : Nat) : Source k C :=
  Vector.ofFn fun i => Vector.ofFn fun c => (BinaryMultiplierAdapter.encodeInteger (rawNumber i.val c.val A)).value

def checkPartition (k : Nat) [NeZero k] (ell r C A : Nat) (normal : Bool) : Bool := Id.run do
  let X := fixture k C A
  let out := execute ell r normal X
  let rawChecks := (List.finRange (3^(2*k))).all fun i =>
    let expected := refOwner k ell r normal i.val
    let owner := out.value.owners.get i
    let ownerOK := owner.map Fin.val==expected
    let valuesOK := (List.finRange C).all fun c =>
      let all := (List.finRange k).map fun s =>
        BinaryCell.view (((out.value.components.get s).get i).get c)
      let exact := (List.finRange k).all fun s =>
        let actual := BinaryCell.view (((out.value.components.get s).get i).get c)
        let reference := if expected=some s.val then rawNumber i.val c.val A else 0
        actual==reference && decide (actual.natAbs≤A) &&
          (if r*ell/k<refWindow k ell normal i.val s.val then actual==0 else true)
      exact && all.sum==(if refCount k normal i.val≤r then rawNumber i.val c.val A else 0)
    ownerOK && valuesOK
  let cells := (out.value.components.toList.map fun p => (p.toList.map fun v => v.toList.length).sum).sum
  return rawChecks && cells==k*3^(2*k)*C && out.value.owners.toArray.size==3^(2*k) &&
    decide (out.bitSteps≤bitBudget k C A) && decide (out.control≤controlBudget k C ell)

def refOrdinary (pair active raw : Nat) : Int :=
  if raw=2 then (if active=0 then 0 else if pair=0 then 1 else -1)
  else if raw=pair then 1 else 0

def refKernel (k pair active index : Nat) : Int :=
  ((List.range (2*k)).map fun j => refOrdinary (pair/2^j%2) (active/2^j%2) (refDigit index j)).prod

/-- Independent contractions exercise complete columns and repeated requests.
No prefix-transform implementation or cost is claimed by this reference. -/
def checkTransforms (k : Nat) [NeZero k] (ell r : Nat) (normal : Bool) : Bool := Id.run do
  let C := 6
  let X := fixture k C 3
  let out := execute ell r normal X
  let requests := [(0,0),(1,1),(1,1),(2^(2*k)-1,2^(2*k)-1),(0,2^(2*k)-1)]
  return requests.all fun req => (List.finRange C).all fun c =>
    let actual := ((List.finRange k).map fun s =>
      ((List.finRange (3^(2*k))).map fun i => refKernel k req.1 req.2 i.val*
        BinaryCell.view (((out.value.components.get s).get i).get c)).sum).sum
    let reference := ((List.range (3^(2*k))).map fun i =>
      if refCount k normal i≤r then refKernel k req.1 req.2 i*rawNumber i c.val 3 else 0).sum
    actual==reference

def checkPrepare (cap cn co : Nat) : Bool := Id.run do
  let X := fixture 2 6 7
  let out := prepare 1 cap cn co X
  let normal := decide (co≤cn)
  let r := cap-max cn co
  let sideOK := (if normal then cn else co)==max cn co && (if cn=co then normal else true)
  return sideOK && (List.finRange (3^4)).all (fun i =>
    (out.value.owners.get i).map Fin.val==refOwner 2 1 r normal i.val) &&
    decide (out.bitSteps≤bitBudget 2 6 7) && decide (out.control≤controlBudget 2 6 1+8)

def checkZero (C A : Nat) : Bool := Id.run do
  let X := fixture 0 C A
  let out := executeZero X
  return ((List.finRange C).all fun c => BinaryCell.view (((out.value.get 0).get 0).get c)==rawNumber 0 c.val A) &&
    out.value.toArray.size==1 && decide (out.bitSteps≤C*BackendScalarBits.backendScalarUnit A.size) &&
    decide (out.control≤36*C+56)

def checkSelector (k : Nat) [NeZero k] (ell r code : Nat) : Bool := Id.run do
  let b := Vector.ofFn fun i : Fin k => code/2^i.val%2==1
  let total := (b.toList.filter id).length
  let weights := (List.finRange k).map fun s => ((List.range ell).filter fun j =>
    code/2^((s.val+j)%k)%2==1).length
  let expected := if total≤r then (List.range k).find? fun s => decide (weights[s]!≤r*ell/k) else none
  let out := WindowSelection.choose ell r b
  return out.value.map Fin.val==expected && weights.sum==ell*total &&
    (if total≤r then out.value.isSome else out.value.isNone) &&
    decide (out.work≤WindowSelection.budget k ell)

def windowChecks : Bool :=
  ((List.range 7).all fun n =>
    let k := n+1
    (List.range (k+2)).all fun ell => (List.range (k+2)).all fun r =>
      (List.range (2^k)).all fun code => checkSelector k ell r code) &&
  ((List.range 9).all fun n => (List.range (3^n+2)).all fun i =>
    let out := WindowSelection.decode n i
    (List.finRange n).all (fun j => (out.value.get j).val==refDigit i j.val) &&
    decide (out.work≤n*(6*n+16)+2)) &&
  ((List.range 3).all fun n =>
    let k := n+1
    (List.range (k+1)).all fun ell => (List.range (k+2)).all fun r =>
      [false,true].all fun b => checkPartition k ell r 12 17 b) &&
  ((List.range 2).all fun n =>
    let k := n+1
    (List.range (k+1)).all fun ell => (List.range (k+1)).all fun r =>
      [false,true].all fun b => checkTransforms k ell r b) &&
  ((List.range 5).all fun cap => (List.range 4).all fun cn => (List.range 4).all fun co => checkPrepare cap cn co) &&
  ([0,1,2,7,8,255,256,65535,65536].all fun A => checkPartition 2 1 1 3 A true && checkZero 12 A) &&
  checkPartition 2 0 0 0 0 false && checkZero 0 0

#eval do
  if windowChecks then
    IO.println "PASS: first cyclic windows through k=7, direct ternary decoding through n=8, both halves and all tested caps; retained binary partitions through k=3 with every B*q*F column, zero writes, cell counts and separate counters; independent ordinary contractions with repeated requests; channel-side ties, zero-position/zero-column cases and magnitude bit boundaries."
  else throw (IO.userError "Cyclic window fixture failed")
