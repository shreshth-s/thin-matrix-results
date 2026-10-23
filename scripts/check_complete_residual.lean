import CompleteResidualArray
open ThinMatrix ThinMatrix.WalshEmbedding ThinMatrix.BinaryResidualPolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def digit (base code position : Nat) : Nat := code/base^position%base
def mask (L code : Nat) : Vector Bool L := Vector.ofFn fun i => digit 2 code i.val==1
def signedValue (A seed : Nat) : Int := if seed%3==0 then (A:Int) else if seed%3==1 then -(A:Int) else 0

def normal : Nat → NormalLetter | 0 => .x1 | 1 => .x2 | 2 => .p1 | _ => .p2
def opposite : Nat → OppositeLetter | 0 => .s | 1 => .v | _ => .w
def nCode : NormalLetter → Nat | .x1 => 0 | .x2 => 1 | .p1 => 2 | .p2 => 3
def oCode : OppositeLetter → Nat | .s => 0 | .v => 1 | .w => 2

/-- Nine columns are three cyclic residues for requests [0,1,1]. -/
def sourceValue {L : Nat} (A : Nat) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) (r : Nat) : Int :=
  let request := [0,1,1].getD (r/3) 0
  let h := ((List.finRange L).map fun i => (i.val+1)*nCode (n i)+(i.val+2)*oCode (o i)).sum
  signedValue A (h+request+2*(r%3))

def rawFixture (L C A : Nat) : BinarySourceFormation.RawStore L C :=
  (BinarySourceFormation.rawBuild fun n o =>
    ⟨Vector.ofFn (fun r => (BinaryMultiplierAdapter.encodeInteger (sourceValue A n o r.val)).value),0⟩).value

/-- Independent dense tensor coefficient: enumerate all 4^m normal and 3^m
opposite letters, use a binomial coefficient for the product of (1+z) factors,
and assemble physical positions by counting preceding mask bits. -/
def reference (L maskN maskO cn co cap A word degree col : Nat) : Int :=
  let indices := List.range L
  let ns := indices.filter fun i => digit 2 maskN i==1
  let os := indices.filter fun i => digit 2 maskO i==1
  let kn := L-ns.length
  ((List.range (4^ns.length)).map fun nc =>
    let compatible := (List.range ns.length).all fun i =>
      if digit 2 cn i==1 then digit 4 nc i==3 else digit 4 nc i < 3
    let p := ((List.range ns.length).filter fun i => digit 4 nc i==2).length
    let minus := ((List.range ns.length).filter fun i => digit 4 nc i < 2).length
    let nf : Int := if compatible then (-1)^minus*(p.choose degree:Int) else 0
    ((List.range (3^os.length)).map fun oc =>
      let ofactor := ((List.range os.length).map fun i =>
        if digit 2 co i==1 then (if digit 3 oc i==2 then (1:Int) else 0)
        else if digit 3 oc i==0 then 2 else 0).prod
      let n : Fin L → NormalLetter := fun j =>
        let rank := (ns.filter fun i => i < j.val).length
        if digit 2 maskN j.val==1 then normal (digit 4 nc rank)
        else let x := digit 3 word (j.val-rank); normal (if x==2 then 3 else x)
      let o : Fin L → OppositeLetter := fun j =>
        let rank := (os.filter fun i => i < j.val).length
        if digit 2 maskO j.val==1 then opposite (digit 3 oc rank)
        else opposite (digit 3 word (kn+j.val-rank))
      if ((List.finRange L).filter fun i => n i==.p2).length ≤ cap &&
         ((List.finRange L).filter fun i => o i==.w).length ≤ cap
      then nf*ofactor*sourceValue A n o col else 0).sum).sum


def checkSpace (L code : Nat) : Bool :=
  let bits := mask L code
  let out := BinaryResidualDegreeSpace.execute bits
  let expected := ((List.range L).filter fun i => digit 2 code i==1).length+1
  out.value==expected && decide (out.bitSteps ≤ BinaryResidualDegreeSpace.bitBudget L) && out.control==8*L+12

def checkComplete (L C maskN maskO cnCode coCode cap A : Nat) : Bool := Id.run do
  let mn := mask L maskN
  let mo := mask L maskO
  let cn := mask (ResidualLayout.selected mn).length cnCode
  let co := mask (ResidualLayout.selected mo).length coCode
  let raw := rawFixture L C A
  let out := CompleteResidualArray.execute cap raw mn mo cn co
  let mN := (ResidualLayout.selected mn).length
  let mO := (ResidualLayout.selected mo).length
  let kN := (ResidualLayout.remaining mn).length
  let kO := (ResidualLayout.remaining mo).length
  let correct := (List.finRange (3^(kN+kO))).all fun i =>
    (List.range (2*L+4)).all fun d => (List.finRange C).all fun r =>
      let row := (out.value.get i).toArray.getD d (Vector.replicate C BinaryCell.zero)
      BinaryCell.view (row.get r)==reference L maskN maskO cnCode coCode cap A i.val d r.val &&
      decide ((BinaryCell.view (row.get r)).natAbs.size ≤ mO+2*mN+A.size)
  let cells := (out.value.toList.map fun b => (b.toList.map fun row => row.toArray.size).sum).sum
  return correct && cells==3^(kN+kO)*(mN+1)*C &&
    decide (out.bitSteps ≤ CompleteResidualArray.bitBudget L mN mO kN kO C cap A) &&
    decide (out.control ≤ CompleteResidualArray.controlBudget L mN mO kN kO C)

def checkChannels (L mn mo : Nat) : Bool :=
  (List.range (2^(ResidualLayout.selected (mask L mn)).length)).all fun cn =>
    (List.range (2^(ResidualLayout.selected (mask L mo)).length)).all fun co =>
      (List.range (L+2)).all fun cap => checkComplete L 9 mn mo cn co cap 17

/-- A source making the highest degree nonzero: the root is exactly
2^L*A*(1+z)^L, so the last stored coefficient must survive. -/
def topDegree (L : Nat) : Bool := Id.run do
  let bits := Vector.replicate L true
  let cn := Vector.replicate (ResidualLayout.selected bits).length false
  let raw : BinarySourceFormation.RawStore L 3 := (BinarySourceFormation.rawBuild fun n o =>
    let nonzero := (List.finRange L).all fun i => n i==.p1 && o i==.s
    ⟨Vector.ofFn (fun r : Fin 3 =>
      (BinaryMultiplierAdapter.encodeInteger (if nonzero then (r.val+1:Int) else 0)).value),0⟩).value
  let out := CompleteResidualArray.execute L raw bits bits cn cn
  return out.value.toList.all fun block =>
    block.toArray.size==L+1 && (List.range (L+3)).all fun d => (List.finRange 3).all fun r =>
      BinaryCell.view ((block.toArray.getD d (Vector.replicate 3 BinaryCell.zero)).get r)==
        (2^L*(r.val+1)*L.choose d:Int)

#eval do
  if !((List.range 8).all fun L => (List.range (2^L)).all fun code => checkSpace L code) then
    throw (IO.userError "binary formal-degree selection failed")
  IO.println "PASS: binary degree-space selection for every mask through L=7; derived F=mN+1, binary count/add/decode prices and control."
  if !(((List.range 2).all fun L => (List.range (2^L)).all fun mn =>
      (List.range (2^L)).all fun mo => checkChannels L mn mo) &&
      ([(0,0),(1,2),(3,3),(1,3)].all fun pair => checkChannels 2 pair.1 pair.2) &&
      ([0,1,2,3,7,8,255,256,65535,65536].all fun A => checkComplete 1 3 1 1 0 0 1 A) &&
      checkComplete 2 0 1 2 0 0 1 0 && (List.range 4).all topDegree) then
    throw (IO.userError "complete residual polynomial fixture failed")
  IO.println "PASS: complete residual arrays against independent dense binomial tensor coefficients through L=2; all retained coefficients and zero tails through degree 2*L+3, nonzero highest-degree examples through L=3, asymmetric masks, repeated request columns, zero dimensions, bit boundaries through 65536, full storage and both construction counters. No FFT runtime was invoked."
