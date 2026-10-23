import BinaryResidualArray
open ThinMatrix ThinMatrix.WalshEmbedding ThinMatrix.BinaryResidualPolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def digit (base code position : Nat) : Nat := code/base^position%base
def mask (L code : Nat) : Vector Bool L := Vector.ofFn fun i => digit 2 code i.val==1

def checkLayout (L code : Nat) : Bool := Id.run do
  let bits := mask L code
  let out := ResidualLayout.build bits
  let ns := (List.finRange L).filter fun i => digit 2 code i.val==1
  let os := (List.finRange L).filter fun i => digit 2 code i.val==0
  let a := (ns.map fun i => 2*i.val+1).toArray
  let b := (os.map fun i => 2*i.val+2).toArray
  let assembled := ResidualLayout.assembleWord out.value a b 0
  return out.value.normalPositions==ns.toArray && out.value.otherPositions==os.toArray &&
    ((List.finRange L).all fun i =>
      let chosen := if digit 2 code i.val==1 then ns else os
      let index := (chosen.filter fun j => j.val < i.val).length
      let locN := ResidualLayout.locate i ns
      let locO := ResidualLayout.locate i os
      out.value.routes.get i==(digit 2 code i.val==1,index) &&
      assembled.value.get i==2*i.val+(if digit 2 code i.val==1 then 1 else 2) &&
      locN.value==ns.idxOf i && locO.value==os.idxOf i &&
      decide (locN.bitSteps ≤ ResidualLayout.locateBudget L) &&
      decide (locO.bitSteps ≤ ResidualLayout.locateBudget L)) &&
    decide (out.bitSteps ≤ L*ResidualLayout.locateBudget L) && decide (out.control ≤ L*(8*L+66)+20) &&
    assembled.bitSteps==0 && decide (assembled.control ≤ 38*L+8)

def signedValue (A seed : Nat) : Int := if seed%3==0 then (A:Int) else if seed%3==1 then -(A:Int) else 0

def checkPolynomial (F C A : Nat) : Bool := Id.run do
  let block := fun seed => Vector.ofFn fun d : Fin F => Vector.ofFn fun r : Fin C =>
    (BinaryMultiplierAdapter.encodeInteger (signedValue A (seed+d.val+2*r.val))).value
  let a := block 0
  let b := block 1
  let c := block 2
  let out := privateRow a b c
  return ((List.finRange F).all fun d => (List.finRange C).all fun r =>
    cellView out.value d r== -signedValue A (d.val+2*r.val)-signedValue A (1+d.val+2*r.val)+
      signedValue A (2+d.val+2*r.val)+(if d.val==0 then 0 else signedValue A (2+(d.val-1)+2*r.val)) &&
    decide ((cellView out.value d r).natAbs ≤ 4*A)) &&
    decide (out.bitSteps ≤ F*(C*(9*BackendScalarBits.backendScalarUnit (4*A).size))) &&
    decide (out.control ≤ F*(C*116+40)+8)

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

def checkRoot (L C F maskN maskO cnCode coCode cap A : Nat) : Bool := Id.run do
  let mn := mask L maskN
  let mo := mask L maskO
  let cn := mask (ResidualLayout.selected mn).length cnCode
  let co := mask (ResidualLayout.selected mo).length coCode
  let raw := rawFixture L C A
  let out := BinaryResidualArray.execute F cap raw mn mo cn co
  let mN := (ResidualLayout.selected mn).length
  let mO := (ResidualLayout.selected mo).length
  let kN := (ResidualLayout.remaining mn).length
  let kO := (ResidualLayout.remaining mo).length
  let correct := (List.finRange (3^(kN+kO))).all fun i =>
    (List.finRange F).all fun d => (List.finRange C).all fun r =>
      cellView (out.value.get i) d r==reference L maskN maskO cnCode coCode cap A i.val d.val r.val &&
      decide ((cellView (out.value.get i) d r).natAbs.size ≤ mO+2*mN+A.size)
  let cells := (out.value.toList.map fun b => (b.toList.map fun row => row.toArray.size).sum).sum
  return correct && cells==3^(kN+kO)*F*C &&
    decide (out.bitSteps ≤ BinaryResidualArray.bitBudget L mN mO kN kO C F cap A) &&
    decide (out.control ≤ BinaryResidualArray.controlBudget L mN mO kN kO C F)

def checkChannels (L mn mo : Nat) : Bool :=
  (List.range (2^(ResidualLayout.selected (mask L mn)).length)).all fun cn =>
    (List.range (2^(ResidualLayout.selected (mask L mo)).length)).all fun co =>
      (List.range (L+2)).all fun cap => checkRoot L 9 4 mn mo cn co cap 17

#eval do
  if !((List.range 7).all fun L => (List.range (2^L)).all fun code => checkLayout L code) then
    throw (IO.userError "retained layout fixture failed")
  IO.println "PASS: retained layouts through L=6, both position arrays, every route and assembly, present/absent binary searches, construction bits and control."
  if !([0,1,2,3,7,8,255,256,65535,65536].all fun A =>
      [(0,0),(0,3),(4,0),(4,3)].all fun shape => checkPolynomial shape.1 shape.2 A) then
    throw (IO.userError "binary shifted polynomial fixture failed")
  IO.println "PASS: shifted binary coefficient rows, signs, all degrees/columns, zero dimensions and bit boundaries through 65536; copies, arithmetic bounds and control."
  if !(((List.range 2).all fun L => (List.range (2^L)).all fun mn =>
      (List.range (2^L)).all fun mo => checkChannels L mn mo) &&
      ([(0,0),(1,2),(3,3),(1,3)].all fun pair => checkChannels 2 pair.1 pair.2) &&
      ([0,1,2,3,7,8,255,256,65535,65536].all fun A => checkRoot 1 3 3 1 1 0 0 1 A) &&
      checkRoot 2 0 3 1 2 0 0 1 0 && checkRoot 1 3 0 1 0 1 0 1 2) then
    throw (IO.userError "retained binary residual array fixture failed")
  IO.println "PASS: complete retained binary residual arrays against independent dense binomial tensor coefficients through L=2; asymmetric layouts/channel counts, all crops, all four formal degrees and nine cyclic/request columns including duplicate requests, zero boundaries, input-derived widths, construction bits and control. No FFT runtime was invoked."
