import GraphResidualFamilies
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



def codeOf {n : Nat} (v : Vector Bool n) : Nat :=
  ((List.finRange n).map fun i => if v.get i then 2^i.val else 0).sum

def checkChannels (m t : Nat) : Bool :=
  let out := ResidualFamilyKeys.channels m t
  let codes := out.value.map codeOf
  let expected := (List.range (2^(m+m))).filter fun n =>
    ((List.range (m+m)).filter fun i => digit 2 n i==1).length<t
  codes.mergeSort (·≤·)==expected && codes.length==(codes.eraseDups).length &&
    out.bitSteps==0 && out.control≤(2*m+1)*(16*m+32)*ResidualFamilyKeys.channelCount m t+4

def checkFamily (L m t C A : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let keys := ResidualFamilyKeys.prepare shape.layout t
  let raw := rawFixture L C A
  let out := RetainedResidualFamily.execute keys.value raw
  let g := keys.value.masks.toArray.size
  let h := keys.value.channels.toArray.size
  if keys.bitSteps != 0 || keys.control>ResidualFamilyKeys.prepareBudget L m t g ||
      out.bitSteps>RetainedResidualFamily.bitBudget L m C t g A ||
      out.control>RetainedResidualFamily.controlBudget L m C t g then return false
  let masks := keys.value.masks.toList.map fun a => codeOf a.bits
  if masks.length != masks.eraseDups.length || masks != (shape.layout.codes.toList.map Fin.val) then return false
  for row in out.value.toList do
    for groups in row.toList do
      if groups.toArray.size != h then return false
      for e in groups.toList do
        let cn := ResidualFamilyKeys.normal e.channel
        let co := ResidualFamilyKeys.opposite e.channel
        if (cn.toList.filter id).length+(co.toList.filter id).length≥t then return false
        if (e.normalMask.bits.toList.filter id).length != m ||
           (e.oppositeMask.bits.toList.filter id).length != m then return false
        if e.rows.toArray.size != 3^(2*(L-m)) then return false
        for i in List.finRange e.rows.toArray.size do
          let poly := e.rows.toArray[i]
          if poly.toArray.size != m+1 then return false
          for d in List.range (m+3) do
            for r in List.finRange C do
              let coeff := BinaryCell.view ((poly.toArray.getD d (Vector.replicate C BinaryCell.zero)).get r)
              if coeff  !=  reference L (codeOf e.normalMask.bits) (codeOf e.oppositeMask.bits)
                (codeOf cn) (codeOf co) (m/2) A i.val d r.val then return false
              if coeff.natAbs>2^m*(4^m*A) then return false
  return GraphResidualFamilies.familyEntries out.value==g*g*h

def checkContainer : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime 1 0
  let keys := ResidualFamilyKeys.prepare shape.layout 1
  let raw := rawFixture 1 3 7
  let sources : ExactHalfBandSources.Families 1 0 3 :=
    Vector.replicate 1 (Vector.replicate 1 (Vector.replicate 1 raw,Vector.replicate 1 raw))
  let out := GraphResidualFamilies.execute keys.value sources
  let g := keys.value.masks.toArray.size
  return out.bitSteps≤GraphResidualFamilies.bitBudget 1 0 3 1 g 7 &&
    out.control≤GraphResidualFamilies.controlBudget 1 0 3 1 g &&
    GraphResidualFamilies.rootEntries out.value==2*g*g

def require (b : Bool) (s : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++s))
  IO.println ("PASS: "++s)
  (← IO.getStdout).flush

def main : IO Unit := do
  require ((List.range 8).all fun n => (List.range (2^n)).all fun x =>
    let out := ResidualFamilyKeys.decode n x
    codeOf out.value==x && out.bitSteps==0 && out.control==ResidualFamilyKeys.decodeBudget n)
    "explicit good-code decoder through L=7, exact retained bits and control recurrence"
  require ((List.range 6).all fun m => (List.range (2*m+3)).all fun t => checkChannels m t)
    "strict joint channel coverage, uniqueness and enumeration costs through m=5, including t=0"
  for L in List.range 3 do
    for m in List.range (L+1) do
      for t in List.range (2*m+2) do
        require (checkFamily L m t 3 7) s!"complete retained family versus independent dense coefficients: L={L}, m={m}, t={t}"
  require (checkFamily 1 1 2 9 65536 && checkFamily 1 1 1 0 0)
    "repeated request columns, coefficient bit boundary and zero cyclic columns"
  require checkContainer "retained outer translation/run container at m=0, both input families and aggregate counters"
  IO.println "PASS: bounded residual-family suite completed; no graph-source or FFT runtime attempt was rerun."
