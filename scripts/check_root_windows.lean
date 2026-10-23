import GraphRootWindows
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

def refWeight (k ell word offset start : Nat) : Nat :=
  ((List.range ell).filter fun j => digit 3 word (offset+(start+j)%k)==2).length

def refOwner (k ell cap cn co word : Nat) : Option Nat :=
  if k==0 then some 0 else
  let r := cap-max cn co
  let offset := if co≤cn then 0 else k
  let total := ((List.range k).filter fun i => digit 3 word (offset+i)==2).length
  if total≤r then (List.range k).find? fun start => refWeight k ell word offset start≤r*ell/k else none

def checkFlatten (F C : Nat) : Bool :=
  let block : Block F C := Vector.ofFn fun d => Vector.ofFn fun r =>
    (BinaryMultiplierAdapter.encodeInteger (signedValue 65536 (d.val+2*r.val))).value
  let out := ResidualWindowSource.flatten block
  out.bitSteps≤F*(C*BackendScalarBits.backendScalarUnit (65536:Nat).size) &&
  out.control≤F*(40*C+48)+8*F*(F*C)+16 &&
  out.value.toArray.size==F*C &&
  (List.finRange (F*C)).all fun col =>
    BinaryCell.view (out.value.get col)==signedValue 65536 (col.val/C+2*(col.val%C))

def checkEntry {L m C : Nat} (e : RetainedResidualFamily.Entry L m C) (A : Nat) : Bool := Id.run do
  let cn := (ResidualFamilyKeys.normal e.channel).toList.count true
  let co := (ResidualFamilyKeys.opposite e.channel).toList.count true
  let k := L-m
  let R := 2^m*(4^m*A)
  let expected := (List.range (3^(2*k))).map fun word =>
    (List.range (m+1)).flatMap fun d => (List.range C).map fun r =>
      reference L (codeOf e.normalMask.bits) (codeOf e.oppositeMask.bits)
        (codeOf (ResidualFamilyKeys.normal e.channel)) (codeOf (ResidualFamilyKeys.opposite e.channel))
        (m/2) A word d r
  for ell in [0,1,k,k+1] do
    let out := RetainedRootWindows.execute ell e
    if out.value.counts != (cn,co) || out.bitSteps>RetainedRootWindows.bitBudget L m C R ||
        out.control>RetainedRootWindows.controlBudget L m C ell then return false
    if RetainedRootWindows.coefficientCells out.value != (1+RetainedRootWindows.slots k)*3^(2*k)*((m+1)*C) then return false
    if k==0 then
      if out.value.windows.owners.isSome then return false
    else
      match out.value.windows.owners with
      | none => return false
      | some owners =>
        for i in List.finRange (3^(2*k)) do
          if (owners.get i).map Fin.val != refOwner k ell (m/2) cn co i.val then return false
    for i in List.finRange (3^(2*k)) do
      let owner := refOwner k ell (m/2) cn co i.val
      for col in List.finRange ((m+1)*C) do
        let ref := (expected.getD i.val []).getD col.val 0
        if BinaryCell.view ((out.value.source.get i).get col) != ref then return false
        let values := (out.value.windows.components.toList.map fun part => BinaryCell.view ((part.get i).get col))
        if values.sum != ref then return false
        for slot in List.finRange (RetainedRootWindows.slots k) do
          let actual := values.getD slot.val 0
          if actual != (if owner==some slot.val then ref else 0) || actual.natAbs>R then return false
  return true

def checkFamily (L m t C A : Nat) (onlyFirstPair : Bool := false) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let keys := ResidualFamilyKeys.prepare shape.layout t
  let raw := rawFixture L C A
  if onlyFirstPair then
    match keys.value.masks.toList with
    | [] => return false
    | a::_ =>
      for c in keys.value.channels.toList do
        if !checkEntry (RetainedResidualFamily.produce raw a a c).value A then return false
      return true
  let roots := RetainedResidualFamily.execute keys.value raw
  let windows := GraphRootWindows.family 1 roots.value
  let G := keys.value.masks.toArray.size
  let R := 2^m*(4^m*A)
  if windows.bitSteps>GraphRootWindows.familyBitBudget L m C t G R ||
      windows.control>GraphRootWindows.familyControlBudget L m C t G 1 ||
      GraphRootWindows.familyCells windows.value != G^2*ResidualFamilyKeys.channelCount m t*
        ((1+RetainedRootWindows.slots (L-m))*3^(2*(L-m))*((m+1)*C)) then return false
  for row in roots.value.toList do
    for groups in row.toList do
      for e in groups.toList do
        if !checkEntry e A then return false
  return true

/-- Independent ownership test with both half choices, ties, impossible caps,
and nontrivial cyclic windows. Input coefficients obey the selected cap. -/
def checkPartition (k C ell cap cn co : Nat) : Bool := Id.run do
  let input : BinaryWindowPartition.Source k C := Vector.ofFn fun word => Vector.ofFn fun col =>
    let offset := if co≤cn then 0 else k
    let rare := ((List.range k).filter fun i => digit 3 word.val (offset+i)==2).length
    (BinaryMultiplierAdapter.encodeInteger
      (if rare≤cap-max cn co then signedValue 7 (word.val+col.val) else 0)).value
  let out := RetainedRootWindows.partition ell cap cn co input
  if out.bitSteps>RetainedRootWindows.partitionBitBudget k C 7 ||
      out.control>RetainedRootWindows.partitionControlBudget k C ell then return false
  for word in List.finRange (3^(2*k)) do
    let owner := refOwner k ell cap cn co word.val
    for col in List.finRange C do
      let ref := BinaryCell.view ((input.get word).get col)
      let values := out.value.components.toList.map fun part => BinaryCell.view ((part.get word).get col)
      if values.sum != ref then return false
      for slot in List.finRange (RetainedRootWindows.slots k) do
        if values.getD slot.val 0 != (if owner==some slot.val then ref else 0) then return false
  return true

def checkContainer : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime 1 0
  let keys := ResidualFamilyKeys.prepare shape.layout 1
  let raw := rawFixture 1 3 7
  let sources : ExactHalfBandSources.Families 1 0 3 :=
    Vector.replicate 1 (Vector.replicate 1 (Vector.replicate 1 raw,Vector.replicate 1 raw))
  let roots := GraphResidualFamilies.execute keys.value sources
  let out := GraphRootWindows.execute 1 roots.value
  let G := keys.value.masks.toArray.size
  return out.bitSteps≤GraphRootWindows.bitBudget 1 0 3 1 G 7 &&
    out.control≤GraphRootWindows.controlBudget 1 0 3 1 G 1 &&
    GraphRootWindows.coefficientCells out.value==2*G^2*(2*9*3) &&
    ((out.value.toList.flatMap fun row => row.toList).flatMap fun runs => runs.toList).all fun pair =>
      GraphRootWindows.familyCells pair.1==GraphRootWindows.familyCells pair.2

def require (b : Bool) (s : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++s))
  IO.println ("PASS: "++s)
  (← IO.getStdout).flush

def main : IO Unit := do
  require ((List.range 6).all fun m => (List.range (2^(m+m))).all fun code =>
    let c := mask (m+m) code
    let out := RetainedRootWindows.weights c
    out.value==(((List.range m).filter fun i => digit 2 code i==1).length,
      ((List.range m).filter fun i => digit 2 code (m+i)==1).length) &&
    out.bitSteps≤2*RetainedRootWindows.countBudget m && out.control==32*m+24)
    "binary channel weights, decoded values and counters through m=5"
  require ((List.range 5).all fun F => [0,1,3,9].all fun C => checkFlatten F C)
    "all degree/cyclic copies, empty dimensions, repeated columns and 65536 bit boundary"
  require ((List.range 3).all fun k => (List.range 5).all fun ell =>
    ([(0,0),(1,0),(0,1),(1,1),(2,1)] : List (Nat×Nat)).all fun pair =>
      checkPartition k 3 ell 1 pair.1 pair.2)
    "independent first-owner reference, both sides, normal ties and zero residual dimension"
  for L in List.range 3 do
    for m in List.range (L+1) do
      for t in [0,1,2*m+1] do
        require (checkFamily L m t 3 7) s!"retained root/windows versus independent dense coefficients: L={L}, m={m}, t={t}"
  require (checkFamily 3 2 3 3 7 true) "nonzero remaining rare budget, selected mask pair at L=3,m=2"
  require (checkFamily 4 2 1 1 7 true) "two residual positions and nontrivial cyclic windows at L=4,m=2"
  require (checkFamily 1 1 2 9 65536 && checkFamily 1 1 1 0 0)
    "root/windows with repeated request columns, bit boundary and zero cyclic columns"
  require checkContainer "both-input retained translation/run container at m=0 and aggregate counters"
  IO.println "PASS: bounded root-window suite completed; no graph-source or FFT runtime attempt was rerun."
