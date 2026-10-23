import GraphPrefixCompletion
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

/-- Independent explicit ordinary four-by-three matrix. -/
def ordinaryEntry (q a : Nat) : Int :=
  if q==0 then (if a==0 || a==2 then 1 else 0)
  else if q==1 then (if a==0 then 1 else 0)
  else if q==2 then (if a==1 then 1 else if a==2 then -1 else 0)
  else if a==1 then 1 else 0

def labelAt (q i : Nat) : Fin 4 := ⟨digit 4 q i, Nat.mod_lt _ (by decide)⟩
def wordAt (w i : Nat) : Fin 3 := ⟨digit 3 w i, Nat.mod_lt _ (by decide)⟩


def requestLabels (N : Nat) (code : Nat) : Vector (Fin 4) N := Vector.ofFn fun i => labelAt code i.val

def checkCompletion (P ell C r A : Nat) : Bool := Id.run do
  let get := fun word col => signedValue A (word+[0,1,1].getD col 0)
  let X : RetainedCappedGroups.Source P ell C := Vector.ofFn fun w => Vector.ofFn fun c =>
    (BinaryMultiplierAdapter.encodeInteger (get w.val c.val)).value
  let prefixOut := CappedPrefixProgram.execute r X
  let labels := ((List.range (4^(P+ell))).map (requestLabels (P+ell))).toArray
  let labels := labels++#[requestLabels (P+ell) 0,requestLabels (P+ell) 0]
  let out := PrefixCompletionProgram.execute prefixOut.value labels
  if out.value.requests.size != labels.size then return false
  if out.bitSteps>PrefixCompletionProgram.bitBudget P ell r C (2^P*A) labels.size ||
      out.control>PrefixCompletionProgram.controlBudget P ell r C labels.size then return false
  if PrefixCompletionProgram.outputCells out.value != labels.size*C ||
      PrefixCompletionProgram.selectorCells out.value != labels.size*CappedSubsetList.count ell r then return false
  for q in List.finRange labels.size do
    if hq : q.val<out.value.requests.size then
      let row := out.value.requests[q.val]
      if row.labels != labels[q.val] then return false
    else return false
    let rowOutput := if hq : q.val<out.value.requests.size then out.value.requests[q.val].output else Vector.replicate C BinaryCell.zero
    for c in List.finRange C do
      let expected := ((List.range (3^(P+ell))).map fun w =>
        if ((List.range ell).filter fun j => digit 3 w (P+j)==2).length≤r then
          get w c.val*((List.finRange (P+ell)).map fun i => ordinaryEntry (labels[q.val].get i).val (digit 3 w i.val)).prod else 0).sum
      if BinaryCell.view (rowOutput.get c) != expected then return false
  let empty := PrefixCompletionProgram.execute prefixOut.value #[]
  return empty.value.requests.isEmpty && empty.bitSteps≤PrefixCompletionProgram.bitBudget P ell r C (2^P*A) 0

def oppositeOrdinary (label a : Nat) : Int :=
  if label==0 then (if a==0 || a==1 then 1 else 0)
  else if label==1 then (if a==0 then 1 else if a==1 then -1 else 0)
  else if label==2 then (if a<2 then 1 else -1)
  else if a==0 then 1 else if a==1 then -1 else 1

def checkCompletedWindow {k C : Nat} (X : BinaryWindowPartition.Source k C) (get : Nat → Nat → Int)
    (A ell cap cn co : Nat) : Bool := Id.run do
  let partition := RetainedRootWindows.partition (min ell k) cap cn co X
  let labels := ((List.range (4^(2*k))).map (requestLabels (2*k))).toArray++#[requestLabels (2*k) 0,requestLabels (2*k) 0]
  for slot in List.finRange (RetainedRootWindows.slots k) do
    let forward := RetainedOppositeTransform.execute (partition.value.components.get slot)
    let permuted := RetainedWindowPermutation.prepare (min ell k) (decide (co≤cn)) slot forward.value.result
    let prefixOut := WindowPrefixProgram.execute ell cap cn co permuted.value.coefficients
    let out := WindowCompletionProgram.execute prefixOut.value permuted.value.layout labels
    if out.completed.value.requests.size != labels.size ||
        out.completed.bitSteps>PrefixCompletionProgram.bitBudget (WindowPrefixProgram.prefixLength k ell) (min ell k)
          prefixOut.value.rareCap C (2^(WindowPrefixProgram.prefixLength k ell)*(2^k*A)) labels.size ||
        out.requests.work+out.completed.control>labels.size*(48*k+56)+8+
          PrefixCompletionProgram.controlBudget (WindowPrefixProgram.prefixLength k ell) (min ell k) prefixOut.value.rareCap C labels.size then return false
    for q in List.finRange labels.size do
      for c in List.finRange C do
        let expected := ((List.range (3^(2*k))).map fun w =>
          if refOwner k (min ell k) cap cn co w==some slot.val then
            get w c.val*((List.finRange k).map fun j => ordinaryEntry ((labels[q.val]).get ⟨j.val,by omega⟩).val (digit 3 w j.val)).prod*
              ((List.finRange k).map fun j => oppositeOrdinary ((labels[q.val]).get ⟨k+j.val,by omega⟩).val (digit 3 w (k+j.val))).prod else 0).sum
        if hq : q.val<out.completed.value.requests.size then
          if BinaryCell.view (out.completed.value.requests[q.val].output.get c) != expected then return false
        else return false
  return true

def checkWindowSynthetic (k C A ell cap cn co : Nat) : Bool :=
  let get := fun w c => signedValue A (w+c)
  let X : BinaryWindowPartition.Source k C := Vector.ofFn fun w => Vector.ofFn fun c =>
    (BinaryMultiplierAdapter.encodeInteger (get w.val c.val)).value
  checkCompletedWindow X get A ell cap cn co

def checkOneRoot : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime 3 2
  let keys := ResidualFamilyKeys.prepare shape.layout 1
  let raw := rawFixture 3 3 7
  match keys.value.masks.toList,keys.value.channels.toList with
  | a::_,c::_ =>
    let root := (RetainedResidualFamily.produce raw a a c).value
    let source := ResidualWindowSource.execute root
    let get := fun w col => reference 3 (codeOf a.bits) (codeOf a.bits)
      (codeOf (ResidualFamilyKeys.normal c)) (codeOf (ResidualFamilyKeys.opposite c)) 1 7 w (col/3) (col%3)
    checkCompletedWindow source.value get (2^2*(4^2*7)) 1 1
      ((ResidualFamilyKeys.normal c).toList.count true) ((ResidualFamilyKeys.opposite c).toList.count true)
  | _,_ => false

def physical : CompactBlocks.PhysicalFactorization 5 := ⟨1,5,by decide,by decide,by decide,by decide⟩
def dimensions (n : Nat) : BinaryFoldedFactory.Plan (n:=n) (h:=1) physical :=
  ⟨2,1,0,FoldedCounts.foldWidth 3,FoldedBackendExecution.outerSize n 3,
    FoldedBackendExecution.middleSize 1 3,3,16,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩

def checkTargets (n : Nat) : Bool := Id.run do
  let p := dimensions n
  let shape := BinaryBackendExecution.prepareShapeRuntime 2 1
  let data : BinaryFoldedFormation.BinaryTable n := Vector.ofFn fun i => Vector.ofFn fun j =>
    (BinaryMultiplierAdapter.encodeInteger ((i.val:Int)-2*(j.val:Int)-7)).value
  let out := GraphCompletionRequests.prepare physical p shape data
  if out.physical.value.toArray.size != n*n*3 || out.physical.bitSteps != 0 ||
      out.physical.control>n*n*3*(1000*4^5+32)+8 then return false
  for q in List.finRange (n*n*3) do
    let i := q.val/3/n
    let j := q.val/3%n
    let w := q.val%3
    let target : Int := 3*((i:Int)-2*(j:Int)-7-((w:Int)-1))
    let row := out.folded.requests.value.get q
    if row.row.val != i*2 || row.column.val != j*2 || row.coefficient.val != ((-target)%5).toNat then return false
    let routed := out.physical.value.get q
    if routed.bandL != i*2/shape.width || routed.bandR != j*2/shape.width || routed.coefficient != row.coefficient then return false
  let B := GraphCompletionRequests.metadataWidth n 1 3 5
  let W := ((List.finRange n).map fun i => ((List.finRange n).map fun j =>
    (BinaryCell.view ((data.get i).get j)).natAbs.size).sum).sum
  if out.folded.geometry.bitSteps+out.folded.requests.bitSteps>10000*(B+1)^2+2000000*(n*n*3)*(W+B+10)^2 then return false
  let keys := ResidualFamilyKeys.prepare shape.layout 0
  match keys.value.masks.toList with
  | mask::_ =>
    for right in [false,true] do
      let projected := GraphCompletionRequests.project right mask mask out.physical.value
      if projected.value.labels.size != n*n*3 || projected.bitSteps != 0 ||
          projected.control>48*2+24+(n*n*3*(32+48)+8) then return false
      let positions := (List.finRange 2).filter fun i => !mask.bits.get i
      for q in List.finRange (n*n*3) do
        if hq : q.val<projected.value.labels.size then
          for j in List.finRange 2 do
            let position := (positions[j.val%1]?).getD 0
            let physicalIndex := (if (j.val==0) != right then 0 else 2)+position.val
            let expected := ((out.physical.value.get q).outside.toArray[physicalIndex]?).getD 0
            if (projected.value.labels[q.val]).get j != expected then return false
        else return false
    return true
  | [] => false

def require (b : Bool) (s : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++s))
  IO.println ("PASS: "++s)
  (← IO.getStdout).flush

def main : IO Unit := do
  for P in [0,1,2] do
    for ell in [0,1,2] do
      require ((List.range (ell+2)).all fun r => checkCompletion P ell 3 r 7) s!"all completion labels P={P}, ell={ell}, all caps; duplicate requests and columns"
  require (checkCompletion 1 1 3 1 65536) "binary width boundary 65536"
  require (checkCompletion 1 1 0 1 7) "empty coefficient vector"
  require (checkWindowSynthetic 0 3 7 5 0 0 0) "zero residual dimension and clamped window"
  require (checkWindowSynthetic 1 3 7 0 1 0 0) "zero window length"
  require (checkWindowSynthetic 2 3 7 1 2 0 1 && checkWindowSynthetic 2 3 7 1 2 1 0) "both opposite orientations and all cyclic windows"
  require (checkTargets 0 && checkTargets 2 && checkTargets 5) "actual folded requests n=0,2,5 with signed targets and all cyclic residues; physical band tags and residual projection"
  require checkOneRoot "actual retained L=3,m=2 root through completion; independent physical coefficient reference"
  IO.println "PASS: bounded completion suite finished; no full graph or production FFT attempt."
