import RootRequestSelection
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

/-- Independent explicit ordinary four-by-three matrix. -/
def ordinaryEntry (q a : Nat) : Int :=
  if q==0 then (if a==0 || a==2 then 1 else 0)
  else if q==1 then (if a==0 then 1 else 0)
  else if q==2 then (if a==1 then 1 else if a==2 then -1 else 0)
  else if a==1 then 1 else 0

def labelAt (q i : Nat) : Fin 4 := ⟨digit 4 q i, Nat.mod_lt _ (by decide)⟩
def wordAt (w i : Nat) : Fin 3 := ⟨digit 3 w i, Nat.mod_lt _ (by decide)⟩


def requestLabels (N : Nat) (code : Nat) : Vector (Fin 4) N := Vector.ofFn fun i => labelAt code i.val

def oppositeOrdinary (label a : Nat) : Int :=
  if label==0 then (if a==0 || a==1 then 1 else 0)
  else if label==1 then (if a==0 then 1 else if a==1 then -1 else 0)
  else if label==2 then (if a<2 then 1 else -1)
  else if a==0 then 1 else if a==1 then -1 else 1

def physical : CompactBlocks.PhysicalFactorization 5 := ⟨1,5,by decide,by decide,by decide,by decide⟩
def dimensions (n : Nat) : BinaryFoldedFactory.Plan (n:=n) (h:=1) physical :=
  ⟨2,1,0,FoldedCounts.foldWidth 3,FoldedBackendExecution.outerSize n 3,
    FoldedBackendExecution.middleSize 1 3,3,16,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩

def require (b : Bool) (s : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++s))
  IO.println ("PASS: "++s)
  (← IO.getStdout).flush


/-- Dense contraction of the original root, without using window ownership,
permutations, transformed coefficients, prefix keys or returned query sums. -/
def checkAggregate {k C : Nat} (X : BinaryWindowPartition.Source k C) (get : Nat → Nat → Int)
    (A ell cap cn co : Nat) (emptyRequests := false) : Bool := Id.run do
  let partition := RetainedRootWindows.partition (min ell k) cap cn co X
  let permuted := GroupedPreparation.ofStoredFn partition.value.components fun slot =>
    let forward := RetainedOppositeTransform.execute (partition.value.components.get slot)
    (RetainedWindowPermutation.prepare (min ell k) (decide (co≤cn)) slot forward.value.result).value
  let prefixes := GroupedPreparation.ofStoredFn permuted fun slot =>
    (WindowPrefixProgram.execute ell cap cn co (permuted.get slot).coefficients).value
  let layouts := permuted.map RetainedWindowPermutation.Prepared.layout
  let labelArray := if emptyRequests then #[] else
    ((List.range (4^(2*k))).map (requestLabels (2*k))).toArray++#[requestLabels (2*k) 0,requestLabels (2*k) 0]
  let labels : Vector _ labelArray.size := ⟨labelArray,rfl⟩
  let out := RetainedWindowCompletion.execute prefixes layouts labels
  let leafBound := 2^(WindowPrefixProgram.prefixLength k ell)*(2^k*A)
  let totalBound := RetainedRootWindows.slots k*(2^(WindowPrefixProgram.length k ell)*leafBound)
  if out.bitSteps>RetainedWindowCompletion.bitBudget prefixes leafBound labels.toArray.size ||
      out.control>RetainedWindowCompletion.controlBudget prefixes labels.toArray.size then return false
  if RetainedWindowCompletion.outputCells out.value != (RetainedRootWindows.slots k+1)*labels.toArray.size*C then return false
  for j in List.finRange labels.toArray.size do
    for c in List.finRange C do
      let expected := ((List.range (3^(2*k))).map fun w =>
        get w c.val*((List.finRange k).map fun a => ordinaryEntry ((labels.get j).get ⟨a.val,by omega⟩).val (digit 3 w a.val)).prod*
          ((List.finRange k).map fun a => oppositeOrdinary ((labels.get j).get ⟨k+a.val,by omega⟩).val (digit 3 w (k+a.val))).prod).sum
      let actual := BinaryCell.view ((out.value.sums.value.get j).output.get c)
      if actual != expected || actual.natAbs>totalBound then return false
  return true

def checkAggregateSynthetic (k C A ell cap cn co : Nat) (emptyRequests := false) : Bool :=
  let get := fun w c =>
    if cn+((List.range k).filter fun j => digit 3 w j==2).length≤cap &&
       co+((List.range k).filter fun j => digit 3 w (k+j)==2).length≤cap
    then signedValue A (w+[0,1,1].getD c 0) else 0
  let X : BinaryWindowPartition.Source k C := Vector.ofFn fun w => Vector.ofFn fun c =>
    (BinaryMultiplierAdapter.encodeInteger (get w.val c.val)).value
  checkAggregate X get A ell cap cn co emptyRequests

def checkAggregateRoot : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime 3 1
  let keys := ResidualFamilyKeys.prepare shape.layout 1
  let raw := rawFixture 3 3 7
  match keys.value.masks.toList,keys.value.channels.toList with
  | a::_,c::_ =>
    let root := (RetainedResidualFamily.produce raw a a c).value
    let source := ResidualWindowSource.execute root
    let get := fun w col => reference 3 (codeOf a.bits) (codeOf a.bits)
      (codeOf (ResidualFamilyKeys.normal c)) (codeOf (ResidualFamilyKeys.opposite c)) 0 7 w (col/3) (col%3)
    checkAggregate source.value get (2^1*(4^1*7)) 1 0
      ((ResidualFamilyKeys.normal c).toList.count true) ((ResidualFamilyKeys.opposite c).toList.count true)
  | _,_ => false

def checkNoWindows : Bool := Id.run do
  let sources : Vector (WindowPrefixProgram.Prepared 1 1 3) 0 := #v[]
  let layouts : Vector (RetainedWindowPermutation.Layout 2) 0 := #v[]
  let labels := #v[requestLabels 2 0,requestLabels 2 0]
  let out := RetainedWindowCompletion.execute sources layouts labels
  if out.bitSteps != 0 || RetainedWindowCompletion.outputCells out.value != 6 then return false
  return out.value.sums.value.toList.all fun row => row.output.toList.all fun cell => BinaryCell.view cell==0

def checkSelection : Bool := Id.run do
  let p := dimensions 5
  let shape := BinaryBackendExecution.prepareShapeRuntime 2 1
  let data : BinaryFoldedFormation.BinaryTable 5 := Vector.ofFn fun i => Vector.ofFn fun j =>
    (BinaryMultiplierAdapter.encodeInteger ((i.val:Int)-2*(j.val:Int)-7)).value
  let requests := (GraphCompletionRequests.prepare physical p shape data).physical.value
  let sums : Vector (RetainedWindowCompletion.SumRow 0 6) (FoldedBackendExecution.windowQuerySize 5) :=
    requests.map fun q => ⟨#v[],#v[],Vector.ofFn fun c => (BinaryMultiplierAdapter.encodeInteger (signedValue 65536 (q.row.val+c.val))).value⟩
  for right in [false,true] do
    for bandL in [0,1,2] do
      for bandR in [0,1,2] do
        for a in List.finRange (GoodMapEmbedding.goodSlots 2 1).card do
          for b in List.finRange (GoodMapEmbedding.goodSlots 2 1).card do
            let out := RootRequestSelection.select bandL bandR right a b requests sums
            if out.bitSteps>requests.toArray.size*(6*BackendScalarBits.backendScalarUnit (65536:Nat).size) ||
                out.control>requests.toArray.size*(40*6+112)+8 then return false
            for j in List.finRange (FoldedBackendExecution.windowQuerySize 5) do
              let q := requests.get j
              let nr := if right then q.column.val/4 else q.row.val/4
              let op := if right then q.row.val/4 else q.column.val/4
              let selected := q.bandL==bandL && q.bandR==bandR && nr==a.val && op==b.val
              if (out.value.get j).matched != selected then return false
              for c in List.finRange 6 do
                let expected := if selected then signedValue 65536 (q.row.val+c.val) else 0
                if BinaryCell.view ((out.value.get j).output.get c) != expected then return false
  let out := GraphCompletionRequests.prepare physical p shape data
  let B := GraphCompletionRequests.metadataWidth 5 1 3 5
  let W := ((List.finRange 5).map fun i => ((List.finRange 5).map fun j =>
    (BinaryCell.view ((data.get i).get j)).natAbs.size).foldl max 0).foldl max 0
  return out.folded.geometry.bitSteps+out.folded.requests.bitSteps≤10000*(B+1)^2+2000000*(5*5*3)*(W+B+10)^2

def main : IO Unit := do
  require (checkAggregateSynthetic 0 3 7 5 0 0 0) "zero residual dimension; all coefficients and duplicate requests"
  require (checkAggregateSynthetic 1 3 7 0 1 0 0) "zero window length"
  for ell in [0,1,2,5] do
    require (checkAggregateSynthetic 2 3 7 ell 1 0 0) s!"all 256 request forms; two executed windows; ell={ell}; rare support and duplicates"
  require (checkAggregateSynthetic 2 3 7 1 2 0 1 && checkAggregateSynthetic 2 3 7 1 2 1 0) "both selected window orientations"
  require (checkAggregateSynthetic 1 3 65536 1 1 0 0) "signed binary width boundary 65536"
  require (checkAggregateSynthetic 1 0 7 1 1 0 0) "empty coefficient vectors"
  require (checkAggregateSynthetic 2 3 7 1 1 0 0 true) "empty request vector"
  require checkNoWindows "empty window family; repeated request rows retained"
  require checkAggregateRoot "actual L=3,m=1 retained root; two windows; all formal degrees/cyclic residues; independent physical coefficient reference"
  require checkSelection "actual folded requests; both orientations, all band/mask selections; full copied columns; maximum target-cell width"
  IO.println "PASS: bounded root-completion suite finished; no full graph or production FFT attempt."
