import GraphLowDegreeFilter
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


def require (b : Bool) (s : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++s))
  IO.println ("PASS: "++s)
  (← IO.getStdout).flush

/-- Independent polynomial arithmetic over explicit coefficient lists. -/
def polyMul (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map fun d =>
    ((List.range a.length).map fun i => if i≤d then a.getD i 0*b.getD (d-i) 0 else 0).sum

def localCoeffs (n o : Nat) : List Int :=
  [if o==0 then (if n<2 then -2 else if n==2 then 2 else 0) else 0,
   if n==2 && o==0 then 2 else if n==3 && o==2 then 1 else 0]

def allowedWords (L m maskN maskO label : Nat) : List (Nat×Nat×Int) :=
  ((List.range (4^L)).flatMap fun nc => (List.range (3^L)).map fun oc => (nc,oc)).filterMap fun x =>
    let nc := x.1; let oc := x.2
    let positions := List.range L
    let ns := positions.filter fun i => digit 2 maskN i==1
    let os := positions.filter fun i => digit 2 maskO i==1
    if (positions.filter fun i => digit 4 nc i==3).length>m/2 ||
       (positions.filter fun i => digit 3 oc i==2).length>m/2 ||
       (positions.any fun i => digit 2 maskN i==0 && digit 4 nc i==2) then none
    else
      let normalOutside := positions.filter fun i => digit 2 maskN i==0
      let oppositeOutside := positions.filter fun i => digit 2 maskO i==0
      let factor := ((normalOutside.zipIdx).map fun (i,j) => ordinaryEntry (digit 4 label j)
          (if digit 4 nc i==3 then 2 else digit 4 nc i)).prod *
        ((oppositeOutside.zipIdx).map fun (i,j) => oppositeOrdinary (digit 4 label (L-m+j)) (digit 3 oc i)).prod
      if factor==0 || ns.length != m || os.length != m then none else some (nc,oc,factor)

def directLow (L m t q maskN maskO labelL labelR residue : Nat) : Int :=
  let left := allowedWords L m maskN maskO labelL
  let right := allowedWords L m maskO maskN labelR
  let ns := (List.range L).filter fun i => digit 2 maskN i==1
  let os := (List.range L).filter fun i => digit 2 maskO i==1
  (left.map fun x => (right.map fun y =>
    let pol := (ns.map fun i => localCoeffs (digit 4 x.1 i) (digit 3 y.2.1 i)) ++
      (os.map fun i => localCoeffs (digit 4 y.1 i) (digit 3 x.2.1 i))
    let coeffs := pol.foldl polyMul [1]
    let weighted := ((List.range t).map fun d => (-1)^(t-d-1)*((2*m-d-1).choose (t-d-1):Int)*coeffs.getD d 0).sum
    let cyclic := ((List.range q).map fun r => ((List.range q).map fun s =>
      if (r+s)%q==residue then
        sourceValue 7 (fun i : Fin L => normal (digit 4 x.1 i.val)) (fun i => opposite (digit 3 x.2.1 i.val)) r *
        sourceValue 7 (fun i : Fin L => normal (digit 4 y.1 i.val)) (fun i => opposite (digit 3 y.2.1 i.val)) s else 0).sum).sum
    let dx : Int := (((List.range L).filter fun i => digit 3 x.2.1 i==2).length:Int)-
      (((List.range L).filter fun i => digit 4 x.1 i==3).length:Int)
    let dy : Int := (((List.range L).filter fun i => digit 4 y.1 i==3).length:Int)-
      (((List.range L).filter fun i => digit 3 y.2.1 i==2).length:Int)
    if dx==dy && -(m:Int)≤dx && dx≤(m:Int) then x.2.2*y.2.2*weighted*cyclic else 0).sum).sum

def sourceDegree {L : Nat} (right : Bool) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : Int :=
  let nw := ((List.finRange L).filter fun i => n i==.p2).length
  let ow := ((List.finRange L).filter fun i => o i==.w).length
  if right then (nw:Int)-(ow:Int) else (ow:Int)-(nw:Int)

def rawRun (L q : Nat) (right : Bool) (run : Int) : BinarySourceFormation.RawStore L q :=
  (BinarySourceFormation.rawBuild fun n o =>
    ⟨Vector.ofFn (fun r => (BinaryMultiplierAdapter.encodeInteger
      (if sourceDegree right n o==run then sourceValue 7 n o r.val else 0)).value),0⟩).value

/-- Decode physical positions independently by counting preceding mask bits. -/
def compressedLabels {L m q : Nat} (right : Bool) (a b : ResidualFamilyKeys.Mask L m)
    (request : GraphCompletionRequests.Physical L m q) : Nat :=
  let ns := (List.range L).filter fun i => digit 2 (codeOf a.bits) i==0
  let os := (List.range L).filter fun i => digit 2 (codeOf b.bits) i==0
  let labels := request.outside.toList.map Fin.val
  ((ns.zipIdx).map fun (i,j) => 4^j*labels.getD (if right then L+i else i) 0).sum+
    ((os.zipIdx).map fun (i,j) => 4^(L-m+j)*labels.getD (if right then i else L+i) 0).sum

def checkMaskRuns (L m t q : Nat) [NeZero q] (hm : m≤L) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let keys := ResidualFamilyKeys.prepare shape.layout t
  let B := ThinMatrixBackend.tileWidth L m
  let hp := ThinMatrixBackend.tileWidth_pos L m hm
  let requests : Vector (TilingCosts.Request (2*B) q) 4 := Vector.ofFn fun j =>
    ⟨⟨if j.val==3 then B else if j.val==1 then B-1 else 0,by dsimp [B] at *; split <;> (try split) <;> omega⟩,
     ⟨if j.val==3 then B else if j.val==1 then 0 else B-1,by dsimp [B] at *; split <;> (try split) <;> omega⟩,0⟩
  let physical := requests.map fun r => (GraphCompletionRequests.locate shape hm r).value
  let x := Vector.ofFn fun d : Fin (2*m+1) => rawRun L q false (SourceFormation.runValue m d)
  let y := Vector.ofFn fun d : Fin (2*m+1) => rawRun L q true (SourceFormation.runValue m d)
  let complete := fun (raw : BinarySourceFormation.RawStore L q) (right : Bool)
      (ai bi : Fin (GoodMapEmbedding.goodSlots L m).card) (ch : ResidualFamilyKeys.Channel m) =>
    let a := keys.value.masks.get ai
    let b := keys.value.masks.get bi
    let root := (RetainedResidualFamily.produce raw a b ch).value
    let X := (ResidualWindowSource.execute root).value
    let cn := (ResidualFamilyKeys.normal ch).toList.count true
    let co := (ResidualFamilyKeys.opposite ch).toList.count true
    let partition := RetainedRootWindows.partition (L-m) (L-m) cn co X
    let permuted := GroupedPreparation.ofStoredFn partition.value.components fun slot =>
      let forward := RetainedOppositeTransform.execute (partition.value.components.get slot)
      (RetainedWindowPermutation.prepare (L-m) (decide (co≤cn)) slot forward.value.result).value
    let prefixes := GroupedPreparation.ofStoredFn permuted fun slot =>
      (WindowPrefixProgram.execute (L-m) (L-m) cn co (permuted.get slot).coefficients).value
    let labels := physical.map fun z => (GraphCompletionRequests.residual right
      (GraphCompletionRequests.positions a).value (GraphCompletionRequests.positions b).value z).value
    let out := RetainedWindowCompletion.execute prefixes (permuted.map RetainedWindowPermutation.Prepared.layout) labels
    RootRequestSelection.select 0 0 right ai bi physical out.value.sums.value
  let pair := fun ai bi =>
    RootProductCollection.execute (Vector.replicate (2*m+1) ()) (fun run =>
      RootProductCollection.execute keys.value.channels (fun c =>
        let ch := keys.value.channels.get c
        let a := complete (x.get run) false ai bi ch
        let b := complete (y.get run) true bi ai (ResidualChannelTranspose.swap ch)
        let products := PairedRootRows.execute a.value b.value
        WeightedRootProducts.prepare (2*m) t (ch.toList.count true) products.value.products.value)
        (fun z j => (z.outputs.value.get j).sum.value)) RootProductCollection.output
  let out := RootProductCollection.execute keys.value.masks (fun ai =>
    RootProductCollection.execute keys.value.masks (pair ai) RootProductCollection.output) RootProductCollection.output
  for j in List.finRange 4 do
    let z := physical.get j
    let request := requests.get j
    if z.bandL != request.row.val/B || z.bandR != request.column.val/B then return false
    let ai : Fin (GoodMapEmbedding.goodSlots L m).card := RootRequestSelection.rowRank z.row
    let bi : Fin (GoodMapEmbedding.goodSlots L m).card := RootRequestSelection.rowRank z.column
    if ai.val != (request.row.val%B)/4^(L-m) || bi.val != (request.column.val%B)/4^(L-m) then return false
    let a := keys.value.masks.get ai
    let b := keys.value.masks.get bi
    for r in List.finRange q do
      let expected := if request.row.val<B && request.column.val<B then
        directLow L m t q (codeOf a.bits) (codeOf b.bits)
          (compressedLabels false a b z) (compressedLabels true b a z) r.val else 0
      if BinaryCell.view ((RootProductCollection.output out.value j).get r) != expected then return false
  return true

/-- Independent interval enumeration and matching-degree counts. -/
def checkRunIndices (m : Nat) : Bool :=
  let actual := (List.finRange (2*m+1)).map (SourceFormation.runValue m)
  let expected := (List.range (2*m+1)).map fun i => (i:Int)-(m:Int)
  actual==expected && actual.eraseDups==actual &&
  (List.finRange (2*m+1)).all fun i =>
    (SourceFormation.runIndex m (SourceFormation.runValue m i) (SourceFormation.runValue_mem m i)).val==i.val

open ThinMatrix.SourceFormation ThinMatrix.ExactHalfSourcePlan
def cubes (L : Nat) : List (Cube L) :=
  (List.range (2^L)).map fun n => fun i => n/2^i.val%2==1

def countRef {L : Nat} (b : Cube L) : Nat := ((List.finRange L).filter fun i => b i).length

def imageRef {L m : Nat} (cols : Vector (Vector Bool m) L) (b : Cube L) : Cube m :=
  fun j => ((List.finRange L).filter fun i => b i && (cols.get i).get j).length%2==1

def inverseRef {L m : Nat} (cols : Vector (Vector Bool m) L) (Q : Cube L) (h : Cube m) : List (Cube L) :=
  (cubes L).filter fun b => ((List.finRange L).all fun i => !b i || Q i) && decide (imageRef cols b=h)

def checkWeights (L m : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let cs := ExactHalfWeightTable.candidates shape.environment.gammaColumns
  let weights := ExactHalfWeightTable.build shape.environment.good cs.value
  let correct := (cubes L).all fun Q => (cubes m).all fun h =>
    let good := tableRead 2 L shape.environment.good (cubeKey Q)
    let preimages := inverseRef shape.environment.gammaColumns Q h
    let expected := if good then (preimages.map countRef).sum else 0
    let actual := tableRead 2 m (tableRead 2 L weights.value (cubeKey Q)) (cubeKey h)
    actual==expected && (!good || preimages.length==1)
  return correct && cs.value.length==2^L &&
    decide (cs.bitSteps≤2^L*ExactHalfWeightTable.candidateBitBudget L) &&
    decide (weights.operations≤ExactHalfWeightTable.buildBudget L m)

def firstRef {L m : Nat} (shape : ThinMatrixBackend.ShapePlan L m) (ds : Shifts m)
    (Q : Finset (Fin L)) (h : Cube m) : Nat :=
  ((List.range ds.toArray.size).find? fun j =>
    let shift := (ds.toArray[j]?).getD (Vector.replicate m false)
    let preimages := inverseRef shape.environment.gammaColumns (setBits Q) (xorBits h shift.get)
    let weight := if ThinMatrixBackend.readGoodSet shape.environment.good Q then
      (preimages.map countRef).sum else 0
    decide (weight ≤ m / 2)).getD 0

def checkPlan {L m : Nat} (shape : ThinMatrixBackend.ShapePlan L m)
    (plan : BinaryGroupedCoordinates.Run (ExactHalfSourcePlan.Plan L m)) : Bool :=
  (cubes L).all (fun Q => (cubes m).all fun h =>
    (readPick plan.value.picks (cubeSupport Q) h).val==firstRef shape plan.value.shifts (cubeSupport Q) h) &&
  plan.value.shifts.toArray.size==(if m==0 then 1 else 64*m^3) &&
  decide (plan.bitSteps≤HalfSourceRetainedTranslations.arithmeticBudget m+
    2^L*ExactHalfWeightTable.candidateBitBudget L)

def rawDatum (a j seed A : Nat) : Int :=
  if (3*a+j+seed)%3==0 then A else if (a+2*j+seed)%3==1 then -(A:Int) else 0

def expected {L m q : Nat} (shape : ThinMatrixBackend.ShapePlan L m) (plan : ExactHalfSourcePlan.Plan L m)
    (a : BinaryBandSource.StoredLeftMatrix L m q) (b : BinaryBandSource.StoredRightMatrix L m q)
    (r s : Fin (J m)) (run : Fin (2*m+1)) (normal : Fin L → NormalLetter)
    (opposite : Fin L → OppositeLetter) (j : Fin q) (rightSide : Bool) : Int := Id.run do
  let Q := normalSupport normal
  let nw := countRef (normalP2Bits normal)
  let ow := countRef (oppositeWBits opposite)
  let gammaN := imageRef shape.environment.gammaColumns (normalP2Bits normal)
  let gammaO := imageRef shape.environment.gammaColumns (oppositeWBits opposite)
  let frequency := imageRef shape.environment.deltaColumns (oppositeVBits opposite)
  let h := if rightSide then gammaO else gammaN
  let k := if rightSide then gammaN else gammaO
  let h' := xorBits h (plan.shifts.get r).get
  let k' := xorBits k (plan.shifts.get s).get
  let picked := firstRef shape plan.shifts Q (if rightSide then k' else h')
  let runOK := if rightSide then nw+m==ow+run.val else ow+m==nw+run.val
  if !ThinMatrixBackend.readGoodSet shape.environment.good Q || !runOK ||
      picked != (if rightSide then s.val else r.val) then return 0
  let total := ((cubes (L-m)).map fun outer =>
    let sign : Int := if ((List.finRange (L-m)).filter fun i => frequency i && outer i).length%2==0 then 1 else -1
    let cell := if rightSide then
      (BinaryBandSource.storedRawRightReader shape.environment.good shape.good shape.layout b
        Q (normalOuterBits normal) h' k' outer j).value
      else (BinaryBandSource.storedRawLeftReader shape.environment.good shape.good shape.layout a
        Q (normalOuterBits normal) outer h' k' j).value
    sign*BinaryCell.view cell).sum
  return (2:Int)^nw*total

def checkSources (L m A : Nat) : Bool := Id.run do
  let q := 3
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let prepared := ExactHalfSourcePlan.prepare shape
  if !checkPlan shape prepared then return false
  let a : BinaryBandSource.StoredLeftMatrix L m q := Vector.ofFn fun i =>
    Vector.ofFn fun j => (BinaryMultiplierAdapter.encodeInteger (rawDatum i.val j.val 1 A)).value
  let b : BinaryBandSource.StoredRightMatrix L m q := Vector.ofFn fun i =>
    Vector.ofFn fun j => (BinaryMultiplierAdapter.encodeInteger (rawDatum i.val j.val 2 A)).value
  let ca := ExactHalfBandSources.cacheLeft shape a
  let cb := ExactHalfBandSources.cacheRight shape b
  let ids := (List.finRange prepared.value.shifts.toArray.size).filter fun j =>
    j.val==0 || j.val==1
  for ri in ids do
    for si in ids do
      let r : Fin (J m) := ⟨ri.val,by simpa using ri.isLt⟩
      let s : Fin (J m) := ⟨si.val,by simpa using si.isLt⟩
      let x := ExactHalfBandSources.left shape prepared.value ca.value r s
      let y := ExactHalfBandSources.right shape prepared.value cb.value r s
      if x.operations>ExactHalfBandSources.bandBudget L m q A ||
          y.operations>ExactHalfBandSources.bandBudget L m q A then return false
      for run in List.finRange (2*m+1) do
        for nc in List.range (4^L) do
          for oc in List.range (3^L) do
            let normal := fun i : Fin L => indexNormal ⟨nc/4^i.val%4, Nat.mod_lt _ (by decide)⟩
            let opposite := fun i : Fin L => indexOpposite ⟨oc/3^i.val%3,Nat.mod_lt _ (by decide)⟩
            for j in List.finRange q do
              let actualL := BinaryCell.view (BinarySourceFormation.readRaw (x.value.get run) normal opposite j)
              let actualR := BinaryCell.view (BinarySourceFormation.readRaw (y.value.get run) normal opposite j)
              if actualL != expected shape prepared.value a b r s run normal opposite j false ||
                  actualR != expected shape prepared.value a b r s run normal opposite j true then return false
  return true


def main : IO Unit := do
  require ((List.range 9).all checkRunIndices) "each shared integer degree run occurs exactly once, m=0..8"
  require (checkSources 0 0 7 && checkSources 1 0 7) "actual masked Walsh source stores against subset/parity reference; zero and ordinary residual dimensions"
  require (checkSources 2 1 7) "actual translated run stores, both orientations, selected translation pairs, every word and cyclic coefficient"
  require (checkMaskRuns 0 0 0 3 (by decide) && checkMaskRuns 0 0 1 3 (by decide)) "empty strict channels, zero dimension, duplicate requests and rejected bands"
  require (checkMaskRuns 1 0 1 3 (by decide)) "actual physical locators and ordinary forms with zero distinguished dimension"
  require (checkMaskRuns 2 1 2 3 (by decide)) "all actual mask pairs and shared runs; independent degree-matched physical pencil"
  require (checkMaskRuns 2 2 3 3 (by decide)) "nonzero rare-letter channels, shared degree filtering, all formal/cyclic coefficients"
  IO.println "PASS: bounded LOW recombination suite finished; no full graph or production FFT evaluation."
