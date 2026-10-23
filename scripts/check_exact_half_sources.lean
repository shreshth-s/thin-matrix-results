import ExactHalfGraphSources

open ThinMatrix WalshEmbedding SourceFormation ExactHalfSourcePlan
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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
  decide (plan.bitSteps≤2^L*ExactHalfWeightTable.candidateBitBudget L)

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
    j.val==0 || j.val==1 || j.val==31 || j.val+1==prepared.value.shifts.toArray.size
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

def physical : CompactBlocks.PhysicalFactorization 1 := ⟨1,1,by decide,by decide,by decide,by decide⟩
def dimensions : BinaryFoldedFactory.Plan (n:=1) (h:=1) physical :=
  ⟨1,1,0,FoldedCounts.foldWidth 3,FoldedBackendExecution.outerSize 1 3,
    FoldedBackendExecution.middleSize 1 3,3,16,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩

def checkGraph : Bool := Id.run do
  let input := (BinaryFoldedFormation.encodeInputs (Vector.replicate 1 (Vector.replicate 1 (-7))) (Vector.replicate 1 (Vector.replicate 1 11)) (Vector.replicate 1 (Vector.replicate 1 (-4)))).value
  let out := ExactHalfGraphSources.execute physical dimensions ⟨0,by decide⟩ input 0 0
  let n := out.selectors.value.shifts.toArray.size
  return n==64 && out.sources.value.toArray.size==n &&
    (out.sources.value.toList.all fun row => row.toArray.size==n) &&
    decide (out.sources.operations≤ExactHalfBandSources.familiesBudget 1 1 1 1) &&
    out.leftBand.value.toList.all (fun row => row.toList.all fun c => (BinaryCell.view c).natAbs≤1) &&
    out.rightBand.value.toList.all (fun row => row.toList.all fun c => (BinaryCell.view c).natAbs≤1)

def require (b : Bool) (message : String) : IO Unit :=
  if b then do
    IO.println ("PASS: "++message)
    (← IO.getStdout).flush
  else throw (IO.userError ("FAIL: "++message))

def main : IO Unit := do
  for L in List.range 4 do
    for m in List.range (L+1) do
      require (checkWeights L m) s!"inverse-weight table against independent subset/parity enumeration, L={L}, m={m}"
  require (checkSources 0 0 0) "zero-dimensional selector and empty source words"
  require (checkSources 1 0 7) "zero-dimensional selector and signed Walsh sources"
  require (checkSources 1 1 65536) "full translation list, first-occurrence masks and binary coefficient boundary"
  require (checkSources 2 1 7) "both shifted sources against signed Walsh reference and charged formation"
  require checkGraph "binary callback inputs through folded formation, copies and all 4096 translation pairs"
