import GraphFoldedCountCorrect
open ThinMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def require (b : Bool) (label : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++label))
  IO.println ("PASS: "++label)
  (← IO.getStdout).flush

def encode (z : Int) : BinaryCell.Cell := (BinaryMultiplierAdapter.encodeInteger z).value

/-- Independent signed values; repeated requests retain separate positions.
This tests actual normalized coefficient copies, not graph correctness by an
assumed oracle. General graph correctness is kernel checked separately. -/
def checkExtract (M q L : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime 0 0
  let requests : Vector (GraphCompletionRequests.Physical 0 0 (q+1)) M := Vector.ofFn fun i =>
    (GraphCompletionRequests.locate shape (by omega)
      (⟨(0 : Fin 1),0,⟨i.val%(q+1),Nat.mod_lt _ (by omega)⟩⟩ : TilingCosts.Request 1 (q+1))).value
  let low : Vector (Vector BinaryCell.Cell (q+1)) M := Vector.ofFn fun i => Vector.ofFn fun j => encode ((i.val:Int)-3*(j.val:Int))
  let high := Vector.ofFn fun i : Fin M => Vector.ofFn fun j : Fin (q+1) =>
    encode ((4:Int)^L*((i.val:Int)-2*(j.val:Int))-((i.val:Int)-3*(j.val:Int)))
  let values := BinaryLowHighNormalize.table L low high
  let out := NormalizedCoefficientCollection.extract requests values.2.value
  return (List.finRange M).all (fun i => BinaryCell.view (out.value.get i)==(i.val:Int)-2*(i.val%(q+1):Nat)) &&
    decide (out.bitSteps≤M*BackendScalarBits.backendScalarUnit (M+2*(q+1)).size) && decide (out.control≤40*M+8)

/-- Both nested actual binary accumulators retain all S^2 children, including
unmatched zero rows. Compare with a direct independent signed reference. -/
def checkCollection (S M : Nat) : Bool := Id.run do
  let ids : Vector (Fin S) S := Vector.ofFn id
  let child := fun a b : Fin S =>
    let rows : Vector (Vector BinaryCell.Cell 1) M := Vector.ofFn fun i =>
      Vector.replicate 1 (encode (if a.val==i.val%S && b.val==(i.val+1)%S then (i.val:Int)-4 else 0))
    (⟨rows,11+a.val+3*b.val⟩ : ToomCook.Counted _)
  let out := CountedCyclicCollection.execute ids
    (fun a => CountedCyclicCollection.execute ids (child a) (fun rows i => rows.get i)) CountedCyclicCollection.output
  let retained := (List.finRange S).all fun a => (List.finRange S).all fun b =>
    ((out.value.children.get a).value.children.get b).operations==11+a.val+3*b.val
  let reference := (List.finRange M).all fun i =>
    BinaryCell.view ((CountedCyclicCollection.output out.value i).get 0)==if S==0 then 0 else (i.val:Int)-4
  let budget := CountedCyclicCollection.budget (fun a : Fin S => CountedCyclicCollection.budget
    (fun b : Fin S => 11+a.val+3*b.val) M 1 (M+4)) M 1 (S*(M+4))
  return retained && reference && decide (out.operations≤budget)

def checkIndices (L N : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L 0
  let out := RetainedBandIndices.produce shape N
  return (out.value.toList.map Fin.val)==List.range (TilingCosts.bandCount N shape.width) &&
    out.bitSteps==0 && out.control==32*TilingCosts.bandCount N shape.width+32

/-- Original incidence ordering independently decoded using the public
incidence equivalence; three windows and all blocks remain distinct. -/
def checkReindex (n h : Nat) : Bool :=
  (List.finRange (EndToEndAPSP.incidenceSize n h)).all fun i =>
    let grouped := (FoldedBackendExecution.groupedIncidenceEquiv n h).symm i
    let query := (FoldedBackendExecution.windowQueryEquiv n).symm grouped.2
    let original := (EndToEndAPSP.incidenceEquiv n h).symm i
    original.1==query.1 && original.2.1==grouped.1 && original.2.2==query.2

/-- Actual copied bands versus direct original cyclic products. This checks
zero padding and partially filled final bands without running an FFT. -/
def checkBandCopies (L N : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L 0
  let a : BinaryBackendExecution.OriginalLeft N 1 3 := Vector.ofFn fun i => Vector.ofFn fun r => encode ((i.val:Int)-2*(r.val:Int)+1)
  let b : BinaryBackendExecution.OriginalRight N 1 3 := Vector.ofFn fun i => Vector.ofFn fun r => encode (3*(i.val:Int)+(r.val:Int)-2)
  let hp := ThinMatrixBackend.tileWidth_pos L 0 (by omega)
  return (List.finRange N).all fun i => (List.finRange N).all fun j =>
    let li := ThinMatrixBackend.storedLocate shape hp i
    let rj := ThinMatrixBackend.storedLocate shape hp j
    let left := BinaryBackendExecution.makeLeftBandStored shape a li.1.val
    let right := BinaryBackendExecution.makeRightBandStored shape b rj.1.val
    let ar := left.value.get (finProdFinEquiv (li.2,(0 : Fin 1)))
    let br := right.value.get (finProdFinEquiv ((0 : Fin 1),rj.2))
    (List.finRange 3).all fun r =>
      let copied := ((List.finRange 3).map fun c => BinaryCell.view (ar.get c)*BinaryCell.view (br.get (r-c))).sum
      let reference := ((List.finRange 3).map fun c =>
        BinaryCell.view ((a.get (finProdFinEquiv (i,(0 : Fin 1)))).get c)*
        BinaryCell.view ((b.get (finProdFinEquiv ((0 : Fin 1),j))).get (r-c))).sum
      copied==reference

/-- The complete new program at n=0 has no graph children. This bounded
corner case tests the actual constructed plan and empty block/output arrays. -/
def checkEmptyGraph (h : Nat) : Bool :=
  let f := CompactBlocks.scalarPhysicalPlan 1 (by decide)
  let input : BinaryFoldedFormation.Inputs 0 := ⟨Vector.replicate 0 (Vector.replicate 0 BinaryCell.zero),Vector.replicate 0 (Vector.replicate 0 BinaryCell.zero),Vector.replicate 0 (Vector.replicate 0 BinaryCell.zero)⟩
  let out := GraphFoldedCountCorrect.execute f input h
  out.1.toArray.size==0 && out.2.1.toArray.size==0 && out.2.2.2.value.toArray.size==0 &&
    out.2.2.2.bitSteps==0 && out.2.2.2.control==8

def main : IO Unit := do
  require ((List.range 5).all fun L => checkExtract 9 3 L) "actual normalized coefficient copies, signed values and binary-copy/control budgets"
  require (checkExtract 0 2 0 && checkExtract 7 0 2) "empty requests and singleton cyclic coefficient space"
  require ((List.range 5).all fun S => (List.range 8).all fun M => checkCollection S M) "exhaustive nested binary collection, unmatched children, multiplicity, empty arrays and accumulation charges"
  require ((List.range 2).all fun L => (List.range 8).all fun N => checkIndices L N) "actual stored-shape band enumeration, including no bands and incomplete final bands"
  require ((List.range 5).all fun n => (List.range 5).all fun h => checkReindex n h) "independent original incidence ordering across blocks and all three request windows"
  require ((List.range 2).all fun L => (List.range 6).all fun N => checkBandCopies L N) "actual copied bands versus independent original signed cyclic products, including zero and partial bands"
  require ((List.range 4).all checkEmptyGraph) "complete new finite program with its constructed plan at n=0, h=0..3; no graph children"
  IO.println "PASS: bounded folded-band scheduling suite finished; no full graph or production FFT evaluation."
