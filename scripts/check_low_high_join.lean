import GraphNormalizedBand
open ThinMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def require (b : Bool) (label : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++label))
  IO.println ("PASS: "++label)
  (← IO.getStdout).flush

def encode (z : Int) : BinaryCell.Cell := (BinaryMultiplierAdapter.encodeInteger z).value

def checkNormalization (L M q : Nat) : Bool := Id.run do
  let scale : Int := 4^L
  let low : Vector (Vector BinaryCell.Cell q) M := Vector.ofFn fun i => Vector.ofFn fun r =>
    encode ((i.val:Int)-2*(r.val:Int)-3)
  let high : Vector (Vector BinaryCell.Cell q) M := Vector.ofFn fun i => Vector.ofFn fun r =>
    encode (scale*((r.val:Int)-2*(i.val:Int))-((i.val:Int)-2*(r.val:Int)-3))
  let A := M+2*q+3
  let B := 4^L*(q+2*M)+A
  let out := BinaryLowHighNormalize.table L low high
  let correct := (List.finRange M).all fun i => (List.finRange q).all fun r =>
    let cell := (out.2.value.get i).get r
    BinaryCell.view cell.numerator.value==scale*((r.val:Int)-2*(i.val:Int)) &&
    BinaryCell.view (BinaryLowHighNormalize.output out.2.value i r)==(r.val:Int)-2*(i.val:Int)
  return correct && BinaryCell.view out.1.value==scale && out.1.value.bits.magnitude.length==2*L+1 &&
    decide (out.1.bitSteps+out.2.bitSteps≤L*BackendScalarBits.backendScalarUnit (2*L+3)+
      M*(q*BinaryLowHighNormalize.cellBudget L A B)) &&
    decide (out.1.control+out.2.control≤8*L+1+M*(44*q+40)+8)

def checkFloor (L : Nat) : Bool :=
  (List.range 33).all fun j =>
    let z : Int := (j:Int)-16
    let out := BinaryLowHighNormalize.cell (BinaryLowHighNormalize.power4 L).value (encode (z-7)) (encode 7)
    BinaryCell.view (BinaryLowHighNormalize.cellValue out.value)==z/(4:Int)^L

def normalTable (row col : Nat) : Int :=
  ([[1,0,0,1],[1,0,0,0],[0,1,0,-1],[0,1,0,0],[-1,-1,1,0]].getD row []).getD col 0

def oppositeTable (row col : Nat) : Int :=
  ([[1,1,0],[1,-1,0],[1,1,-1],[1,-1,1],[2,0,0]].getD row []).getD col 0

def polyMul (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map fun k =>
    ((List.range a.length).map fun i => if i≤k then a.getD i 0*b.getD (k-i) 0 else 0).sum

def digit (base code pos : Nat) : Nat := code/base^pos%base

/-- Independent ordinary-label threshold enumeration versus the signed LOW
polynomial functional, for every pair of local letters and every threshold. -/
def checkJoin (k : Nat) : Bool :=
  (List.range (12^k)).all fun code =>
    let n := fun i => digit 12 code i/3
    let o := fun i => digit 12 code i%3
    let full := fun i => ((List.range 5).map fun l => normalTable l (n i)*oppositeTable l (o i)).sum
    let privateTerm := fun i => normalTable 4 (n i)*oppositeTable 4 (o i)
    let pencil := (List.range k).foldl (fun a i => polyMul a [privateTerm i,full i]) [1]
    (List.range (k+1)).all fun t =>
      let low := ((List.range t).map fun d => (-1)^(t-d-1)*((k-d-1).choose (t-d-1):Int)*pencil.getD d 0).sum
      let high := ((List.range (5^k)).map fun labels =>
        if ((List.range k).filter fun i => digit 5 labels i<4).length≥t then
          ((List.range k).map fun i => normalTable (digit 5 labels i) (n i)*oppositeTable (digit 5 labels i) (o i)).prod else 0).sum
      low+high==((List.range k).map full).prod

/-- The bounded cyclic base is elementary; no production FFT evaluation. -/
def elementaryProduct {q : Nat} (a b : Vector BinaryCell.Cell q) : Vector BinaryCell.Cell q × Nat :=
  let rows := Vector.ofFn fun r : Fin q =>
    (List.finRange q).foldl (fun acc j =>
      let p := BinaryCell.mul (a.get j) (b.get (r-j))
      let s := BinaryCell.add acc.value p.value
      (⟨s.value,acc.bitSteps+p.bitSteps+s.bitSteps+4⟩ : BinaryCell.Result BinaryCell.Cell)) ⟨BinaryCell.zero,1⟩
  (rows.map (fun x => x.value),(rows.toList.map (fun x => x.bitSteps)).sum+2*q)

/-- Actual exact-half band source construction, cropped encoder, HIGH table,
physical query, and new normalization; m=0 has no strict LOW channels. The
reference is ordinary stored-matrix cyclic multiplication, not a source sum. -/
def checkBand (L : Nat) : Bool := Id.run do
  let q := 3
  let m := 0
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let plan := ExactHalfSourcePlan.prepare shape
  let B := ThinMatrixBackend.tileWidth L m
  let a : BinaryBandSource.StoredLeftMatrix L m q := Vector.ofFn fun i => Vector.ofFn fun r => encode ((i.val:Int)-2*(r.val:Int)+1)
  let b : BinaryBandSource.StoredRightMatrix L m q := Vector.ofFn fun i => Vector.ofFn fun r => encode (2*(i.val:Int)+(r.val:Int)-3)
  let ca := ExactHalfBandSources.cacheLeft shape a
  let cb := ExactHalfBandSources.cacheRight shape b
  let z : Fin (ExactHalfSourcePlan.J m) := ⟨0,by exact ExactHalfCroppedEmbedding.shifts_nonempty m⟩
  let x := (ExactHalfBandSources.left shape plan.value ca.value z z).value.get 0
  let y := (ExactHalfBandSources.right shape plan.value cb.value z z).value.get 0
  let xe := BinaryCroppedHighEncoder.execute L m 0 q 0 true x
  let ye := BinaryCroppedHighEncoder.execute L m 0 q 0 false y
  let base := BinaryHighTable.guardedBase (L:=L) (m:=m) (t:=0) fun w =>
    let key := ArrayKeys.materialize w.val
    let xr := BinaryHighExecution.readBase xe key
    let yr := BinaryHighExecution.readBase ye key
    let p := elementaryProduct xr.value yr.value
    (p.1,xr.bitSteps+yr.bitSteps+p.2)
  let high := (BinaryHighTable.execute (L:=L) (m:=m) (t:=0) base (2*L+1)).value
  let hp := ThinMatrixBackend.tileWidth_pos L m (by omega)
  let requests : Vector (TilingCosts.Request (2*B) q) 4 := Vector.ofFn fun j =>
    ⟨⟨if j.val==3 then B else if j.val==1 then B-1 else 0,by dsimp [B] at *; split <;> (try split) <;> omega⟩,
     ⟨if j.val==3 then B else B-1,by dsimp [B] at *; split <;> omega⟩,0⟩
  let physical := requests.map fun request => (GraphCompletionRequests.locate shape (by omega) request).value
  let highRows := physical.map fun request => CroppedHighQueries.output (CroppedHighQueries.row 0 0 0 shape request high).value
  let lowRows := Vector.replicate 4 (Vector.replicate q BinaryCell.zero)
  let out := BinaryLowHighNormalize.table L lowRows highRows
  return (List.finRange 4).all fun i => (List.finRange q).all fun r =>
    let req := requests.get i
    let reference := if hreq : req.row.val<B ∧ req.column.val<B then
      ((List.finRange q).map fun j =>
        BinaryCell.view ((a.get ⟨req.row.val,by simpa only [B,m,Nat.pow_zero,Nat.mul_one] using hreq.1⟩).get j)*
          BinaryCell.view ((b.get ⟨req.column.val,by simpa only [B,m,Nat.pow_zero,Nat.one_mul] using hreq.2⟩).get (r-j))).sum else 0
    BinaryCell.view ((highRows.get i).get r)==(4:Int)^L*reference &&
    BinaryCell.view (BinaryLowHighNormalize.output out.2.value i r)==reference

def main : IO Unit := do
  require ((List.range 13).all fun L => checkNormalization L 5 3) "binary divisor, retained numerators, signed exact quotients and arithmetic/control budgets, L=0..12"
  require (checkNormalization 128 3 3) "257-bit divisor and signed cancellation without integer reconversion"
  require (checkNormalization 0 0 3 && checkNormalization 5 4 0) "empty request and cyclic arrays retain and charge shared divisor construction"
  require ((List.range 5).all checkFloor) "signed Euclidean quotient including nondivisible inputs"
  require (checkJoin 0 && checkJoin 1 && checkJoin 2) "independent LOW plus ordinary-threshold HIGH identity for all local letters and thresholds, k=0..2"
  require (checkBand 0 && checkBand 1) "actual exact-half band sources through normalized physical queries, m=0, L=0..1; signed cyclic products, duplicate and rejected requests"
  IO.println "PASS: bounded LOW/HIGH join suite finished; no full graph or production FFT evaluation."
