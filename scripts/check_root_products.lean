import GraphRootFamilyProducts
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

def coeff (a : Block F q) (d r : Nat) : Int :=
  if hd : d<F then if hr : r<q then BinaryCell.view ((a.get ⟨d,hd⟩).get ⟨r,hr⟩) else 0 else 0

/-- Independent integer convolution, testing the cyclic equation directly. -/
def referenceProduct (F q : Nat) (a b : Nat → Nat → Int) (degree residue : Nat) : Int :=
  ((List.range F).map fun d => ((List.range F).map fun e =>
    if d+e==degree then ((List.range q).map fun r => ((List.range q).map fun s =>
      if (r+s)%q==residue then a d r*b e s else 0).sum).sum else 0).sum).sum

def checkProducts (F q A : Nat) [NeZero q] : Bool := Id.run do
  let a : Block F q := Vector.ofFn fun d => Vector.ofFn fun r =>
    (BinaryMultiplierAdapter.encodeInteger (signedValue A (d.val+2*r.val))).value
  let b : Block F q := Vector.ofFn fun d => Vector.ofFn fun r =>
    (BinaryMultiplierAdapter.encodeInteger (signedValue A (2*d.val+r.val+1))).value
  let out := CompletedRootProducts.execute a b
  if out.bitSteps>CompletedRootProducts.bitBudget F q A || out.control>CompletedRootProducts.controlBudget F q then return false
  for d in List.finRange (CompletedRootProducts.outputLength F) do
    for r in List.finRange q do
      let expected := referenceProduct F q (coeff a) (coeff b) d.val r.val
      if cellView out.value d r != expected || expected.natAbs>CompletedRootProducts.magnitude F q A then return false
  return true

def weightReference (k t d : Nat) : Int := (-1)^(t-d-1)*((k-d-1).choose (t-d-1):Int)

def checkWeighted (F q k t card A : Nat) : Bool := Id.run do
  let product : Block F q := Vector.ofFn fun d => Vector.ofFn fun r =>
    (BinaryMultiplierAdapter.encodeInteger (signedValue A (d.val+r.val))).value
  let out := WeightedRootProducts.prepare k t card #v[product,product]
  if out.bitSteps>t*WeightedRootProducts.weightBudget k t+2*WeightedRootProducts.bitBudget t q (2^k) A ||
      out.control>t*(WeightedRootProducts.weightBudget k t+48)+8+3*t+4+(2*(WeightedRootProducts.controlBudget t q+32)+8)+8 then return false
  for j in List.finRange 2 do
    for r in List.finRange q do
      let expected := ((List.range t).map fun d =>
        if card≤d then weightReference k t d*coeff product (d-card) r.val else 0).sum
      if BinaryCell.view (((out.value.outputs.value.get j).sum.value).get r) != expected then return false
  return true

def checkTranspose (m t : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime (m+1) m
  let keys := (ResidualFamilyKeys.prepare shape.layout t).value.channels
  let out := ResidualChannelTranspose.prepare keys
  if out.bitSteps != 0 || out.control>keys.toArray.size*(ResidualChannelTranspose.budget m keys.toArray.size+32)+8 then return false
  for i in List.finRange (ResidualFamilyKeys.channelCount m t) do
    let j := out.value.get i
    let a := keys.get i
    let b := keys.get j
    if (out.value.get j).val != i.val || a.toList.count true != b.toList.count true then return false
    if (ResidualFamilyKeys.normal b).toList != (ResidualFamilyKeys.opposite a).toList ||
        (ResidualFamilyKeys.opposite b).toList != (ResidualFamilyKeys.normal a).toList then return false
  return true

def checkCollection (S M q : Nat) : Bool := Id.run do
  let shapes := Vector.replicate S ()
  let children := fun (j : Fin S) =>
    let rows : Vector (Vector BinaryCell.Cell q) M := Vector.ofFn fun i => Vector.ofFn fun r =>
      (BinaryMultiplierAdapter.encodeInteger (signedValue 7 (j.val+[0,0,1].getD i.val 1+r.val))).value
    (⟨rows,0,3*(M+q)+4⟩ : BinaryGroupedCoordinates.Run _)
  let out := RootProductCollection.execute shapes children (fun rows i => rows.get i)
  if out.bitSteps>RootProductCollection.bitBudget (fun _ : Fin S => 0) M q 7 ||
      out.control>RootProductCollection.controlBudget (fun _ : Fin S => 3*(M+q)+4) M q then return false
  for i in List.finRange M do
    for r in List.finRange q do
      let expected := ((List.range S).map fun j => signedValue 7 (j+[0,0,1].getD i.val 1+r.val)).sum
      if BinaryCell.view ((RootProductCollection.output out.value i).get r) != expected then return false
  return true

/-- Execute the actual two-root residual/window/transform/prefix/completion
path for a small physical root. Its reference sums physical letters directly. -/
def checkPhysicalPair : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime 3 2
  let keys := ResidualFamilyKeys.prepare shape.layout 3
  let raw := rawFixture 3 3 7
  match keys.value.masks.toList with
  | a::b::_ =>
    let c : ResidualFamilyKeys.Channel 2 := #v[true,false,false,true]
    let cR := ResidualChannelTranspose.swap c
    let left := (RetainedResidualFamily.produce raw a b c).value
    let right := (RetainedResidualFamily.produce raw b a cR).value
    let labels := ((List.range 16).map (requestLabels 2)).toArray++#[requestLabels 2 0,requestLabels 2 0]
    let labelVector : Vector _ labels.size := ⟨labels,rfl⟩
    let complete := fun (root : RetainedResidualFamily.Entry 3 2 3) (ch : ResidualFamilyKeys.Channel 2) =>
      let X := (ResidualWindowSource.execute root).value
      let cn := (ResidualFamilyKeys.normal ch).toList.count true
      let co := (ResidualFamilyKeys.opposite ch).toList.count true
      let partition := RetainedRootWindows.partition 1 1 cn co X
      let permuted := GroupedPreparation.ofStoredFn partition.value.components fun slot =>
        let forward := RetainedOppositeTransform.execute (partition.value.components.get slot)
        (RetainedWindowPermutation.prepare 1 (decide (co≤cn)) slot forward.value.result).value
      let prefixes := GroupedPreparation.ofStoredFn permuted fun slot =>
        (WindowPrefixProgram.execute 1 1 cn co (permuted.get slot).coefficients).value
      let out := RetainedWindowCompletion.execute prefixes (permuted.map RetainedWindowPermutation.Prepared.layout) labelVector
      GroupedPreparation.ofStoredFn out.value.sums.value fun j =>
        (RootRequestSelection.selectRow (decide (j.val+1<labels.size)) (out.value.sums.value.get j).output).value
    let arows := complete left c
    let brows := complete right cR
    let products := PairedRootRows.execute arows brows
    let weighted := WeightedRootProducts.prepare 4 3 2 products.value.products.value
    let ref := fun (mn mo : ResidualFamilyKeys.Mask 3 2) (ch : ResidualFamilyKeys.Channel 2) (code d r : Nat) =>
      ((List.range 9).map fun w => reference 3 (codeOf mn.bits) (codeOf mo.bits)
        (codeOf (ResidualFamilyKeys.normal ch)) (codeOf (ResidualFamilyKeys.opposite ch)) 1 7 w d r*
        ordinaryEntry (digit 4 code 0) (digit 3 w 0)*oppositeOrdinary (digit 4 code 1) (digit 3 w 1)).sum
    for j in List.finRange labels.size do
      let code := if j.val<16 then j.val else 0
      let expected := fun d r => if j.val+1<labels.size then referenceProduct 3 3 (ref a b c code) (ref b a cR code) d r else 0
      for d in List.finRange 5 do
        for r in List.finRange 3 do
          if cellView (products.value.products.value.get j) d r != expected d.val r.val then return false
      for r in List.finRange 3 do
        let answer := ((List.range 3).map fun d => if 2≤d then weightReference 4 3 d*expected (d-2) r.val else 0).sum
        if BinaryCell.view (((weighted.value.outputs.value.get j).sum.value).get r) != answer then return false
    return true
  | _ => false

def main : IO Unit := do
  require (checkProducts 0 3 7) "zero formal dimension and empty product"
  require (checkProducts 1 1 7 && checkProducts 3 1 7) "full formal product with one cyclic residue"
  require (checkProducts 2 3 7 && checkProducts 3 3 7) "full degree/cyclic convolution against independent dense reference"
  require (checkProducts 2 3 65536) "signed width boundary 65536; product budgets"
  for k in [0,2,4] do
    require (((List.range (k+3)).all fun t => (List.range (k+4)).all fun card => checkWeighted 5 3 k t card 7)) s!"actual binomial weights and all shifts including zero tails; k={k}"
  require (checkWeighted 0 3 4 3 0 7 && checkWeighted 3 0 4 3 0 7) "empty weighted degree and cyclic arrays"
  for m in [0,1,2] do
    require (((List.range (2*m+3)).all fun t => checkTranspose m t)) s!"strict retained-channel transpose and involution; m={m}"
  require (checkCollection 3 3 3 && checkCollection 0 3 3 && checkCollection 3 0 3 && checkCollection 3 3 0) "retained collection sums, duplicate requests, empty children/requests/columns and budgets"
  require checkPhysicalPair "actual L=3,m=2 paired roots with swapped masks/channel halves; all 16 forms, duplicate/unmatched requests, 5 degrees and 3 cyclic residues; independent physical tensor reference"
  IO.println "PASS: bounded root-products suite finished; no full graph or production FFT attempt."
