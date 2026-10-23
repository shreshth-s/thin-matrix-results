import GraphWindowPermutations
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

/-- Independent dense product of the explicit 3 by 3 forward matrix. -/
def matrixEntry (out input : Nat) : Int :=
  if out==0 then (if input<2 then 1 else 0)
  else if out==1 then (if input==0 then 1 else if input==1 then -1 else 0)
  else if input==2 then -1 else 0

def denseForward (k : Nat) (get : Nat → Nat → Int) (word col : Nat) : Int :=
  ((List.range (3^k)).map fun code =>
    let factor := ((List.range k).map fun i => matrixEntry (digit 3 word (k+i)) (digit 3 code i)).prod
    factor*get (word%(3^k)+(3^k)*code) col).sum

def forwardPosition (k ell : Nat) (normal : Bool) (slot j : Nat) : Nat :=
  if j<k then (if normal then k+j else j)
  else (if normal then 0 else k)+(j-k+slot+ell)%k

def oldCode (k ell : Nat) (normal : Bool) (slot word : Nat) : Nat :=
  ((List.range (2*k)).map fun j => digit 3 word j*3^(forwardPosition k ell normal slot j)).sum

/-- Input values are supplied only to the independent reference, never to an
intermediate binary operation. Check every retained coefficient and layer. -/
def checkStored {k C : Nat} (X : BinaryWindowPartition.Source k C) (get : Nat → Nat → Int)
    (A ell cap cn co : Nat) : Bool := Id.run do
  let len := min ell k
  let normal := decide (co≤cn)
  let partition := RetainedRootWindows.partition len cap cn co X
  for slot in List.finRange (RetainedRootWindows.slots k) do
    let transformed := RetainedOppositeTransform.execute (partition.value.components.get slot)
    if transformed.bitSteps>RetainedOppositeTransform.bitBudget (2*k) C k A ||
        transformed.control>RetainedOppositeTransform.controlBudget (2*k) C k+8*k+8 ||
        transformed.value.layers.length != k then return false
    if (transformed.value.layers.map fun layer => (layer.toList.map fun row => row.toArray.size).sum).sum != k*3^(2*k)*C then return false
    let out := RetainedWindowPermutation.prepare ell normal slot transformed.value.result
    if out.bitSteps>RetainedWindowPermutation.bitBudget (2*k) C (2^k*A) ||
        out.control>128*(2*k)+40+RetainedWindowPermutation.controlBudget (2*k) C then return false
    for i in List.finRange (2*k) do
      if (out.value.layout.forward.get i).val != forwardPosition k len normal slot.val i.val then return false
      if out.value.layout.forward.get (out.value.layout.backward.get i) != i then return false
    let ref := fun word col => if refOwner k len cap cn co word==some slot.val then get word col else 0
    for word in List.finRange (3^(2*k)) do
      let old := oldCode k len normal slot.val word.val
      let suffixRare := ((List.range len).filter fun j => digit 3 word.val (2*k-len+j)==2).length
      for col in List.finRange C do
        let tv := BinaryCell.view ((transformed.value.result.get word).get col)
        let actual := BinaryCell.view ((out.value.coefficients.get word).get col)
        if tv != denseForward k ref word.val col.val || actual != denseForward k ref old col.val ||
            actual.natAbs>2^k*A then return false
        if (cap-max cn co)*len/k<suffixRare && actual != 0 then return false
  return true

def checkSynthetic (k C A ell cap cn co : Nat) : Bool :=
  let get := fun word col => signedValue A (word+[0,1,1].getD (col/3) 0+2*(col%3))
  let X : BinaryWindowPartition.Source k C := Vector.ofFn fun word => Vector.ofFn fun col =>
    (BinaryMultiplierAdapter.encodeInteger (get word.val col.val)).value
  checkStored X get A ell cap cn co

def checkRoot (L m C A : Nat) : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let keys := ResidualFamilyKeys.prepare shape.layout 2
  let raw := rawFixture L C A
  match keys.value.masks.toList with
  | [] => return false
  | a::_ =>
    for c in keys.value.channels.toList do
      let e := (RetainedResidualFamily.produce raw a a c).value
      let source := ResidualWindowSource.execute e
      let cn := (ResidualFamilyKeys.normal c).toList.count true
      let co := (ResidualFamilyKeys.opposite c).toList.count true
      let get := fun word col => reference L (codeOf a.bits) (codeOf a.bits)
        (codeOf (ResidualFamilyKeys.normal c)) (codeOf (ResidualFamilyKeys.opposite c))
        (m/2) A word (col/C) (col%C)
      if !checkStored source.value get (2^m*(4^m*A)) 1 (m/2) cn co then return false
    return true

def checkContainer : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime 1 0
  let keys := ResidualFamilyKeys.prepare shape.layout 1
  let raw := rawFixture 1 3 7
  let sources : ExactHalfBandSources.Families 1 0 3 :=
    Vector.replicate 1 (Vector.replicate 1 (Vector.replicate 1 raw,Vector.replicate 1 raw))
  let roots := GraphResidualFamilies.execute keys.value sources
  let windows := GraphRootWindows.execute 1 roots.value
  let transformed := GraphWindowTransforms.execute windows.value
  let permuted := GraphWindowPermutations.execute 1 windows.value transformed.value
  let G := keys.value.masks.toArray.size
  return transformed.bitSteps≤GraphWindowTransforms.bitBudget 1 0 3 1 G 7 &&
    transformed.control≤GraphWindowTransforms.controlBudget 1 0 3 1 G &&
    permuted.bitSteps≤GraphWindowPermutations.bitBudget 1 0 3 1 G 14 &&
    permuted.control≤GraphWindowPermutations.controlBudget 1 0 3 1 G &&
    GraphWindowPermutations.coefficientCells permuted.value==2*G^2*9*3

def require (b : Bool) (s : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++s))
  IO.println ("PASS: "++s)
  (← IO.getStdout).flush

def main : IO Unit := do
  for k in [0,1,2] do
    for ell in [0,1,k,k+1] do
      require (([(0,0),(1,0),(0,1),(1,1)] : List (Nat×Nat)).all fun pair =>
        checkSynthetic k 3 7 ell 1 pair.1 pair.2)
        s!"independent dense forward matrix and coordinate permutation: k={k}, ell={ell}, both sides and ties"
  require (checkSynthetic 1 9 65536 1 2 0 1 && checkSynthetic 0 0 0 4 0 0 0)
    "repeated request columns, 65536 bit boundary and empty coefficients"
  require (checkRoot 2 2 3 7 && checkRoot 1 0 3 7)
    "complete retained roots to transformed/permuted windows, zero residual and empty distinguished masks"
  require (checkRoot 3 2 3 7)
    "independent physical-root tensor reference with nonzero rare budget at L=3,m=2"
  require checkContainer "both input families and aggregate retained-array counters at m=0"
  IO.println "PASS: bounded window-transform suite completed; no expensive graph-source or FFT runtime attempt was rerun."
