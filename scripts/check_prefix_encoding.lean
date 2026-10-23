import GraphPrefixTensor
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
def checkOldStored {k C : Nat} (X : BinaryWindowPartition.Source k C) (get : Nat → Nat → Int)
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
  checkOldStored X get A ell cap cn co


/-- Independent explicit ordinary four-by-three matrix. -/
def ordinaryEntry (q a : Nat) : Int :=
  if q==0 then (if a==0 || a==2 then 1 else 0)
  else if q==1 then (if a==0 then 1 else 0)
  else if q==2 then (if a==1 then 1 else if a==2 then -1 else 0)
  else if a==1 then 1 else 0

def labelAt (q i : Nat) : Fin 4 := ⟨digit 4 q i, Nat.mod_lt _ (by decide)⟩
def wordAt (w i : Nat) : Fin 3 := ⟨digit 3 w i, Nat.mod_lt _ (by decide)⟩

/-- All actual stored outputs, against an independent dense tensor sum. -/
def checkPrefix {P ell C : Nat} (X : RetainedCappedGroups.Source P ell C)
    (get : Nat → Nat → Int) (r A : Nat) : Bool := Id.run do
  let out := CappedPrefixProgram.execute r X
  if out.bitSteps>CappedPrefixProgram.bitBudget P ell r C A ||
      out.control>CappedPrefixProgram.controlBudget P ell r C then return false
  if CappedPrefixProgram.traceCells out.value>(P+1)*4^P*(2^ell*CappedSubsetList.count ell r)*C then return false
  if RetainedCappedGroups.cells out.value.grouped != 2^ell*CappedSubsetList.count ell r*3^P*C then return false
  for pair in List.finRange (2^ell) do
    let bits := (out.value.grouped.pairs.get pair)
    for key in List.finRange (CappedSubsetList.count ell r) do
      let support := (out.value.grouped.keys.get key)
      let suffix := ((List.finRange ell).map fun i =>
        (if support.get i then 2 else if bits.get i then 1 else 0)*3^i.val).sum
      let minus := ((List.finRange ell).filter fun i => support.get i && bits.get i).length
      for q in List.range (4^P) do
        for c in List.finRange C do
          let actual := BinaryCell.view (RetainedPrefixEncoder.output ((out.value.traces.get pair).get key) (fun i => labelAt q i.val) c)
          let expected := ((List.range (3^P)).map fun w =>
            (-1)^minus*get (w+3^P*suffix) c.val*
              ((List.range P).map fun i => ordinaryEntry (digit 4 q i) (digit 3 w i)).prod).sum
          if actual != expected || actual.natAbs>2^P*A then return false
    for active in List.range (2^ell) do
      for q in List.range (4^P) do
        for c in List.finRange C do
          let actual := ((List.finRange (CappedSubsetList.count ell r)).map fun j =>
            if (List.finRange ell).all (fun i => !(out.value.grouped.keys.get j).get i || digit 2 active i.val==1)
            then BinaryCell.view (RetainedPrefixEncoder.output ((out.value.traces.get pair).get j) (fun i => labelAt q i.val) c) else 0).sum
          let expected := ((List.range (3^(P+ell))).map fun w =>
            if ((List.range ell).filter fun i => digit 3 w (P+i)==2).length≤r then
              get w c.val*((List.range P).map fun i => ordinaryEntry (digit 4 q i) (digit 3 w i)).prod*
                ((List.finRange ell).map fun i =>
                  let label := (if bits.get i then 2 else 0)+(if digit 2 active i.val==1 then 0 else 1)
                  ordinaryEntry label (digit 3 w (P+i.val))).prod else 0).sum
          if actual != expected then return false
  return true

def checkPrefixSynthetic (P ell C r A : Nat) : Bool :=
  let get := fun word col => signedValue A (word+[0,1,1].getD col 0)
  let X : RetainedCappedGroups.Source P ell C := Vector.ofFn fun w => Vector.ofFn fun c =>
    (BinaryMultiplierAdapter.encodeInteger (get w.val c.val)).value
  checkPrefix X get r A

/-- Actual retained roots/windows/transform/permutation feed the new encoder;
the independent reference starts at the original physical coefficient array. -/
def checkStored {k C : Nat} (X : BinaryWindowPartition.Source k C) (get : Nat → Nat → Int)
    (A ell cap cn co : Nat) : Bool := Id.run do
  let len := min ell k
  let partition := RetainedRootWindows.partition len cap cn co X
  for slot in List.finRange (RetainedRootWindows.slots k) do
    let transformed := RetainedOppositeTransform.execute (partition.value.components.get slot)
    let permuted := RetainedWindowPermutation.prepare len (decide (co≤cn)) slot transformed.value.result
    let encoded := WindowPrefixProgram.execute ell cap cn co permuted.value.coefficients
    if encoded.bitSteps>WindowPrefixProgram.bitBudget k ell cap cn co C (2^k*A) ||
        encoded.control>WindowPrefixProgram.controlBudget k ell cap cn co C then return false
    let ref := fun word col => if refOwner k len cap cn co word==some slot.val then get word col else 0
    let refPermuted := fun word col => denseForward k ref (oldCode k len (decide (co≤cn)) slot.val word) col
    if !checkPrefix (WindowPrefixProgram.reshape ell permuted.value.coefficients) refPermuted
        ((cap-max cn co)*len/k) (2^k*A) then return false
  return true

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
  let encoded := GraphPrefixProgram.execute 1 windows.value permuted.value
  let G := keys.value.masks.toArray.size
  return encoded.bitSteps≤GraphPrefixProgram.bitBudget 1 windows.value 14 &&
    encoded.control≤GraphPrefixProgram.controlBudget 1 windows.value &&
    transformed.bitSteps≤GraphWindowTransforms.bitBudget 1 0 3 1 G 7 &&
    transformed.control≤GraphWindowTransforms.controlBudget 1 0 3 1 G &&
    permuted.bitSteps≤GraphWindowPermutations.bitBudget 1 0 3 1 G 14 &&
    permuted.control≤GraphWindowPermutations.controlBudget 1 0 3 1 G &&
    GraphWindowPermutations.coefficientCells permuted.value==2*G^2*9*3

def require (b : Bool) (s : String) : IO Unit := do
  if !b then throw (IO.userError ("FAIL: "++s))
  IO.println ("PASS: "++s)
  (← IO.getStdout).flush


def main : IO Unit := do
  for P in [0,1,2,3] do
    for ell in [0,1,2] do
      require ((List.range (ell+2)).all fun r => checkPrefixSynthetic P ell 3 r 7)
        s!"all capped groups, all prefix labels and all suffix queries: P={P}, ell={ell}"
  require (checkPrefixSynthetic 2 2 3 1 65536 && checkPrefixSynthetic 0 0 0 0 0)
    "65536 bit boundary, duplicate columns, zero dimensions and empty coefficients"
  require (checkRoot 2 2 3 7 && checkRoot 1 0 3 7)
    "actual retained root/window/permutation/prefix pipeline with zero residual and empty distinguished masks"
  require (checkRoot 3 2 3 7)
    "actual capped prefix arrays versus independent physical-root tensor at L=3,m=2"
  require checkContainer "both-input graph-family container and input-dependent prefix budgets at m=0"
  IO.println "PASS: bounded prefix-encoding suite completed; no expensive graph-source or FFT runtime attempt was rerun."
