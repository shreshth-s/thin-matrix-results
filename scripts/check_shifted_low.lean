import GraphShiftedLow
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

def directLow (L m t q maskN maskO label residue : Nat) : Int :=
  let left := allowedWords L m maskN maskO label
  let right := allowedWords L m maskO maskN label
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
    x.2.2*y.2.2*weighted*cyclic).sum).sum

/-- Execute root generation, every window, forms, completion, all channels,
full products, shifted weights and retained sums. No graph-wide evaluator. -/
def checkLow (L m t q : Nat) [NeZero q] : Bool := Id.run do
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let keys := ResidualFamilyKeys.prepare shape.layout t
  let raw := rawFixture L q 7
  match keys.value.masks.toList with
  | a::_ =>
    let b := keys.value.masks.toList.getLast?.getD a
    let labels := #v[requestLabels (2*(L-m)) 0,requestLabels (2*(L-m)) 3,
      requestLabels (2*(L-m)) 0,requestLabels (2*(L-m)) 0]
    let complete := fun (ch : ResidualFamilyKeys.Channel m) (a b : ResidualFamilyKeys.Mask L m) =>
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
      let out := RetainedWindowCompletion.execute prefixes (permuted.map RetainedWindowPermutation.Prepared.layout) labels
      GroupedPreparation.ofStoredFn out.value.sums.value fun j =>
        (RootRequestSelection.selectRow (decide (j.val<3)) (out.value.sums.value.get j).output).value
    let child := fun c =>
      let ch := keys.value.channels.get c
      let products := PairedRootRows.execute (complete ch a b) (complete (ResidualChannelTranspose.swap ch) b a)
      WeightedRootProducts.prepare (2*m) t (ch.toList.count true) products.value.products.value
    let out := RootProductCollection.execute keys.value.channels child fun v j => (v.outputs.value.get j).sum.value
    for j in List.finRange 4 do
      let label := if j.val==1 then 3 else 0
      for r in List.finRange q do
        let expected := if j.val<3 then directLow L m t q (codeOf a.bits) (codeOf b.bits) label r.val else 0
        if BinaryCell.view ((RootProductCollection.output out.value j).get r) != expected then return false
    return true
  | _ => false

def main : IO Unit := do
  require (checkLow 0 0 0 1 && checkLow 0 0 1 1) "empty channel list, zero physical/residual dimensions and threshold one"
  require (checkLow 1 0 1 3) "nonempty ordinary residual, opposite forms and every cyclic residue; m=0"
  require (checkLow 1 1 2 3) "shifted private p1 baseline and weighted degree-one functional; m=1"
  require (checkLow 2 1 2 3) "distinct physical masks, retained windows/forms and shifted LOW; L=2,m=1"
  require (checkLow 2 2 3 3) "joint strict channels, nonzero rare letters, full product degrees and cyclic residues; m=2"
  IO.println "PASS: bounded shifted-LOW suite finished; duplicate and rejected requests retained in every case."
