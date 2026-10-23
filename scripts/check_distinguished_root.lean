import ExactHalfResidualWindow
open ThinMatrix ThinMatrix.WalshEmbedding ThinMatrix.DistinguishedResidualRoot
open ThinMatrix.DistinguishedResidualSupport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def refNormal (a : Nat) : NormalLetter := if a=0 then .x1 else if a=1 then .x2 else if a=2 then .p1 else .p2

def refOpposite (a : Nat) : OppositeLetter := if a=0 then .s else if a=1 then .v else .w

def nCode : NormalLetter → Nat | .x1 => 0 | .x2 => 1 | .p1 => 2 | .p2 => 3
def oCode : OppositeLetter → Nat | .s => 0 | .v => 1 | .w => 2

def refNFactor (channel : Bool) (z : Int) (a : Nat) : Int :=
  if channel then (if a=3 then 1 else 0) else if a<2 then -1 else if a=2 then 1+z else 0

def refOFactor (channel : Bool) (a : Nat) : Int :=
  if channel then (if a=2 then 1 else 0) else if a=0 then 2 else 0

def fixtureSource (L col : Nat) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : Int :=
  let a := ((List.finRange L).map fun i => (i.val+1)*(nCode (n i)+1)).sum
  let b := ((List.finRange L).map fun i => (i.val+2)*(oCode (o i)+1)).sum
  ((a*b+a*col+3*b+col^2)%23 : Nat)-11

def refCrop (L cap col : Nat) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : Int :=
  if ((List.finRange L).filter fun i => n i==.p2).length≤cap &&
     ((List.finRange L).filter fun i => o i==.w).length≤cap then fixtureSource L col n o else 0

def checkRoot (m k cnCode coCode cap : Nat) (z : Int) : Bool := Id.run do
  let cn : Cube m := fun i => cnCode/2^i.val%2==1
  let co : Cube m := fun i => coCode/2^i.val%2==1
  let eN : Layout (m+k) m k := finSumFinEquiv.symm
  let eO : Layout (m+k) m k := Fin.revPerm.trans eN
  let cnSize := ((List.finRange m).filter cn).length
  let coSize := ((List.finRange m).filter co).length
  -- B=2, q=3, F=2: every column, including repeated request incidences.
  let requests := [0,1,1]
  return (List.range (3^(2*k))).all fun index =>
    let wn : CroppedGroupedSuffix.Word k := fun i => ⟨index/3^i.val%3,Nat.mod_lt _ (by decide)⟩
    let wo : CroppedGroupedSuffix.Word k := fun i => ⟨index/3^(k+i.val)%3,Nat.mod_lt _ (by decide)⟩
    let rn := ((List.finRange k).filter fun i => wn i==2).length
    let ro := ((List.finRange k).filter fun i => wo i==2).length
    (requests.all fun request => (List.range 12).all fun col =>
      let read := fun n => refCrop (m+k) cap (col+request)
        (assemble eN n (fun i => normalRemaining (wn i)))
        (assemble eO (fun i => oppositeLetter (co i)) (fun i => refOpposite (wo i).val))
      let out := evaluate m cn z read
      let scale := ((List.finRange m).map fun i => if co i then (1 : Int) else 2).prod
      let actual := scale*out.value
      let reference := ((List.range (4^m)).map fun nc =>
        ((List.range (3^m)).map fun oc =>
          let n : Fin m → NormalLetter := fun i => refNormal (nc/4^i.val%4)
          let o : Fin m → OppositeLetter := fun i => refOpposite (oc/3^i.val%3)
          let factor := ((List.finRange m).map fun i =>
            refNFactor (cn i) z (nc/4^i.val%4)*refOFactor (co i) (oc/3^i.val%3)).prod
          factor*refCrop (m+k) cap (col+request)
            (assemble eN n (fun i => refNormal (if wn i=2 then 3 else (wn i).val)))
            (assemble eO o (fun i => refOpposite (wo i).val))).sum).sum
      actual==reference && decide (out.lookups≤3^m) && decide (2*out.ringOps≤5*(3^m-1)) &&
        (if cap<cnSize+rn || cap<coSize+ro then actual==0 else true))

/-- The dense comparison includes independent letter encodings, swapped
physical layouts, all remaining ternary words, all retained coefficient
columns, duplicate requests, zero roots, and channel-count ties. It tests
scalar evaluation only; no binary root-array or FFT execution is claimed. -/
def rootChecks : Bool :=
  ([(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)].all fun mk =>
    (List.range (2^mk.1)).all fun cn => (List.range (2^mk.1)).all fun co =>
      (List.range (mk.1+2)).all fun cap =>
        [-2,-1,0,1,2].all fun z => checkRoot mk.1 mk.2 cn co cap z)

#eval do
  if !rootChecks then throw (IO.userError "distinguished root fixture failed")
  IO.println "PASS: sparse shifted residual roots equal independent dense contractions; rare caps, all 12 coefficient columns, duplicated requests, asymmetric layouts and zero dimensions."
