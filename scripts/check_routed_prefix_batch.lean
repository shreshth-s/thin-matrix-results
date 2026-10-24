import RoutedPrefixBatch
open ThinMatrix RecursiveTable
open scoped BigOperators

private def smallBase : RetainedEqualCopy.Base 9 1 (prod (fin 2) (fin 2))
    (prod (fin 2) (fin 2)) (prod (fin 2) (fin 2)) ℚ :=
  ⟨store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val/4 && p.2.2.2.val == (p.1.val/2)%2 then 1/2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == (p.1.val/2)%2 && p.2.2.2.val == p.1.val%2 then -2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val%2 && p.2.2.2.val == p.1.val/4 then -1 else 0)⟩

private def scheme : RectangularBatch.Scheme :=
  ⟨2,2,2,1,1,1,9,1,by decide,by decide,by decide,by decide,rfl,rfl,smallBase⟩

private def digit (base code position : Nat) : Nat := code/base^position%base

private def labels (n code : Nat) : Vector (Fin 4) n :=
  Vector.ofFn (fun i => ⟨digit 4 code i.val,Nat.mod_lt _ (by decide)⟩)

private def sourceValue (seed : Int) (block word col : Nat) : Int :=
  let magnitude := seed+(block:Int)*5+(col:Int)*3
  if word%3=0 then magnitude else if word%3=1 then -magnitude else 0

private def entry (q a : Nat) : Int :=
  if q=0 then (if a=0 || a=2 then 1 else 0)
  else if q=1 then (if a=0 then 1 else 0)
  else if q=2 then (if a=1 then 1 else if a=2 then -1 else 0)
  else if a=1 then 1 else 0

private def reference (P ell r : Nat) (seed : Int) (block col : Nat)
    (request : Vector (Fin 4) (P+ell)) : Int :=
  ((List.range (3^(P+ell))).map (fun w =>
    if ((List.range ell).filter (fun j => digit 3 w (P+j)=2)).length≤r then
      sourceValue seed block w col *
        ((List.finRange (P+ell)).map (fun i => entry (request.get i).val (digit 3 w i.val))).prod
    else 0)).sum

private def check (P ell r B C A Z : Nat) (seed : Int) (noRequests : Bool) : IO Nat := do
  let D := CappedSubsetList.count ell r
  if hD : 0<D then
    if hA : 0<A then
      if hZ : 0<Z then
        if hf : (A-1)^scheme.den≤D^scheme.num then
          if hl : Z≤D^scheme.z then
            let source : Vector (RetainedCappedGroups.Source P ell C) B := Vector.ofFn (fun b =>
              Vector.ofFn (fun w => Vector.ofFn (fun c =>
                (BinaryMultiplierAdapter.encodeInteger (sourceValue seed b.val w.val c.val)).value)))
            let xs := source.map (fun x => (CappedPrefixProgram.execute r x).value)
            let requests := if noRequests then #[] else
              ((List.range (4^(P+ell))).map (labels (P+ell))).toArray++#[labels (P+ell) 0,labels (P+ell) 0]
            let prepared := RoutedPrefixBatch.prepare xs requests
            let routing := PrefixRequestRouting.run requests
            let routeBudget := 12*2^(P+(P+ell))+requests.size*(16*(P+(P+ell)+1)^2+64*(P+ell+1)+36)+20
            unless routing.bitSteps=0 && routing.control≤routeBudget do
              throw (IO.userError "Routing exceeds its proved counters")
            unless BooleanRequestRouter.items routing.value=requests.size do
              throw (IO.userError "Routing lost or repeated an occurrence")
            let mut seen := Array.replicate requests.size 0
            let mut checked := 0
            for pair in List.finRange (2^ell) do
              for q in List.range (4^P) do
                let digits := labels P q
                let out := RoutedPrefixBatch.group scheme hD hA hZ hf hl requests prepared.value pair digits
                let expectedIds := (List.finRange requests.size).filter (fun i =>
                  (List.finRange P).all (fun j => (requests[i.val].get ⟨j.val,by omega⟩).val=digit 4 q j.val) &&
                  (List.finRange ell).all (fun j =>
                    ((requests[i.val].get ⟨P+j.val,by omega⟩).val≥2)=((prepared.value.pairs.get pair).get j=true)))
                unless out.value.indices=expectedIds do
                  throw (IO.userError "Original request indices or stable group order differ")
                unless out.value.output.size=out.value.indices.length do
                  throw (IO.userError "Group output size differs from routed occurrence count")
                let H := 2^P*(seed.natAbs+B*5+C*3+1)
                let budget := CompactBlocks.blockCount out.value.indices.length A*
                  CompactBlocks.blockCount (B*C) Z*RectangularBatch.scalarBudget scheme D H
                unless out.bitSteps≤budget do throw (IO.userError "Routed block batch exceeds scalar budget")
                for j in List.finRange out.value.indices.length do
                  let original := out.value.indices[j.val]
                  seen := seen.modify original.val (·+1)
                  for b in List.finRange B do
                    for c in List.finRange C do
                      let actual := ((out.value.output[j.val]?).getD (Vector.replicate (B*C) BinaryCell.zero)).get
                        (PrefixBlockBatch.column b c)
                      unless BinaryCell.view actual=reference P ell r seed b.val c.val requests[original.val] do
                        throw (IO.userError "Routed block result differs from independent raw tensor")
                      let old := PrefixCompletionProgram.row (xs.get b) (prepared.value.banks.get b) requests[original.val]
                      unless BinaryCell.view actual=BinaryCell.view (old.value.output.get c) do
                        throw (IO.userError "Routed block result differs from production elementary row")
                      checked := checked+1
            unless seen.all (·=1) do throw (IO.userError "Some original occurrence was not routed exactly once")
            IO.println s!"PASS: P={P}, suffix={ell}, cap={r}, blocks={B}, coefficients={C}, requests={requests.size}, seed={seed}; {checked} full outputs."
            return checked
  throw (IO.userError "Invalid rectangular fixture shape")

def main : IO Unit := do
  let mut checked := 0
  for seed in ([-7,65537] : List Int) do
    checked := checked+(← check 0 0 0 2 3 1 1 seed false)
    checked := checked+(← check 1 2 1 3 2 2 3 seed false)
    checked := checked+(← check 2 1 1 2 1 2 2 seed false)
    checked := checked+(← check 1 1 0 1 0 1 1 seed false)
    checked := checked+(← check 1 1 2 0 3 2 2 seed false)
    checked := checked+(← check 1 1 1 2 2 2 2 seed true)
  IO.println s!"PASS: {checked} routed prefix/block outputs against independent raw tensors and the production row; original IDs, duplicate requests, empty cases and scalar budgets."
  IO.println "SCOPE: retained compatible prefix batches and routing; global window scheduling, rounded batch fit, address integration and full APSP cost remain."
