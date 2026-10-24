import SharedPrefixScatter
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
            let scheduled := SharedPrefixSchedule.execute scheme hD hA hZ hf hl requests prepared.value
            let entries := RoutedPrefixScatter.collect scheduled.value
            let full := SharedPrefixScatter.execute scheme hD hA hZ hf hl requests prepared.value
            unless entries.value.length=requests.size do throw (IO.userError "Schedule output count changed")
            unless full.bitSteps=scheduled.bitSteps do throw (IO.userError "Scatter changed scalar count")
            unless full.control=scheduled.control+128*requests.size+32*(2^ell)*(4^P+1)+32*(B*C)+52 do
              throw (IO.userError "Scatter control counter differs")
            let H := 2^P*(seed.natAbs+B*5+C*3+1)
            if Z≤B*C then
              let shape := SharedMatrixSetup.prepare scheme hD hf hl
              let W := (SharedAddressedBatch.addressSpan requests.size D (B*C) A Z).size
              let volumeBudget := (shape.bitSteps+SharedPrefixSchedule.addressBudget requests.size D (B*C) A P ell W)*A*Z+
                2*(requests.size+(2^ell*4^P)*A)*(B*C)*BinaryRecursiveCost.bits scheme.base shape.value.depth H
              unless scheduled.bitSteps*A*Z≤volumeBudget do
                throw (IO.userError "Aggregate scalar/address/setup volume bound failed")
            let mut checked := 0
            for original in List.finRange requests.size do
              for b in List.finRange B do
                for c in List.finRange C do
                  let actual := (full.value.get original).get (PrefixBlockBatch.column b c)
                  unless BinaryCell.view actual=reference P ell r seed b.val c.val requests[original.val] do
                    throw (IO.userError "Full scattered result differs from independent raw tensor")
                  let old := PrefixCompletionProgram.row (xs.get b) (prepared.value.banks.get b) requests[original.val]
                  unless BinaryCell.view actual=BinaryCell.view (old.value.output.get c) do
                    throw (IO.userError "Full scattered result differs from production row")
                  checked := checked+1
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
  IO.println s!"PASS: {checked} full scheduled/scattered prefix/block outputs against independent raw tensors and the production row; original IDs, duplicate requests, empty cases, aggregate padded scalar/address volume, one-time setup and scatter counters."
  IO.println "SCOPE: addressed prefix-batch schedule and shared setup with original-index scatter; recursive internal addresses, global graph/window integration and full APSP counter domination remain."
