import SharedGroupedCompletion
open ThinMatrix RecursiveTable
open scoped BigOperators

-- A small rational base with the same fixed-coefficient interface. The actual
-- positive CW scale is symbolic and far too large for these finite fixtures.
private def smallBase : RetainedEqualCopy.Base 9 1 (prod (fin 2) (fin 2))
    (prod (fin 2) (fin 2)) (prod (fin 2) (fin 2)) ℚ :=
  ⟨store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val/4 && p.2.2.2.val == (p.1.val/2)%2 then 1/2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == (p.1.val/2)%2 && p.2.2.2.val == p.1.val%2 then -2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val%2 && p.2.2.2.val == p.1.val/4 then -1 else 0)⟩

private def scheme : RectangularBatch.Scheme :=
  ⟨2,2,2,1,1,1,9,1,by decide,by decide,by decide,by decide,rfl,rfl,smallBase⟩

private def check (N D C A P : Nat) (seed : Int) : IO Nat := do
  if hD : 0 < D then
    if hA : 0 < A then
      if hP : 0 < P then
        if hf : (A-1)^scheme.den ≤ D^scheme.num then
          if hl : P ≤ D^scheme.z then
            let M : Array (Vector Bool D) := Array.ofFn (fun i : Fin N =>
              Vector.ofFn (fun j => ((i.val%3)+j.val)%3 != 1))
            let X : Vector (Vector BinaryCell.Cell C) D := Vector.ofFn (fun i => Vector.ofFn (fun j =>
              (BinaryMultiplierAdapter.encodeInteger (seed+2*(i.val: Int)-3*(j.val: Int))).value))
            let out := SharedGroupedCompletion.complete scheme hD hA hP hf hl M X
            let H := X.toList.foldl (fun m row => row.toList.foldl (fun m z => max m (BinaryCell.view z).natAbs) m) 1
            let budget := CompactBlocks.blockCount N A*CompactBlocks.blockCount C P*RectangularBatch.scalarBudget scheme D H
            unless out.bitSteps ≤ budget do throw (IO.userError "Shared batch exceeds scalar budget")
            unless out.value.size == N do throw (IO.userError "Shared batch changed request count")
            for i in List.finRange N do
              for j in List.finRange C do
                let expected := ∑ k : Fin D, if (M[i.val]!).get k then BinaryCell.view ((X.get k).get j) else 0
                unless BinaryCell.view (((out.value[i.val]?).getD (Vector.replicate C BinaryCell.zero)).get j) == expected do
                  throw (IO.userError "Shared chunk result differs from dense selector sum")
            let left := SharedGroupedCompletion.selectors M
            let right := SharedGroupedCompletion.data X
            let product := RectangularBatch.run scheme hD hA hP hf hl left.value right.value
            let expectedControl := product.control+40*(N*D+D*C+N*C)+32*N+40
            unless out.control == expectedControl do throw (IO.userError "Shared adapter control mismatch")
            IO.println s!"PASS: {N} requests, {D} terms, {C} columns, chunks {A}x{P}, seed {seed}; {N*C} outputs."
            return N*C
  throw (IO.userError "Invalid fixture dimensions")

private def checkPrepared : IO Nat := do
  let X : BinaryGroupedPreparation.Source 2 6 := Vector.ofFn (fun c => Vector.ofFn (fun w =>
    if (w.val+c.val)%3=0 then (65537:Int) else if (w.val+c.val)%3=1 then -65537 else 0))
  let prepared := BinaryGroupedPreparation.prepare 1 X
  let mut checked := 0
  for p in List.finRange 4 do
    let full := (GroupedPreparation.keyVector 2 2).toArray
    let requests := if p.val=0 then #[] else full.push (Vector.replicate 2 false)
    let out := SharedGroupedCompletion.runGroup scheme (by decide) (A:=2) (P:=2)
      (by decide) (by decide) (by decide) (by decide) prepared.value p requests
    unless out.value.size == requests.size do throw (IO.userError "Prepared completion lost request indices")
    for i in List.finRange requests.size do
      for c in List.finRange 6 do
        let expected := (List.ofFn (fun w : Fin 9 =>
          let word := (StoredGroupedCompletion.rawIndex 2).symm w
          CroppedGroupedSuffix.kernel ((prepared.value.pairs.get p).get)
            (CappedBitPreparation.support requests[i.val]) word *
          CroppedGroupedSuffix.crop 1 (StoredGroupedCompletion.readSource X c) word)).sum
        let cell := ((out.value[i.val]?).getD (Vector.replicate 6 BinaryCell.zero)).get c
        unless BinaryCell.view cell == expected do throw (IO.userError "Prepared fast completion differs from raw tensor oracle")
        checked := checked+1
    let budget := CompactBlocks.blockCount requests.size 2*CompactBlocks.blockCount 6 2*
      RectangularBatch.scalarBudget scheme (CappedSubsetList.count 2 1) 65537
    unless out.bitSteps ≤ budget do throw (IO.userError "Prepared completion exceeds scalar bound")
  IO.println s!"PASS: {checked} prepared-group outputs against independent raw-tensor sums, including empty and duplicate requests."
  return checked

def main : IO Unit := do
  let mut checked := 0
  for dims in ([(0,1,3,1,1),(3,1,0,2,1),(1,1,1,2,1),(5,1,3,2,1),
    (3,2,5,3,2),(5,2,6,2,1),(5,3,7,2,3),(2,3,1,4,2)] : List (Nat×Nat×Nat×Nat×Nat)) do
    for seed in ([-7,65537] : List Int) do
      checked := checked + (← check dims.1 dims.2.1 dims.2.2.1 dims.2.2.2.1 dims.2.2.2.2 seed)
  let preparedCount ← checkPrepared
  IO.println s!"PASS: {checked} shared rectangular outputs and {preparedCount} prepared-group outputs; duplicate request rows, empty rows/columns, partial chunks and full scalar budgets."
  IO.println "SCOPE: matrix-level shared completion; production graph routing, global address pricing, rounded fit and full APSP proof remain."
