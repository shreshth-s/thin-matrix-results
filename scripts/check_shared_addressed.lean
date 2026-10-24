import SharedAddressedBatch
open ThinMatrix RecursiveTable
open scoped BigOperators

private def smallBase : RetainedEqualCopy.Base 9 1 (prod (fin 2) (fin 2))
    (prod (fin 2) (fin 2)) (prod (fin 2) (fin 2)) ℚ :=
  ⟨store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val/4 && p.2.2.2.val == (p.1.val/2)%2 then 1/2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == (p.1.val/2)%2 && p.2.2.2.val == p.1.val%2 then -2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val%2 && p.2.2.2.val == p.1.val/4 then -1 else 0)⟩

private def scheme : RectangularBatch.Scheme :=
  ⟨2,2,2,1,1,1,9,1,by decide,by decide,by decide,by decide,rfl,rfl,smallBase⟩

private def check (N D P A C : Nat) (seed : Int) : IO Nat := do
  if hD : 0 < D then
    if hA : 0 < A then
      if hC : 0 < C then
        if hf : (A-1)^scheme.den ≤ D^scheme.num then
          if hl : C ≤ D^scheme.z then
            let x := store (PaddedMatrix.matrix N D) (fun i =>
              (BinaryMultiplierAdapter.encodeInteger (seed+2*(i.1.val:Int)-3*(i.2.val:Int))).value)
            let y := store (PaddedMatrix.matrix D P) (fun i =>
              (BinaryMultiplierAdapter.encodeInteger (seed-5*(i.1.val:Int)+7*(i.2.val:Int))).value)
            let shape := SharedMatrixSetup.prepare scheme hD hf hl
            let out := SharedAddressedBatch.run scheme shape.value hA hC x y
            let old := RectangularBatch.run scheme hD hA hC hf hl x y
            let shared := SharedMatrixSetup.run scheme shape.value hA hC x y
            unless out.value.toList.map BinaryCell.view == old.value.toList.map BinaryCell.view &&
                out.value.toList.map BinaryCell.view == shared.value.toList.map BinaryCell.view do
              throw (IO.userError "Addressed/shared batch changed output cells")
            let H := max 1 (max (x.toList.map (fun z => (BinaryCell.view z).natAbs)).sum
              (y.toList.map (fun z => (BinaryCell.view z).natAbs)).sum)
            let W := (SharedAddressedBatch.addressSpan N D P A C).size
            let budget := CompactBlocks.blockCount N A*CompactBlocks.blockCount P C*
              BinaryRecursiveCost.bits scheme.base shape.value.depth H+
              SharedAddressedBatch.addressBudget N D P A C W
            unless out.bitSteps ≤ budget do throw (IO.userError "Addressed batch exceeds binary budget")
            unless shape.bitSteps ≤ 1400*(D.size+3)*(scheme.q.size+D.size+6)^2+4 do
              throw (IO.userError "Shared setup exceeds binary budget")
            for i in List.finRange N do
              for j in List.finRange P do
                let expected := ∑ k : Fin D, BinaryCell.view (read x (i,k))*BinaryCell.view (read y (k,j))
                unless BinaryCell.view (read out.value (i,j)) == expected do
                  throw (IO.userError "Addressed batch differs from independent matrix sum")
            IO.println s!"PASS: {N}x{D}x{P}, chunks {A}x{C}, seed {seed}; {N*P} outputs and complete address/setup budgets."
            return N*P
  throw (IO.userError "Invalid fixture dimensions")

def main : IO Unit := do
  let mut total := 0
  for dims in ([(0,1,3,1,1),(3,1,0,2,1),(1,1,1,2,1),(5,1,3,2,1),
    (3,2,5,3,2),(5,2,6,2,1),(5,3,7,2,3),(2,3,1,4,2)] : List (Nat×Nat×Nat×Nat×Nat)) do
    for seed in ([-7,65537] : List Int) do
      total := total+(←check dims.1 dims.2.1 dims.2.2.1 dims.2.2.2.1 dims.2.2.2.2 seed)
  IO.println s!"PASS: {total} binary-addressed batch outputs; padded chunks, signed cells, empty axes, exact legacy agreement and independent dense sums."
  IO.println "SCOPE: binary outer chunk addresses and shared shape setup; recursive internal address lowering and whole APSP costs remain."
