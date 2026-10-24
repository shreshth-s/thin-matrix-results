import BinaryAddressedPrice
import SharedAddressedStorage
open ThinMatrix RecursiveTable
open scoped BigOperators

private def smallBase : RetainedEqualCopy.Base 9 1 (prod (fin 2) (fin 2))
    (prod (fin 2) (fin 2)) (prod (fin 2) (fin 2)) ℚ :=
  ⟨store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val/4 && p.2.2.2.val == (p.1.val/2)%2 then 1/2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == (p.1.val/2)%2 && p.2.2.2.val == p.1.val%2 then -2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val%2 && p.2.2.2.val == p.1.val/4 then -1 else 0)⟩

private def check (n m p k : Nat) (seed : Int) : IO Nat := do
  if hn : n≤2^k then
    if hm : m≤2^k then
      if hp : p≤2^k then
        let x := store (PaddedMatrix.matrix n m) (fun i =>
          (BinaryMultiplierAdapter.encodeInteger (seed+2*(i.1.val:Int)-3*(i.2.val:Int))).value)
        let y := store (PaddedMatrix.matrix m p) (fun i =>
          (BinaryMultiplierAdapter.encodeInteger (seed-5*(i.1.val:Int)+7*(i.2.val:Int))).value)
        let out := BinaryAddressedMatrix.execute (by decide) (by decide) (by decide) (by decide) smallBase k hn hp x y
        let old := PaddedMatrix.execute (fin 2) (fin 2) (fin 2) (by decide) smallBase k hn hp x y
        unless out.value.toList.map BinaryCell.view == old.value.toList.map BinaryCell.view do
          throw (IO.userError "Addressed matrix differs from legacy output")
        let H := max 1 (max (x.toList.map (fun z => (BinaryCell.view z).natAbs)).sum
          (y.toList.map (fun z => (BinaryCell.view z).natAbs)).sum)
        let budget := BinaryAddressedMatrix.constant smallBase*(k+H.size+2)^5*9^k
        unless out.bitSteps≤budget do throw (IO.userError "Addressed matrix exceeds full uniform bound")
        let controlBudget := BinaryAddressedControl.constant smallBase*(k+2)^2*9^k
        unless out.control≤controlBudget do throw (IO.userError "Addressed matrix exceeds uniform control bound")
        let workBudget := BinaryAddressedControl.workConstant smallBase*(k+H.size+2)^5*9^k
        unless out.bitSteps+out.control≤workBudget do throw (IO.userError "Addressed matrix exceeds complete work bound")
        let localPrice := BinaryAddressedPrice.price smallBase 9 n m p k H
        let priceBudget := BinaryAddressedPrice.priceConstant smallBase 9*(k+H.size+2)^2
        unless localPrice≤priceBudget do throw (IO.userError "Derived control price exceeds quadratic bound")
        let pricedBudget := (BinaryAddressedPrice.priceConstant smallBase 9+1)*BinaryAddressedControl.workConstant smallBase*(k+H.size+2)^7*9^k
        unless out.bitSteps+localPrice*out.control≤pricedBudget do throw (IO.userError "Derived addressed work bound failed")
        let cells := BinaryAddressedStorage.matrixCells 9 1 2 2 2 n m p k
        let fields := BinaryAddressedPrice.fieldWidth smallBase 9 k H
        let maxAddress := BinaryAddressedStorage.bitCells cells fields-1
        unless maxAddress.size≤BinaryAddressedPrice.addressWidth smallBase 9 n m p k H do
          throw (IO.userError "Retained tree address width failed")
        let wholeBatch := BinaryAddressedStorage.batchCells n m p 1 1 cells
        let W := max n.size (max m.size p.size)+1
        unless wholeBatch≤2^(4*W+cells.size+4) do throw (IO.userError "Whole batch storage bound failed")
        let globalAddress := BinaryAddressedStorage.bitCells wholeBatch fields-1
        unless globalAddress.size≤4*W+cells.size+fields.size+12 do throw (IO.userError "Whole batch address bound failed")
        for i in List.finRange n do
          for j in List.finRange p do
            let expected := ∑ q : Fin m, BinaryCell.view (read x (i,q))*BinaryCell.view (read y (q,j))
            unless BinaryCell.view (read out.value (i,j)) == expected do
              throw (IO.userError "Addressed matrix differs from independent dense sum")
        IO.println s!"PASS: {n}x{m}x{p}, depth{k}, seed{seed}: {n*p} outputs; full binary pad, recursion, rational recovery, crop and uniform bit/control/priced-work, full-tree storage and whole-batch address bounds."
        return n*p
  throw (IO.userError "Invalid shape")

def main : IO Unit := do
  let mut total := 0
  for dims in ([(0,1,1,0),(1,0,1,0),(1,1,0,0),(1,1,1,0),(2,1,2,1),
      (1,2,1,1),(2,2,2,1),(3,2,4,2),(4,3,2,2)] : List (Nat×Nat×Nat×Nat)) do
    for seed in ([-7,65537] : List Int) do
      total := total+(←check dims.1 dims.2.1 dims.2.2.1 dims.2.2.2 seed)
  IO.println s!"PASS: {total} complete binary-addressed ordinary matrix outputs; signed inputs, rational base, padded and empty axes, actual bit plus derived indexed-control price and whole-batch address bounds."
